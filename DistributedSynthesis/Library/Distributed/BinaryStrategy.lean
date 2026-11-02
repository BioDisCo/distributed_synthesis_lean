/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.BinaryAgreement
import DistributedSynthesis.Library.Logic.BinaryWords

/-! # Constructing local binary strategies

Payload tables depend on virtual depth, projected coordinate, and bit index.
The encoder itself reads only a single physical local view. The protocol
theorem holds for every payload table, on every actual environment.
-/
namespace DistributedSynthesis.BinaryStrategy
open FullViewPath PaddingProjection BlockEmbedding BinaryAgreement

abbrev Payload := Nat → Nat → Nat → Bool

def emit (K : Nat) (data : Nat → Bool) (t : Nat) : Bool :=
  let r := t % (2*K+3)
  if r < 2 then true else if r % 2 = 0 then false else data ((r-3)/2)

def localBit (K : Nat) (data : Payload) (v : Vertex) : Bool :=
  emit K (data (virtualDepth (active (2*K+3)) (vertexDepth v))
    (vertexProject (active (2*K+3)) v)) (vertexDepth v-1)

def strategy (K : Nat) (data : Payload) : StrategyPair Unit Unit Bool Bool where
  one v := localBit K data (.inl v)
  two v := localBit K data (.inr v)

def read (r : Letter) : Proc → Bool
  | .one => r.outputOne
  | .two => r.outputTwo

theorem emit_header (K : Nat) (data : Nat → Bool) (n r : Nat) (hr : r < 2) :
    emit K data ((2*K+3)*n+r) = true := by
  have hl : r < 2*K+3 := by omega
  simp [emit, Nat.add_mod, Nat.mod_eq_of_lt hl, hr]

theorem emit_separator (K : Nat) (data : Nat → Bool) (n j : Nat) (hj : j ≤ K) :
    emit K data ((2*K+3)*n+(2*j+2)) = false := by
  have hl : 2*j+2 < 2*K+3 := by omega
  simp [emit, Nat.add_mod, Nat.mod_eq_of_lt hl, show ¬ 2*j+2 < 2 by omega]

theorem emit_data (K : Nat) (data : Nat → Bool) (n j : Nat) (hj : j < K) :
    emit K data ((2*K+3)*n+(2*j+3)) = data j := by
  have hl : 2*j+3 < 2*K+3 := by omega
  simp [emit, Nat.add_mod, Nat.mod_eq_of_lt hl, show ¬ 2*j+3 < 2 by omega]

theorem localBit_endpoint (K : Nat) (data : Payload) (h : List Graph) (p : Proc) :
    localBit K data (endpoint h p) = emit K
      (data (virtualDepth (active (2*K+3)) h.length)
        (vertexProject (active (2*K+3)) (endpoint h p))) (h.length-1) := by
  have hd := at_depth h
  cases p <;> simp [localBit, endpoint, vertexDepth, hd.1, hd.2]

theorem execution_read (K : Nat) (data : Payload) (env : EnvironmentSequence Unit Unit)
    (t : Nat) (p : Proc) :
    read (execution (strategy K data) env t) p = emit K
      (data (virtualDepth (active (2*K+3)) (t+1))
        (vertexProject (active (2*K+3)) (endpoint (graphPrefix (fun k ↦ (env k).graph) (t+1)) p))) t := by
  have ho := GraphExecutions.execution_outputs (strategy K data) env t
  have he : read (execution (strategy K data) env t) p =
      localBit K data (endpoint (graphPrefix (fun k ↦ (env k).graph) (t+1)) p) := by
    cases p
    · exact ho.1
    · exact ho.2
  rw [he, localBit_endpoint, prefix_length, Nat.add_sub_cancel]

theorem strategy_frame (K : Nat) (data : Payload) (env : EnvironmentSequence Unit Unit) :
    LTL.Satisfies interp (execution (strategy K data) env)
      (LTL.BinaryClock.frame (.inr .one) (.inr .two) K) := by
  have hh : ∀ n r, r < 2 → ∀ p, read (execution (strategy K data) env ((2*K+3)*n+r)) p = true := by
    intro n r hr p
    rw [execution_read]
    exact emit_header K _ n r hr
  have hz : ∀ n j, j ≤ K → ∀ p, read (execution (strategy K data) env ((2*K+3)*n+(2*j+2))) p = false := by
    intro n j hj p
    rw [execution_read]
    exact emit_separator K _ n j hj
  apply LTL.BinaryClock.frame_of_pattern
  · intro n
    exact ⟨by simpa [interp, read, LTL.BinaryClock.length] using hh n 0 (by omega) .one,
      hh n 1 (by omega) .one,
      by simpa [interp, read, LTL.BinaryClock.length] using hh n 0 (by omega) .two,
      hh n 1 (by omega) .two⟩
  · intro n j hj
    change ¬ read _ .one = true ∧ ¬ read _ .two = true
    simp only [LTL.BinaryClock.length, hz n j hj, Bool.false_eq_true, not_false_eq_true, and_self]

theorem strategy_fault_agreement (K : Nat) (data : Payload) (h : List Graph)
    (hc : core (active (2*K+3)) h = false) :
    (strategy K data).one (evaluate h).one = (strategy K data).two (evaluate h).two := by
  have he := (collapsed_iff (active (2*K+3)) h).mpr hc
  have hp : vertexProject (active (2*K+3)) (endpoint h .one) =
      vertexProject (active (2*K+3)) (endpoint h .two) := by
    cases ht : (evaluate h).oneLeft <;> simp [left, right, ht] at he
    · exact he.symm
    · exact he
  change localBit K data (endpoint h .one) = localBit K data (endpoint h .two)
  rw [localBit_endpoint, localBit_endpoint, hp]

/-- The constructed local strategy satisfies the entire frame/equality
protocol on all graph sequences, for arbitrary payload data. -/
theorem strategy_winning (K : Nat) (data : Payload) : Winning K (strategy K data) :=
  (winning_iff K _).mpr ⟨strategy_frame K data, strategy_fault_agreement K data⟩

def wordAt {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂)
    (v : Vertex) (j : Nat) : Bool :=
  if hj : j < K then
    Sum.elim (fun v ↦ c₁.bits (σ.one v) ⟨j,hj⟩) (fun v ↦ c₂.bits (σ.two v) ⟨j,hj⟩) v
  else false

/-- Choice is used only to represent an arbitrary original strategy by its
coordinate table. It is not used in the finite formula compiler. -/
noncomputable def payload {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂) : Payload := by
  classical
  exact fun m k j ↦ if h : ∃ v, Reachable m v ∧ coordinate v = k then
    wordAt c₁ c₂ σ h.choose j else false

theorem payload_at_view {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂)
    {m : Nat} {v : Vertex} (hv : Reachable m v) (j : Nat) :
    payload c₁ c₂ σ m (coordinate v) j = wordAt c₁ c₂ σ v j := by
  classical
  have hex : ∃ u, Reachable m u ∧ coordinate u = coordinate v := ⟨v,hv,rfl⟩
  simp only [payload, dif_pos hex]
  rw [coordinate_injective hex.choose_spec.1 hv hex.choose_spec.2]

noncomputable def encode {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂) :
    StrategyPair Unit Unit Bool Bool := strategy K (payload c₁ c₂ σ)

theorem encode_winning {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂) : Winning K (encode c₁ c₂ σ) :=
  strategy_winning K _

/-- Every bit of the encoded history comes from the original local strategy,
with the physical owner exchange already accounted for. -/
theorem encode_history_data {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂)
    (h : List Graph) (g : Graph) (j : Nat) (hj : j < K) (p : Proc) :
    localBit K (payload c₁ c₂ σ) (endpoint (phase (2*K+3) h g (2*j+3)) p.other) =
      wordAt c₁ c₂ σ (endpoint (h ++ [g]) p) j := by
  have hl : 0 < 2*K+3 := by omega
  have hd : 2*j+3 < 2*K+3 := by omega
  have he : (2*K+3-1)%2 = 0 := by omega
  have hp : ownerAt (2*j+3) p.other = p := by
    simp [ownerAt, show (2*j+3)%2 ≠ 0 by omega]
  rw [localBit_endpoint, phase_virtualDepth _ hl h g _ hd,
    phase_coordinate _ hl he h g _ hd, hp, phase_length _ hl]
  rw [show (2*K+3)*h.length+1+(2*j+3)-1 = (2*K+3)*h.length+(2*j+3) by omega,
    emit_data K _ h.length j hj]
  exact payload_at_view c₁ c₂ σ (by simpa using endpoint_reachable (h ++ [g]) p) j

theorem encode_stream_data {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂)
    (source : Nat → Graph) (n j : Nat) (hj : j < K) (p : Proc) :
    read (execution (encode c₁ c₂ σ) (GraphExecutions.ofGraphs (stream (2*K+3) source))
      ((2*K+3)*n+(2*j+3))) p.other = wordAt c₁ c₂ σ (endpoint (graphPrefix source (n+1)) p) j := by
  have ho := GraphExecutions.execution_outputs (encode c₁ c₂ σ)
    (GraphExecutions.ofGraphs (stream (2*K+3) source)) ((2*K+3)*n+(2*j+3))
  have hx : read (execution (encode c₁ c₂ σ) (GraphExecutions.ofGraphs (stream (2*K+3) source))
      ((2*K+3)*n+(2*j+3))) p.other = localBit K (payload c₁ c₂ σ)
        (endpoint (graphPrefix (stream (2*K+3) source) ((2*K+3)*n+(2*j+3)+1)) p.other) := by
    cases p
    · exact ho.2
    · exact ho.1
  rw [hx, show (2*K+3)*n+(2*j+3)+1 = (2*K+3)*n+1+(2*j+3) by omega,
    stream_prefix_phase _ (by omega) source n _ (by omega), prefix_succ]
  exact encode_history_data c₁ c₂ σ _ _ j hj p

def validCodes {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂) : LTL Atom :=
  .conj (BinaryWords.valid (.inr .two) c₁ a₁) (BinaryWords.valid (.inr .one) c₂ a₂)

theorem encode_stream_valid {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (ha₁ : ∀ a, a ∈ a₁) (ha₂ : ∀ a, a ∈ a₂) (σ : StrategyPair Unit Unit O₁ O₂)
    (source : Nat → Graph) (n : Nat) :
    LTL.Satisfies interp (OmegaWord.drop (execution (encode c₁ c₂ σ)
      (GraphExecutions.ofGraphs (stream (2*K+3) source))) ((2*K+3)*n))
      (validCodes c₁ c₂ a₁ a₂) := by
  constructor
  · apply (BinaryWords.valid_iff _ _ _ _ _ _).mpr
    refine ⟨σ.one (evaluate (graphPrefix source (n+1))).one, ha₁ _, ?_⟩
    intro j
    have he := encode_stream_data c₁ c₂ σ source n j.val j.isLt .one
    simpa [wordAt, endpoint, read, interp, j.isLt] using congrArg (fun b ↦ b = true) he
  · apply (BinaryWords.valid_iff _ _ _ _ _ _).mpr
    refine ⟨σ.two (evaluate (graphPrefix source (n+1))).two, ha₂ _, ?_⟩
    intro j
    have he := encode_stream_data c₁ c₂ σ source n j.val j.isLt .two
    simpa [wordAt, endpoint, read, interp, j.isLt] using congrArg (fun b ↦ b = true) he

def coreCondition : LTL Atom := .always (.disj marker (.atom (.inl .both)))

def validOnCore {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂) : LTL Atom :=
  .disj (.neg coreCondition) (.always (.disj (.neg marker) (validCodes c₁ c₂ a₁ a₂)))

/-- Every environment with bidirectional padding is one embedded source
environment. This is a proof-side reconstruction, not information given to
the local strategies. -/
theorem environment_as_stream (L : Nat) (env : EnvironmentSequence Unit Unit)
    (hc : ∀ t, t % L ≠ 0 → (env t).graph = .both) :
    env = GraphExecutions.ofGraphs (stream L (fun n ↦ (env (L*n)).graph)) := by
  funext t
  have hg : (env t).graph = stream L (fun n ↦ (env (L*n)).graph) t := by
    unfold stream
    split_ifs with ht
    · have he : L*(t/L) = t := by have := Nat.mod_add_div t L; omega
      simpa only [he]
    · exact hc t ht
  calc
    env t = ⟨(),(),(env t).graph⟩ := by
      obtain ⟨⟨⟩,⟨⟩,g⟩ := env t
      rfl
    _ = _ := congrArg (fun g ↦ (⟨(),(),g⟩ : EnvironmentRound Unit Unit)) hg

/-- All code-validity obligations hold on every core execution of the
constructed strategy. Faulty executions still satisfy the protocol. -/
theorem encode_valid_on_core {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (ha₁ : ∀ a, a ∈ a₁) (ha₂ : ∀ a, a ∈ a₂) (σ : StrategyPair Unit Unit O₁ O₂)
    (env : EnvironmentSequence Unit Unit) :
    LTL.Satisfies interp (execution (encode c₁ c₂ σ) env) (validOnCore c₁ c₂ a₁ a₂) := by
  classical
  change ¬ LTL.Satisfies interp _ coreCondition ∨ LTL.Satisfies interp _ (.always _)
  apply or_iff_not_imp_left.mpr
  intro hnn
  have hc := Classical.not_not.mp hnn
  have hf := (encode_winning c₁ c₂ σ env).1
  have hs : ∀ t, t % (2*K+3) ≠ 0 → (env t).graph = .both := by
    intro t ht
    have ha : active (2*K+3) t = false := by simp [active, ht]
    have hm : ¬ LTL.Satisfies interp (OmegaWord.drop (execution (encode c₁ c₂ σ) env) t) marker := by
      intro hm
      have := (marker_iff_active K _ hf t).mp hm
      simp [ha] at this
    have hh := (LTL.satisfies_always _ _ _).mp hc t
    rcases hh with hh | hh
    · exact (hm hh).elim
    · simpa only [LTL.Satisfies, interp, OmegaWord.drop_apply, Nat.add_zero,
        GraphExecutions.execution_graph] using hh
  apply (LTL.satisfies_always _ _ _).mpr
  intro t
  change ¬ LTL.Satisfies interp _ marker ∨ LTL.Satisfies interp _ (validCodes c₁ c₂ a₁ a₂)
  apply or_iff_not_imp_left.mpr
  intro hnn
  have hm := Classical.not_not.mp hnn
  obtain ⟨n, rfl⟩ := (LTL.BinaryClock.clock_exact interp _ (.inr .one) (.inr .two) K hf t).mp hm
  rw [environment_as_stream (2*K+3) env hs]
  exact encode_stream_valid c₁ c₂ a₁ a₂ ha₁ ha₂ σ _ n

theorem encode_protocol_and_validity {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (ha₁ : ∀ a, a ∈ a₁) (ha₂ : ∀ a, a ∈ a₂) (σ : StrategyPair Unit Unit O₁ O₂) :
    ∀ env, LTL.Satisfies interp (execution (encode c₁ c₂ σ) env)
      (.conj (protocol K) (validOnCore c₁ c₂ a₁ a₂)) :=
  fun env ↦ ⟨encode_winning c₁ c₂ σ env, encode_valid_on_core c₁ c₂ a₁ a₂ ha₁ ha₂ σ env⟩

end DistributedSynthesis.BinaryStrategy
