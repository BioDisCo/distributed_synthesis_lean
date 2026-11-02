/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.BinaryStrategy

/-! # Literal LTL compilation to binary outputs

Source atoms test complete singleton-input round letters. Target atoms inspect
only a graph or one Boolean output. The formula compiler is structural and
uses explicit finite alphabet lists. This module separates semantic correctness
from the still separate encoded-computability certificate.
-/
namespace DistributedSynthesis.BinaryReduction
open FullViewPath PaddingProjection BlockEmbedding BinaryAgreement BinaryStrategy

abbrev SourceLetter (O₁ O₂ : Type*) := RoundRecord Unit Unit Graph O₁ O₂
def sourceInterp {O₁ O₂ : Type*} (a r : SourceLetter O₁ O₂) : Prop := r = a

def letterTest {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a : SourceLetter O₁ O₂) : LTL Atom :=
  .conj (.atom (.inl a.graph)) (.conj
    (BinaryWords.wordTest (.inr .two) (c₁.bits a.outputOne))
    (BinaryWords.wordTest (.inr .one) (c₂.bits a.outputTwo)))

def translate {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (φ : LTL (SourceLetter O₁ O₂)) : LTL Atom :=
  LTL.BlockTranslation.translate (2*K+3) marker (letterTest c₁ c₂) φ

def compile {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (φ : LTL (SourceLetter O₁ O₂)) : LTL Atom :=
  .conj (protocol K) (.conj (validOnCore c₁ c₂ a₁ a₂)
    (.disj (.neg coreCondition) (translate c₁ c₂ φ)))

def SourceWinning {O₁ O₂ : Type*} (φ : LTL (SourceLetter O₁ O₂))
    (σ : StrategyPair Unit Unit O₁ O₂) : Prop :=
  ∀ env, LTL.Satisfies sourceInterp (execution σ env) φ

def TargetWinning {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (φ : LTL (SourceLetter O₁ O₂)) (τ : StrategyPair Unit Unit Bool Bool) : Prop :=
  ∀ env, LTL.Satisfies interp (execution τ env) (compile c₁ c₂ a₁ a₂ φ)

/-- A target word represents all graph and output fields of a source word. -/
structure Represents {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (s : OmegaWord (SourceLetter O₁ O₂))
    (w : OmegaWord Letter) : Prop where
  graph : ∀ n, (w ((2*K+3)*n)).graph = (s n).graph
  one : ∀ n (j : Fin K), (w ((2*K+3)*n+(2*j.val+3))).outputTwo = c₁.bits (s n).outputOne j
  two : ∀ n (j : Fin K), (w ((2*K+3)*n+(2*j.val+3))).outputOne = c₂.bits (s n).outputTwo j

theorem interp_output (p : Proc) (r : Letter) : interp (.inr p) r ↔ read r p = true := by
  cases p <;> rfl

theorem codeTest_iff {O : Type*} {K : Nat} (c : BinaryWords.Code O K)
    (w : OmegaWord Letter) (p : Proc) (t : Nat) (value a : O)
    (hb : ∀ j : Fin K, read (w (t+(2*j.val+3))) p = c.bits value j) :
    LTL.Satisfies interp (w.drop t) (BinaryWords.wordTest (.inr p) (c.bits a)) ↔ value = a := by
  rw [BinaryWords.wordTest_iff]
  simp only [interp_output, hb]
  constructor
  · intro h
    apply c.injective
    funext j
    have hj := h j
    cases ha : c.bits value j <;> cases hb : c.bits a j <;> simp_all
  · rintro rfl
    simp

theorem letter_eq_iff {O₁ O₂ : Type*} (r a : SourceLetter O₁ O₂) :
    r = a ↔ r.graph = a.graph ∧ r.outputOne = a.outputOne ∧ r.outputTwo = a.outputTwo := by
  obtain ⟨⟨⟩,⟨⟩,g,o,p⟩ := r
  obtain ⟨⟨⟩,⟨⟩,g',o',p'⟩ := a
  simp

theorem letterTest_correct {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (s : OmegaWord (SourceLetter O₁ O₂))
    (w : OmegaWord Letter) (hr : Represents c₁ c₂ s w) (a : SourceLetter O₁ O₂) (n : Nat) :
    LTL.Satisfies interp (w.drop ((2*K+3)*n)) (letterTest c₁ c₂ a) ↔ sourceInterp a (s n) := by
  change ((w ((2*K+3)*n)).graph = a.graph ∧
    LTL.Satisfies interp (w.drop ((2*K+3)*n)) (BinaryWords.wordTest (.inr .two) (c₁.bits a.outputOne)) ∧
    LTL.Satisfies interp (w.drop ((2*K+3)*n)) (BinaryWords.wordTest (.inr .one) (c₂.bits a.outputTwo))) ↔ _
  rw [hr.graph, codeTest_iff c₁ w .two _ (s n).outputOne a.outputOne (hr.one n),
    codeTest_iff c₂ w .one _ (s n).outputTwo a.outputTwo (hr.two n)]
  exact (letter_eq_iff (s n) a).symm

theorem translate_correct {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (s : OmegaWord (SourceLetter O₁ O₂)) (w : OmegaWord Letter)
    (hr : Represents c₁ c₂ s w)
    (hf : LTL.Satisfies interp w (LTL.BinaryClock.frame (.inr .one) (.inr .two) K))
    (φ : LTL (SourceLetter O₁ O₂)) (n : Nat) :
    LTL.Satisfies interp (w.drop ((2*K+3)*n)) (translate c₁ c₂ φ) ↔
      LTL.Satisfies sourceInterp (s.drop n) φ :=
  LTL.BlockTranslation.correct (2*K+3) (by omega) marker (letterTest c₁ c₂)
    sourceInterp interp s w (LTL.BinaryClock.clock_exact _ _ _ _ _ hf)
    (letterTest_correct c₁ c₂ s w hr) φ n

theorem encoded_represents {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (σ : StrategyPair Unit Unit O₁ O₂) (source : Nat → Graph) :
    Represents c₁ c₂ (execution σ (GraphExecutions.ofGraphs source))
      (execution (encode c₁ c₂ σ) (GraphExecutions.ofGraphs (stream (2*K+3) source))) := by
  constructor
  · intro n
    simp only [GraphExecutions.execution_graph, GraphExecutions.ofGraphs,
      stream_boundary (2*K+3) (by omega)]
  · intro n j
    have he := encode_stream_data c₁ c₂ σ source n j.val j.isLt .one
    have ho := (GraphExecutions.execution_outputs σ (GraphExecutions.ofGraphs source) n).1
    rw [ho]
    simpa [wordAt, endpoint, BinaryStrategy.read, j.isLt, GraphExecutions.ofGraphs] using he
  · intro n j
    have he := encode_stream_data c₁ c₂ σ source n j.val j.isLt .two
    have ho := (GraphExecutions.execution_outputs σ (GraphExecutions.ofGraphs source) n).2
    rw [ho]
    simpa [wordAt, endpoint, BinaryStrategy.read, j.isLt, GraphExecutions.ofGraphs] using he

/-- The core guard determines padding graphs once the frame is satisfied. -/
theorem core_environment (K : Nat) (τ : StrategyPair Unit Unit Bool Bool)
    (env : EnvironmentSequence Unit Unit)
    (hf : LTL.Satisfies interp (execution τ env) (LTL.BinaryClock.frame (.inr .one) (.inr .two) K))
    (hc : LTL.Satisfies interp (execution τ env) coreCondition) :
    ∀ t, t % (2*K+3) ≠ 0 → (env t).graph = .both := by
  intro t ht
  have h := (LTL.satisfies_always _ _ _).mp hc t
  rcases h with hm | hg
  · have := (marker_iff_active K _ hf t).mp hm
    simp [active, ht] at this
  · simpa only [LTL.Satisfies, interp, OmegaWord.drop_apply, Nat.add_zero,
      GraphExecutions.execution_graph] using hg

/-- Full forward correctness: a source winner yields a winner for the whole
compiled formula, including the translated original LTL objective. -/
theorem encode_wins {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (ha₁ : ∀ a, a ∈ a₁) (ha₂ : ∀ a, a ∈ a₂) (φ : LTL (SourceLetter O₁ O₂))
    (σ : StrategyPair Unit Unit O₁ O₂) (hw : SourceWinning φ σ) :
    TargetWinning c₁ c₂ a₁ a₂ φ (encode c₁ c₂ σ) := by
  classical
  intro env
  refine ⟨encode_winning c₁ c₂ σ env, encode_valid_on_core c₁ c₂ a₁ a₂ ha₁ ha₂ σ env, ?_⟩
  change ¬ LTL.Satisfies interp _ coreCondition ∨ LTL.Satisfies interp _ (translate c₁ c₂ φ)
  apply or_iff_not_imp_left.mpr
  intro hnn
  have hf := (encode_winning c₁ c₂ σ env).1
  have hs := core_environment K _ env hf (Classical.not_not.mp hnn)
  rw [environment_as_stream (2*K+3) env hs]
  have hr := encoded_represents c₁ c₂ σ (fun n ↦ (env ((2*K+3)*n)).graph)
  have hf' := (encode_winning c₁ c₂ σ (GraphExecutions.ofGraphs (stream (2*K+3)
    (fun n ↦ (env ((2*K+3)*n)).graph)))).1
  simpa using (translate_correct c₁ c₂ _ _ hr hf' φ 0).mpr (by simpa using hw _)

/-- Pick a label on a physical projection fiber. Agreement makes the choice
irrelevant for every strategy satisfying the protocol. -/
noncomputable def fiberBit (K : Nat) (τ : StrategyPair Unit Unit Bool Bool)
    (t k : Nat) : Bool := by
  classical
  exact if h : ∃ v, Reachable t v ∧ vertexProject (active (2*K+3)) v = k
  then label τ h.choose else false

theorem fiberBit_at (K : Nat) (τ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K τ) (t : Nat) (v : Vertex) (hv : Reachable t v) :
    fiberBit K τ t (vertexProject (active (2*K+3)) v) = label τ v := by
  classical
  have he : ∃ u, Reachable t u ∧ vertexProject (active (2*K+3)) u =
      vertexProject (active (2*K+3)) v := ⟨v, hv, rfl⟩
  rw [fiberBit, dif_pos he]
  exact winning_fiber_agreement K τ hw t he.choose_spec.1 hv he.choose_spec.2

/-- Recovered bits depend only on the original tagged local view. -/
noncomputable def localWord (K : Nat) (τ : StrategyPair Unit Unit Bool Bool)
    (v : Vertex) (j : Fin K) : Bool :=
  fiberBit K τ ((2*K+3)*(vertexDepth v-1)+1+(2*j.val+3)) (coordinate v)

theorem endpoint_depth (h : List Graph) (p : Proc) :
    vertexDepth (endpoint h p) = h.length := by
  cases p
  · exact (at_depth h).1
  · exact (at_depth h).2

theorem execution_read (τ : StrategyPair Unit Unit Bool Bool)
    (source : Nat → Graph) (t : Nat) (p : Proc) :
    BinaryStrategy.read (execution τ (GraphExecutions.ofGraphs source) t) p =
      label τ (endpoint (graphPrefix source (t+1)) p) := by
  have ho := GraphExecutions.execution_outputs τ (GraphExecutions.ofGraphs source) t
  cases p
  · exact ho.1
  · exact ho.2

theorem localWord_stream (K : Nat) (τ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K τ) (source : Nat → Graph) (n : Nat) (p : Proc) (j : Fin K) :
    localWord K τ (endpoint (graphPrefix source (n+1)) p) j =
      BinaryStrategy.read (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source))
        ((2*K+3)*n+(2*j.val+3))) p.other := by
  have hp := (binary_stream_data_view_iff K source n j.val j.isLt p.other
    (endpoint (graphPrefix source (n+1)) p)).mpr (by simp)
  unfold localWord
  rw [endpoint_depth, prefix_length, Nat.add_sub_cancel, hp.2]
  have hu := endpoint_reachable
    (graphPrefix (stream (2*K+3) source) ((2*K+3)*n+1+(2*j.val+3))) p.other
  rw [prefix_length] at hu
  rw [fiberBit_at K τ hw _ _ hu]
  rw [execution_read]
  congr 3
  omega

/-- Only unreachable or invalid words use the default. Validity will exclude
that branch at every original view encountered in an execution. -/
noncomputable def decodeValue {O : Type*} [Nonempty O] {K : Nat}
    (c : BinaryWords.Code O K) (word : Fin K → Bool) : O := by
  classical
  exact if h : ∃ a, c.bits a = word then h.choose else Classical.choice inferInstance

theorem decodeValue_bits {O : Type*} [Nonempty O] {K : Nat}
    (c : BinaryWords.Code O K) (word : Fin K → Bool) (h : ∃ a, c.bits a = word) :
    c.bits (decodeValue c word) = word := by
  rw [decodeValue, dif_pos h]
  exact h.choose_spec

noncomputable def decode {O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂] {K : Nat}
    (c₁ : BinaryWords.Code O₁ K) (c₂ : BinaryWords.Code O₂ K)
    (τ : StrategyPair Unit Unit Bool Bool) : StrategyPair Unit Unit O₁ O₂ where
  one v := decodeValue c₁ (localWord K τ (.inl v))
  two v := decodeValue c₂ (localWord K τ (.inr v))

theorem decode_valid_word {O : Type*} [Nonempty O] {K : Nat}
    (c : BinaryWords.Code O K) (alphabet : List O) (w : OmegaWord Letter)
    (p : Proc) (t : Nat) (word : Fin K → Bool)
    (hb : ∀ j, word j = BinaryStrategy.read (w (t+(2*j.val+3))) p)
    (hv : LTL.Satisfies interp (w.drop t) (BinaryWords.valid (.inr p) c alphabet)) :
    c.bits (decodeValue c word) = word := by
  obtain ⟨a, _, ha⟩ := (BinaryWords.valid_iff interp w (.inr p) c alphabet t).mp hv
  apply decodeValue_bits
  refine ⟨a, funext fun j ↦ ?_⟩
  have hj := ha j
  rw [interp_output, ← hb j] at hj
  cases hc : c.bits a j <;> cases hw : word j <;> simp_all

theorem stream_core (K : Nat) (τ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K τ) (source : Nat → Graph) :
    LTL.Satisfies interp (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source)))
      coreCondition := by
  apply (LTL.satisfies_always _ _ _).mpr
  intro t
  by_cases ht : t % (2*K+3) = 0
  · left
    exact (marker_iff_active K _ (hw _).1 t).mpr (by simp [active, ht])
  · right
    change (execution τ _ t).graph = .both
    rw [GraphExecutions.execution_graph]
    simp [GraphExecutions.ofGraphs, stream, ht]

theorem target_protocol {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (φ : LTL (SourceLetter O₁ O₂)) (τ : StrategyPair Unit Unit Bool Bool)
    (hw : TargetWinning c₁ c₂ a₁ a₂ φ τ) : Winning K τ := fun env ↦ (hw env).1

theorem target_stream_valid {O₁ O₂ : Type*} {K : Nat} (c₁ : BinaryWords.Code O₁ K)
    (c₂ : BinaryWords.Code O₂ K) (a₁ : List O₁) (a₂ : List O₂)
    (φ : LTL (SourceLetter O₁ O₂)) (τ : StrategyPair Unit Unit Bool Bool)
    (hw : TargetWinning c₁ c₂ a₁ a₂ φ τ) (source : Nat → Graph) (n : Nat) :
    LTL.Satisfies interp
      (OmegaWord.drop (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source))) ((2*K+3)*n))
      (validCodes c₁ c₂ a₁ a₂) := by
  have hp := target_protocol c₁ c₂ a₁ a₂ φ τ hw
  have hc := stream_core K τ hp source
  have hv := (hw (GraphExecutions.ofGraphs (stream (2*K+3) source))).2.1
  rcases hv with hn | hv
  · exact (hn hc).elim
  · have hvn := (LTL.satisfies_always _ _ _).mp hv ((2*K+3)*n)
    rcases hvn with hn | hvn
    · exact (hn ((marker_iff_active K _ (hp _).1 _).mpr (by simp [active]))).elim
    · exact hvn

/-- A winner's data bits represent the execution of one original local
strategy, simultaneously on every embedded source environment. -/
theorem decoded_represents {O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂] {K : Nat}
    (c₁ : BinaryWords.Code O₁ K) (c₂ : BinaryWords.Code O₂ K)
    (a₁ : List O₁) (a₂ : List O₂) (φ : LTL (SourceLetter O₁ O₂))
    (τ : StrategyPair Unit Unit Bool Bool) (hw : TargetWinning c₁ c₂ a₁ a₂ φ τ)
    (source : Nat → Graph) :
    Represents c₁ c₂ (execution (decode c₁ c₂ τ) (GraphExecutions.ofGraphs source))
      (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source))) := by
  have hp := target_protocol c₁ c₂ a₁ a₂ φ τ hw
  constructor
  · intro n
    simp only [GraphExecutions.execution_graph, GraphExecutions.ofGraphs,
      stream_boundary (2*K+3) (by omega)]
  · intro n j
    have hv := (target_stream_valid c₁ c₂ a₁ a₂ φ τ hw source n).1
    have hb := decode_valid_word c₁ a₁ _ .two ((2*K+3)*n)
      (localWord K τ (endpoint (graphPrefix source (n+1)) .one))
      (localWord_stream K τ hp source n .one) hv
    rw [(GraphExecutions.execution_outputs (decode c₁ c₂ τ) (GraphExecutions.ofGraphs source) n).1]
    change BinaryStrategy.read (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source))
      ((2*K+3)*n+(2*j.val+3))) .two =
      c₁.bits (decodeValue c₁ (localWord K τ (endpoint (graphPrefix source (n+1)) .one))) j
    rw [hb]
    exact (localWord_stream K τ hp source n .one j).symm
  · intro n j
    have hv := (target_stream_valid c₁ c₂ a₁ a₂ φ τ hw source n).2
    have hb := decode_valid_word c₂ a₂ _ .one ((2*K+3)*n)
      (localWord K τ (endpoint (graphPrefix source (n+1)) .two))
      (localWord_stream K τ hp source n .two) hv
    rw [(GraphExecutions.execution_outputs (decode c₁ c₂ τ) (GraphExecutions.ofGraphs source) n).2]
    change BinaryStrategy.read (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source))
      ((2*K+3)*n+(2*j.val+3))) .one =
      c₂.bits (decodeValue c₂ (localWord K τ (endpoint (graphPrefix source (n+1)) .two))) j
    rw [hb]
    exact (localWord_stream K τ hp source n .two j).symm

theorem environment_as_graphs (env : EnvironmentSequence Unit Unit) :
    env = GraphExecutions.ofGraphs (fun t ↦ (env t).graph) := by
  funext t
  change env t = ⟨(), (), (env t).graph⟩
  obtain ⟨⟨⟩, ⟨⟩, g⟩ := env t
  rfl

/-- Reverse correctness without a view-coherence or decoding certificate. -/
theorem decode_wins {O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂] {K : Nat}
    (c₁ : BinaryWords.Code O₁ K) (c₂ : BinaryWords.Code O₂ K)
    (a₁ : List O₁) (a₂ : List O₂) (φ : LTL (SourceLetter O₁ O₂))
    (τ : StrategyPair Unit Unit Bool Bool) (hw : TargetWinning c₁ c₂ a₁ a₂ φ τ) :
    SourceWinning φ (decode c₁ c₂ τ) := by
  intro env
  let source := fun t ↦ (env t).graph
  have hp := target_protocol c₁ c₂ a₁ a₂ φ τ hw
  have ht := (hw (GraphExecutions.ofGraphs (stream (2*K+3) source))).2.2
  have hc := stream_core K τ hp source
  have ht' : LTL.Satisfies interp
      (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source))) (translate c₁ c₂ φ) :=
    ht.resolve_left (fun hn ↦ hn hc)
  have hr := decoded_represents c₁ c₂ a₁ a₂ φ τ hw source
  have hs := (translate_correct c₁ c₂ _ _ hr (hp _).1 φ 0).mp (by simpa using ht')
  rw [environment_as_graphs env]
  simpa only [OmegaWord.drop_zero] using hs

/-- Binary serialization preserves and reflects realizability in the same
full-view, perfect-recall network model. The alphabet lists must be exhaustive;
no restriction is imposed on the environment's graph sequences. -/
theorem realizable_iff {O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂] {K : Nat}
    (c₁ : BinaryWords.Code O₁ K) (c₂ : BinaryWords.Code O₂ K)
    (a₁ : List O₁) (a₂ : List O₂) (ha₁ : ∀ a, a ∈ a₁) (ha₂ : ∀ a, a ∈ a₂)
    (φ : LTL (SourceLetter O₁ O₂)) :
    (∃ σ, SourceWinning φ σ) ↔ ∃ τ, TargetWinning c₁ c₂ a₁ a₂ φ τ := by
  constructor
  · rintro ⟨σ, hw⟩
    exact ⟨encode c₁ c₂ σ, encode_wins c₁ c₂ a₁ a₂ ha₁ ha₂ φ σ hw⟩
  · rintro ⟨τ, hw⟩
    exact ⟨decode c₁ c₂ τ, decode_wins c₁ c₂ a₁ a₂ φ τ hw⟩

/-- Executable specialization to explicitly indexed finite alphabets. The
encoded computability theorem for this syntax transformation is separate. -/
def finCompile (m₁ m₂ : Nat) (φ : LTL (SourceLetter (Fin m₁) (Fin m₂))) : LTL Atom :=
  compile (BinaryWords.finCode m₁ (m₁+m₂+1) (by omega))
    (BinaryWords.finCode m₂ (m₁+m₂+1) (by omega)) (List.finRange m₁) (List.finRange m₂) φ

theorem fin_realizable_iff (m₁ m₂ : Nat) [NeZero m₁] [NeZero m₂]
    (φ : LTL (SourceLetter (Fin m₁) (Fin m₂))) :
    (∃ σ, SourceWinning φ σ) ↔
      ∃ τ : StrategyPair Unit Unit Bool Bool, ∀ env,
        LTL.Satisfies interp (execution τ env) (finCompile m₁ m₂ φ) := by
  exact realizable_iff (BinaryWords.finCode m₁ (m₁+m₂+1) (by omega))
    (BinaryWords.finCode m₂ (m₁+m₂+1) (by omega))
    (List.finRange m₁) (List.finRange m₂) (by simp) (by simp) φ

end DistributedSynthesis.BinaryReduction
