/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphExecutions
import DistributedSynthesis.Library.Logic.BinaryClock

/-! # From permanent-equality LTL to agreement on projection fibers

Atoms inspect only the current graph or one of the two Boolean outputs.
The clock is the existing `11` output marker, not a fresh proposition.
The winning premise below quantifies over all actual infinite environments;
one-way padding histories are not removed from that quantification.
-/

namespace DistributedSynthesis.BinaryAgreement
open FullViewPath PaddingProjection

abbrev Atom := Graph ⊕ Proc
abbrev Letter := RoundRecord Unit Unit Graph Bool Bool

def interp : Atom → Letter → Prop
  | .inl g, r => r.graph = g
  | .inr .one, r => r.outputOne = true
  | .inr .two, r => r.outputTwo = true

def marker : LTL Atom := LTL.BinaryClock.marker (.inr .one)

def agreement : LTL Atom :=
  .conj (.disj (.neg (.atom (.inr .one))) (.atom (.inr .two)))
    (.disj (.neg (.atom (.inr .two))) (.atom (.inr .one)))

/-- `G ((not marker and not both) -> G (out1 iff out2))`.
The inner `G` includes the current (fault) round. -/
def permanentEquality : LTL Atom :=
  .always (.disj marker (.disj (.atom (.inl .both)) (.always agreement)))

def protocol (K : Nat) : LTL Atom :=
  .conj (LTL.BinaryClock.frame (.inr .one) (.inr .two) K) permanentEquality

def Winning (K : Nat) (σ : StrategyPair Unit Unit Bool Bool) : Prop :=
  ∀ env, LTL.Satisfies interp (execution σ env) (protocol K)

def label (σ : StrategyPair Unit Unit Bool Bool) : Vertex → Bool := Sum.elim σ.one σ.two

theorem agreement_iff (w : OmegaWord Letter) (t : Nat) :
    LTL.Satisfies interp (w.drop t) agreement ↔ (w t).outputOne = (w t).outputTwo := by
  cases h₁ : (w t).outputOne <;> cases h₂ : (w t).outputTwo <;>
    simp [agreement, LTL.Satisfies, interp, OmegaWord.drop, h₁, h₂]

theorem permanentEquality_iff (w : OmegaWord Letter) :
    LTL.Satisfies interp w permanentEquality ↔
      ∀ t, ¬ LTL.Satisfies interp (w.drop t) marker → (w t).graph ≠ .both →
        ∀ d, (w (t+d)).outputOne = (w (t+d)).outputTwo := by
  classical
  simp only [permanentEquality, LTL.satisfies_always]
  change (∀ t, LTL.Satisfies interp (w.drop t) marker ∨
    (w t).graph = .both ∨ LTL.Satisfies interp (w.drop t) (.always agreement)) ↔ _
  simp only [or_iff_not_imp_left, LTL.satisfies_always, OmegaWord.drop_drop, agreement_iff]

/-- A satisfying frame gives the precise local-time schedule used by the
projection; no separate clock correctness assumption is needed. -/
theorem marker_iff_active (K : Nat) (w : OmegaWord Letter)
    (hf : LTL.Satisfies interp w (LTL.BinaryClock.frame (.inr .one) (.inr .two) K))
    (t : Nat) :
    LTL.Satisfies interp (w.drop t) marker ↔ BlockEmbedding.active (2*K+3) t = true := by
  rw [show marker = LTL.BinaryClock.marker (.inr .one) from rfl,
    LTL.BinaryClock.clock_exact interp w (.inr .one) (.inr .two) K hf t]
  change (∃ n, t = (2*K+3)*n) ↔ decide (t % (2*K+3) = 0) = true
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨n, rfl⟩
    simp
  · intro ht
    exact ⟨t / (2*K+3), by have := Nat.mod_add_div t (2*K+3); omega⟩

/-- The formula's consequence on an arbitrary actual execution, including
the round where the one-way padding graph first occurs. -/
theorem execution_agreement (K : Nat) (σ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K σ) (env : EnvironmentSequence Unit Unit) (t d : Nat)
    (ha : BlockEmbedding.active (2*K+3) t = false) (hg : (env t).graph ≠ .both) :
    (execution σ env (t+d)).outputOne = (execution σ env (t+d)).outputTwo := by
  have hp := hw env
  change LTL.Satisfies interp (execution σ env)
    (LTL.BinaryClock.frame (.inr .one) (.inr .two) K) ∧
      LTL.Satisfies interp (execution σ env) permanentEquality at hp
  apply (permanentEquality_iff _).mp hp.2 t ?_ ?_ d
  · intro hm
    have := (marker_iff_active K _ hp.1 t).mp hm
    simp [ha] at this
  · simpa only [GraphExecutions.execution_graph] using hg

/-- The previously explicit finite-history premise is now derived from a
winning literal LTL protocol. Every finite graph history is extended to an
actual infinite execution; no feasibility or view-coherence premise remains. -/
theorem finite_history_agreement (K : Nat) (σ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K σ) (h : List Graph)
    (hc : core (BlockEmbedding.active (2*K+3)) h = false) :
    σ.one (evaluate h).one = σ.two (evaluate h).two := by
  obtain ⟨before, g, after, rfl, ha, hg⟩ := (core_false_iff _ h).mp hc
  let h := before ++ [g] ++ after
  have hn : 0 < h.length := by simp [h]
  have he := execution_agreement K σ hw (GraphExecutions.extend h) before.length after.length
    ha (by simpa only [h, GraphExecutions.extend_fault] using hg)
  have ht : before.length+after.length = h.length-1 := by simp [h]
  rw [ht] at he
  have ho := GraphExecutions.extend_outputs σ h hn
  rw [ho.1, ho.2] at he
  exact he

/-- The composed information-preservation theorem for actual winning binary
strategies. It needs neither an echo certificate nor a separate clock premise. -/
theorem winning_fiber_agreement (K : Nat) (σ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K σ) (t : Nat) {u v : Vertex}
    (hu : Reachable t u) (hv : Reachable t v)
    (hp : vertexProject (BlockEmbedding.active (2*K+3)) u =
      vertexProject (BlockEmbedding.active (2*K+3)) v) : label σ u = label σ v :=
  fiber_agreement (BlockEmbedding.active (2*K+3)) t (label σ)
    (fun h _ hc ↦ finite_history_agreement K σ hw h hc) hu hv hp

theorem winning_factors_through_projection (K : Nat) (σ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K σ) (t : Nat) :
    ∃ decoded : Nat → Bool, ∀ v, Reachable t v →
      label σ v = decoded (vertexProject (BlockEmbedding.active (2*K+3)) v) :=
  factors_through_projection (BlockEmbedding.active (2*K+3)) t (label σ)
    (fun h _ hc ↦ finite_history_agreement K σ hw h hc)

/-- Under the frame formula, permanent equality on all executions is exactly
finite-history agreement. This direction is also available to constructions
of binary strategies; the LTL obligation need not be reproved from scratch. -/
theorem winning_iff (K : Nat) (σ : StrategyPair Unit Unit Bool Bool) :
    Winning K σ ↔
      (∀ env, LTL.Satisfies interp (execution σ env)
        (LTL.BinaryClock.frame (.inr .one) (.inr .two) K)) ∧
      (∀ h, core (BlockEmbedding.active (2*K+3)) h = false →
        σ.one (evaluate h).one = σ.two (evaluate h).two) := by
  constructor
  · intro hw
    exact ⟨fun env ↦ (hw env).1, finite_history_agreement K σ hw⟩
  · rintro ⟨hf, he⟩ env
    refine ⟨hf env, (permanentEquality_iff _).mpr ?_⟩
    intro t hm hg d
    have ha : BlockEmbedding.active (2*K+3) t = false := by
      cases h : BlockEmbedding.active (2*K+3) t with
      | false => rfl
      | true => exact (hm ((marker_iff_active K _ (hf env) t).mpr h)).elim
    let source := fun k ↦ (env k).graph
    have hbad : core (BlockEmbedding.active (2*K+3)) (BlockEmbedding.graphPrefix source (t+1)) = false := by
      rw [BlockEmbedding.prefix_succ, core_append, BlockEmbedding.prefix_length]
      have hg' : source t ≠ .both := by simpa only [source, GraphExecutions.execution_graph] using hg
      simp [ha, hg']
    have hc : core (BlockEmbedding.active (2*K+3)) (BlockEmbedding.graphPrefix source (t+d+1)) = false := by
      rw [show t+d+1 = (t+1)+d by omega, GraphExecutions.graphPrefix_add]
      exact fault_persists _ _ _ hbad
    have hlabels := he _ hc
    have ho := GraphExecutions.execution_outputs σ env (t+d)
    rw [ho.1, ho.2]
    exact hlabels

/-- A serialized bit is a function of the original process's local view.
The two histories may differ globally and reveal different information during
padding; only their original tagged endpoint is required to coincide. -/
theorem serialized_bit_local (K : Nat) (σ : StrategyPair Unit Unit Bool Bool)
    (hw : Winning K σ) (h h' : List Graph) (g g' : Graph)
    (ht : h.length = h'.length) (j : Nat) (hj : j < K) (p : Proc)
    (hv : BlockEmbedding.endpoint (h ++ [g]) p = BlockEmbedding.endpoint (h' ++ [g']) p) :
    label σ (BlockEmbedding.endpoint (BlockEmbedding.phase (2*K+3) h g (2*j+3)) p.other) =
      label σ (BlockEmbedding.endpoint (BlockEmbedding.phase (2*K+3) h' g' (2*j+3)) p.other) := by
  have hl : 0 < 2*K+3 := by omega
  have he : (2*K+3-1) % 2 = 0 := by omega
  have hd : 2*j+3 < 2*K+3 := by omega
  have hp : BlockEmbedding.ownerAt (2*j+3) p.other = p := by
    simp [BlockEmbedding.ownerAt, show (2*j+3) % 2 ≠ 0 by omega]
  have hu := BlockEmbedding.endpoint_reachable (BlockEmbedding.phase (2*K+3) h g (2*j+3)) p.other
  have hu' := BlockEmbedding.endpoint_reachable (BlockEmbedding.phase (2*K+3) h' g' (2*j+3)) p.other
  have hlen : (BlockEmbedding.phase (2*K+3) h g (2*j+3)).length =
      (BlockEmbedding.phase (2*K+3) h' g' (2*j+3)).length := by
    rw [BlockEmbedding.phase_length _ hl, BlockEmbedding.phase_length _ hl, ht]
  rw [← hlen] at hu'
  apply winning_fiber_agreement K σ hw _ hu hu'
  rw [BlockEmbedding.phase_coordinate _ hl he h g _ hd,
    BlockEmbedding.phase_coordinate _ hl he h' g' _ hd, hp, hv]

end DistributedSynthesis.BinaryAgreement
