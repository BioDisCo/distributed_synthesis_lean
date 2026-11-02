/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.BinaryAgreement

/-! Public execution/logic adapter tests, kept separate from the lightweight
view and block-logic clients. -/
open DistributedSynthesis FullViewPath PaddingProjection BinaryAgreement

example : Fintype.card Atom = 5 := by decide

-- The fault round itself is included, not just its strict future.
example (w : OmegaWord Letter) (he : LTL.Satisfies interp w permanentEquality)
    (t : Nat) (hm : ¬ LTL.Satisfies interp (w.drop t) marker)
    (hg : (w t).graph ≠ .both) : (w t).outputOne = (w t).outputTwo := by
  simpa using (permanentEquality_iff w).mp he t hm hg 0

example (K : Nat) (σ : StrategyPair Unit Unit Bool Bool) (hw : Winning K σ)
    (before after : List Graph) (g : Graph)
    (ha : BlockEmbedding.active (2*K+3) before.length = false) (hg : g ≠ .both) :
    σ.one (evaluate (before ++ [g] ++ after)).one =
      σ.two (evaluate (before ++ [g] ++ after)).two := by
  apply finite_history_agreement K σ hw
  exact (core_false_iff _ _).mpr ⟨before, g, after, rfl, ha, hg⟩

example (K : Nat) (σ : StrategyPair Unit Unit Bool Bool) (hw : Winning K σ)
    (t : Nat) {u v : Vertex} (hu : Reachable t u) (hv : Reachable t v)
    (hp : vertexProject (BlockEmbedding.active (2*K+3)) u =
      vertexProject (BlockEmbedding.active (2*K+3)) v) : label σ u = label σ v :=
  winning_fiber_agreement K σ hw t hu hv hp

#guard_msgs (drop info) in
#check winning_iff
#guard_msgs (drop info) in
#check serialized_bit_local
