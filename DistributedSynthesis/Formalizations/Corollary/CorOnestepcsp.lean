/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemTreecsp

/-!
# One-step automaton constraints over a fixed input cube
-/

namespace DistributedSynthesis

universe u v w

/--
Corollary `cor:onestepcsp`: once the fixed-input one-step requirements are
represented as finite process-owned edge constraints, locally uniform
satisfiability is decidable by the finite tree CSP.
-/
noncomputable def one_step_automaton_constraints_decidable
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype Out₁] [Fintype Out₂]
    (T : RootedConstraintTree.{u, v, w} Out₁ Out₂)
    [DecidableEq T.Vertex]
    [DecidableRel T.edge]
    [∀ a b h left right, Decidable (T.edgeRel a b h left right)] :
    Decidable (∃ label : T.Labeling, T.Satisfying label) :=
  RootedConstraintTree.finite_tree_csp_decidable T

end DistributedSynthesis
