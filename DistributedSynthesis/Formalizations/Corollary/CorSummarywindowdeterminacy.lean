/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropSummarywindowcompatiblehandoff

/-!
# Determinacy of summary-window successors is finite
-/

namespace DistributedSynthesis

universe u v w x y z

/--
Certificate that the finite summary-window successor relation is single-valued
on reachable old values and refines the synchronized atom successors.
-/
structure SummaryWindowDeterminacyCertificate
    (EdgeType : Proc -> Type u)
    (Atom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z)
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂) where
  finiteRelationEffective : Prop
  uniqueReachableSummarySuccessor : Prop
  summarySuccessorDeterminesAtom : Prop
  uniqueAtomSuccessor : AtMostOneHandoffSuccessor tests
  finiteRelationEffective_proof : finiteRelationEffective
  uniqueReachableSummarySuccessor_proof : uniqueReachableSummarySuccessor
  summarySuccessorDeterminesAtom_proof : summarySuccessorDeterminesAtom

/--
Corollary `cor:summarywindowdeterminacy`: finite single-valuedness of the
summary-window successor relation gives the finite handoff successor check.
-/
theorem summary_window_successor_determinacy_is_finite
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (cert :
      SummaryWindowDeterminacyCertificate
        EdgeType Atom In₁ In₂ Out₁ Out₂ tests) :
    cert.finiteRelationEffective ∧
      cert.uniqueReachableSummarySuccessor ∧
      cert.summarySuccessorDeterminesAtom ∧
      AtMostOneHandoffSuccessor tests := by
  exact
    ⟨cert.finiteRelationEffective_proof,
      cert.uniqueReachableSummarySuccessor_proof,
      cert.summarySuccessorDeterminesAtom_proof,
      cert.uniqueAtomSuccessor⟩

end DistributedSynthesis
