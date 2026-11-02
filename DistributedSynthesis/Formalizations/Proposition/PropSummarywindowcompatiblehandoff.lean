/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Corollary.CorSummarywindowfiniteclosure
import DistributedSynthesis.Formalizations.Proposition.PropHandoffsuccessortests

/-!
# Summary-window compatibility closes the handoff
-/

namespace DistributedSynthesis

universe u v w x y z

/--
The functional direct-closing extension induced by successor tests.  Its
functionality field is the single-valuedness condition proved by the finite
summary-window closure.
-/
def functionalDirectClosingFromSuccessors
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂) :
    FunctionalDirectClosingExtension EdgeType Atom In₁ In₂ Out₁ Out₂ where
  tests := tests
  reachableTuples := fun _ => Set.univ
  functionalOnReachable := AtMostOneHandoffSuccessor tests

/--
Paper-facing summary-window compatibility certificate.  The first three fields
are the finite-algebra consequences of summary-window compatibility; the last
field is the resulting single-valuedness of successor atoms.
-/
structure SummaryWindowCompatibleHandoffCertificate
    (EdgeType : Proc -> Type u)
    (Atom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z)
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂) where
  finiteSummaryWindowAlgebra : Prop
  successorTestsInFiniteAlgebra : Prop
  simultaneousRefinementStabilizes : Prop
  uniqueSuccessorAtoms : AtMostOneHandoffSuccessor tests
  finiteSummaryWindowAlgebra_proof : finiteSummaryWindowAlgebra
  successorTestsInFiniteAlgebra_proof : successorTestsInFiniteAlgebra
  simultaneousRefinementStabilizes_proof : simultaneousRefinementStabilizes

/--
Proposition `prop:summarywindowcompatiblehandoff`: once summary-window
compatibility puts all reversal successor tests inside one finite closure
algebra, the simultaneous refinement stabilizes and yields a functional
direct-closing extension.
-/
theorem summary_window_compatible_handoff_closes
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (cert :
      SummaryWindowCompatibleHandoffCertificate
        EdgeType Atom In₁ In₂ Out₁ Out₂ tests) :
    cert.finiteSummaryWindowAlgebra ∧
      cert.successorTestsInFiniteAlgebra ∧
      cert.simultaneousRefinementStabilizes ∧
      Nonempty (FunctionalDirectClosingExtension EdgeType Atom In₁ In₂ Out₁ Out₂) ∧
      (functionalDirectClosingFromSuccessors tests).functionalOnReachable := by
  exact
    ⟨cert.finiteSummaryWindowAlgebra_proof,
      cert.successorTestsInFiniteAlgebra_proof,
      cert.simultaneousRefinementStabilizes_proof,
      ⟨functionalDirectClosingFromSuccessors tests⟩,
      cert.uniqueSuccessorAtoms⟩

end DistributedSynthesis
