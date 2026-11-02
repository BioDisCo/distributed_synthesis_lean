/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.InstanceEncoding
import DistributedSynthesis.Library.Distributed.GraphAdversaries.SingletonInputEncodingCorrect
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Decidability

/-! The complete graph-hole characterization of LTL synthesis, in both the
original singleton-input encoding and the library's finite-private-input
encoding. The negative direction is transferred by a proved computable
embedding; the positive direction uses the generated leader-game solver. -/
namespace Characterisation
open DistributedSynthesis

namespace WithInputs

/-- Failure of graph-only holes already makes the singleton-input subproblem
undecidable. No omega-regularity assumption is needed in this direction. -/
theorem no_geometric_holes_undecidable (A : Set (Nat → Graph))
    (noHoles : ¬ GeometricHoles A) : ¬ ComputablePred (Realizable A) := by
  intro decidable
  exact Characterisation.no_geometric_holes_undecidable A noHoles
    (SingletonInputEncoding.computable_preimage A decidable)

theorem decidable_implies_geometric_holes (A : Set (Nat → Graph))
    (decidable : ComputablePred (Realizable A)) : GeometricHoles A :=
  Characterisation.decidable_implies_geometric_holes A
    (SingletonInputEncoding.computable_preimage A decidable)

/-- For a fixed omega-regular adversary, finite-private-input LTL synthesis
is computable exactly when its graph-sequence image has open holes at every scale. -/
theorem realizable_computable_iff_geometric_holes
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ GeometricHoles A :=
  ⟨decidable_implies_geometric_holes A,holes_realizable_computable A regular⟩

/-- Equivalently, the closure of the graph-sequence image has empty interior
in the relative topology of the unit interval. -/
theorem realizable_computable_iff_interior_closure_empty
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ interior (closure (geometricMap '' A)) = ∅ :=
  (realizable_computable_iff_geometric_holes A regular).trans (geometricHoles_iff A)

/-- The original finite-private-input iff target, with no additional hypotheses. -/
theorem holesCharacterization : HolesCharacterization :=
  realizable_computable_iff_geometric_holes

end WithInputs

/-- The same iff also holds in the earlier singleton-input instance encoding. -/
theorem realizable_computable_iff_geometric_holes
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ GeometricHoles A :=
  ⟨decidable_implies_geometric_holes A,fun holes =>
    SingletonInputEncoding.computable_preimage A (WithInputs.holes_realizable_computable A regular holes)⟩

/-- The initial singleton-input iff target is proved as well. -/
theorem holesCharacterization : HolesCharacterization :=
  realizable_computable_iff_geometric_holes

end Characterisation
