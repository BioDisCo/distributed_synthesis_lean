/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Results.HolesCharacterization
import DistributedSynthesis.Library.Distributed.GraphAdversaries.NoDirectReversal
import DistributedSynthesis.Library.Distributed.InputAlphabetRelabeling
import DistributedSynthesis.Tests.GraphAdversaries.HandoverProgressRegression
import DistributedSynthesis.Tests.GraphAdversaries.PhaseOfferRegression
import DistributedSynthesis.Tests.GraphAdversaries.WinningRestartObstruction

/-! Public clients check the exact iff, the existing input encoding, physical
round preservation, and the unchanged no-direct-reversal specialization. -/
namespace DistributedSynthesis.Tests.GraphAdversaries
open DistributedSynthesis.GraphAdversaries

example (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ GeometricHoles A :=
  realizable_computable_iff_geometric_holes A regular

example (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ solve : EncodedNoDirect.Instance → Bool,
      Primrec solve ∧ ∀ i, solve i = true ↔ Realizable A i :=
  holes_primitive_recursive_solver A regular holes

example (d : EncodedNoDirect.Instance) :
    Realizable Characterisation.WithInputs.NoDirectGraphs d ↔ EncodedNoDirect.Realizable d := Iff.rfl

example : ComputablePred (Realizable Characterisation.WithInputs.NoDirectGraphs) :=
  EncodedNoDirectComputable.realizable_computable

example (A : Set (Nat → Graph)) (d : Characterisation.SynthesisInstance) :
    Realizable A (Characterisation.SingletonInputEncoding.embed d) ↔
      SingletonInputs.Realizable A d := Characterisation.SingletonInputEncoding.realizable A d

example : Characterisation.HolesCharacterization := Characterisation.holesCharacterization
example : Characterisation.WithInputs.HolesCharacterization := Characterisation.WithInputs.holesCharacterization

#guard_msgs (drop info) in
#check Characterisation.InputAlphabetRelabeling.execution_map
#guard_msgs (drop info) in
#check EncodedNoDirectComputable.compile_correct
#guard_msgs (drop info) in
#check EncodedNoDirectComputable.solve_correct
#guard_msgs (drop info) in
#check EncodedNoDirectComputable.solve_eq_original

end DistributedSynthesis.Tests.GraphAdversaries
