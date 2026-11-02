/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.SingletonInputs
import DistributedSynthesis.Library.Distributed.EncodedNoDirect

/-! The finite-private-input target. The adversary and its holes concern only
communication graphs; input streams are unrestricted and observed locally. -/
namespace Characterisation
open DistributedSynthesis

namespace WithInputs

/-- Reuse the original finite-input synthesis instance representation. -/
abbrev Instance := EncodedNoDirect.Instance

/-- All private input streams are quantified independently of the graph promise. -/
def Realizable (A : Set (Nat → Graph)) (d : Instance) : Prop :=
  ∃ σ : StrategyPair
      (Fin (d.inputOneSizeMinusOne + 1)) (Fin (d.inputTwoSizeMinusOne + 1))
      (Fin (d.outputOneSizeMinusOne + 1)) (Fin (d.outputTwoSizeMinusOne + 1)),
    ∀ env, (fun n => (env n).graph) ∈ A →
      LTL.Satisfies (EncodedNoDirect.interp d) (execution σ env)
        (EncodedFiniteLTL.decode d.formula)

/-- The positive target, proved by `positiveHolesCharacterization` in
`PositiveHolesComputable.lean`. -/
def PositiveHolesCharacterization : Prop :=
  ∀ A : Set (Nat → Graph), OmegaRegular A → GeometricHoles A →
    ComputablePred (Realizable A)

/-- The finite-private-input iff, proved by `holesCharacterization` in
`HolesIff.lean`. -/
def HolesCharacterization : Prop :=
  ∀ A : Set (Nat → Graph), OmegaRegular A →
    (ComputablePred (Realizable A) ↔ GeometricHoles A)

end WithInputs
end Characterisation
