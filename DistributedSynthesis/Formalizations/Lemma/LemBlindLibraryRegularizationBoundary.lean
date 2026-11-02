/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlindLibrarySourceRealization
import DistributedSynthesis.Formalizations.Lemma.LemFiniteBlindLiteralTraceObstruction

/-!
# The blind-regularization premise is not supplied by an arbitrary hwin

The accept-all objective has a winning source with a nonperiodic blind
stream. Even the weakened blind-only summary premise fails for this source.
Completeness must regularize a winning replacement, not assert that the
particular named strategy has finite blind residuals.
-/

namespace DistributedSynthesis
namespace BlindLibraryRegularizationBoundary

def rightEnvironment : EnvironmentSequence Unit Unit := fun _ ↦ ⟨(),(),.right⟩

variable (L : BlindControllerLibrary Unit Unit Bool Bool)
variable (strategy : StrategyPair Unit Unit Bool Bool)
variable (R : L.RealizesBlind strategy)

theorem blind_orbit (n : Nat) :
    (fun q ↦ (L.noRecvOne q ()).1)^[n] L.initialOne =
      R.one (currentView .one (executionPrefix strategy rightEnvironment n)) := by
  induction n with
  | zero => exact R.initialOne.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have h := congrArg Prod.fst (R.noRecvOne
      (executionPrefix strategy rightEnvironment n)
      (strategyGeneratedPrefix_executionPrefix strategy rightEnvironment n) ())
    dsimp only at h
    rw [h, executionPrefix_succ]
    simp [currentView, viewPair_append, advanceViews, nextRound, rightEnvironment]

include R in
theorem blind_output (n : Nat) :
    (L.noRecvOne ((fun q ↦ (L.noRecvOne q ()).1)^[n] L.initialOne) ()).2 =
      (execution strategy rightEnvironment n).outputOne := by
  rw [blind_orbit L strategy R]
  have h := congrArg Prod.snd (R.noRecvOne
    (executionPrefix strategy rightEnvironment n)
    (strategyGeneratedPrefix_executionPrefix strategy rightEnvironment n) ())
  dsimp only at h
  rw [h, execution_apply]
  rfl

variable [Finite L.OneControl]

/-- An already-proved winning source has no finite blind realization. Thus
the remaining normalization must be existential over winning replacements. -/
theorem pulse_no_finite_blind_realization :
    ¬ Nonempty (L.RealizesBlind powerOfTwoPulseStrategy) := by
  rintro ⟨R⟩
  apply powerOfTwoPulseStrategy_no_finite_literal_suffix
    (fun q ↦ (L.noRecvOne q ()).1) (fun q ↦ (L.noRecvOne q ()).2)
    L.initialOne rightEnvironment 0
  intro n
  simpa only [Nat.zero_add] using blind_output L powerOfTwoPulseStrategy R n

end BlindLibraryRegularizationBoundary
end DistributedSynthesis
