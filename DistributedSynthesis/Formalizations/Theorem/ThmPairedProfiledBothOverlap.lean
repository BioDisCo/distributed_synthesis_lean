/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledPhaseInvariant

/-!
# The ambiguous profiled boundary

At a synchronizing `both` round, the old receiver still emits the closing
output of the old orientation while the other process has enough information
to start the staged opposite orientation.  The local modes need not agree.
The stored one-round profile proves that these two independently computed
outputs are nevertheless identical.

The theorems below are restricted to actual finite-controller prefixes.  No
process is given the orientation, the global phase, or a strict-leader bit;
the prefix witnesses occur only in the correctness proof.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Every real recurrent right prefix has a staged left candidate, and its
fresh output at an ambiguous synchronization equals the old right close. -/
theorem profiledBankRight_real_both_compatible
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (stagingMove : In₂ × In₁)
    (move : In₁ × In₂) :
    ∃ target : ProfiledBankLeftMacro A,
      (stepProfiledBankRightReceiverFor A source
        (profiledBankRightFiniteStateAfter A source past).1 row
        (profiledBankRightFiniteStateAfter A source past).2
        stagingMove).2.2 = some target ∧
      ProfiledBankRightBoundaryCompatible A
        ⟨source,
          (profiledBankRightFiniteStateAfter A source
            (past ++ [stagingMove])).1⟩
        ⟨source, row,
          (profiledBankRightFiniteStateAfter A source
            (past ++ [stagingMove])).2, some target⟩
        move false := by
  classical
  have hsome := profiledBankRight_real_close_staged A source row past
    stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepProfiledBankRightReceiverFor_pending_of_staged A source
      (profiledBankRightFiniteStateAfter A source past).1 row
      (profiledBankRightFiniteStateAfter A source past).2 stagingMove target
      hstage
  have hafter :
      profiledBankRightFiniteStateAfter A source (past ++ [stagingMove]) =
        stepProfiledBankRightFiniteState A source
          (profiledBankRightFiniteStateAfter A source past) stagingMove := by
    simp [profiledBankRightFiniteStateAfter, List.foldl_append]
  have hpending :
      (profiledBankRightFiniteStateAfter A source
        (past ++ [stagingMove])).2.2.2.1 row = some target.2.1.2 := by
    rw [hafter]
    rw [stepProfiledBankRightReceiverFor_monitor] at hpendingStep
    simpa [stepProfiledBankRightFiniteState, narrowedRecord] using hpendingStep
  have hold := profiledBankRight_real_overlap A source row
    (past ++ [stagingMove]) (move.2, move.1) target.2.1.2 hpending
  have hfresh := profiledBankLeft_root_profile A target move
  unfold ProfiledBankRightBoundaryCompatible
  simp only [switchProfiledBankRightOwnerToBankLeftReceiver,
    guardedEntryRowOfReceived]
  simp [continueProfiledBankLeftReceiver,
    initialProfiledBankLeftReceiver, initialProfiledBankLeftOwner,
    profiledBankLeftOwnerControlFor, profiledBankRightOwnerControlFor,
    stepProfiledBankLeftReceiverFor_output,
    stepProfiledBankRightReceiverFor_output]
  rw [hfresh, hold]

/-- Left-to-right mirror. -/
theorem profiledBankLeft_real_both_compatible
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (stagingMove : In₁ × In₂)
    (move : In₂ × In₁) :
    ∃ target : ProfiledBankRightMacro A,
      (stepProfiledBankLeftReceiverFor A source
        (profiledBankLeftFiniteStateAfter A source past).1 row
        (profiledBankLeftFiniteStateAfter A source past).2
        stagingMove).2.2 = some target ∧
      ProfiledBankLeftBoundaryCompatible A
        ⟨source,
          (profiledBankLeftFiniteStateAfter A source
            (past ++ [stagingMove])).1⟩
        ⟨source, row,
          (profiledBankLeftFiniteStateAfter A source
            (past ++ [stagingMove])).2, some target⟩
        move false := by
  classical
  have hsome := profiledBankLeft_real_close_staged A source row past stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepProfiledBankLeftReceiverFor_pending_of_staged A source
      (profiledBankLeftFiniteStateAfter A source past).1 row
      (profiledBankLeftFiniteStateAfter A source past).2 stagingMove target
      hstage
  have hafter :
      profiledBankLeftFiniteStateAfter A source (past ++ [stagingMove]) =
        stepProfiledBankLeftFiniteState A source
          (profiledBankLeftFiniteStateAfter A source past) stagingMove := by
    simp [profiledBankLeftFiniteStateAfter, List.foldl_append]
  have hpending :
      (profiledBankLeftFiniteStateAfter A source
        (past ++ [stagingMove])).2.2.2.1 row = some target.2.1.2 := by
    rw [hafter]
    rw [stepProfiledBankLeftReceiverFor_monitor] at hpendingStep
    simpa [stepProfiledBankLeftFiniteState, narrowedRecord] using hpendingStep
  have hold := profiledBankLeft_real_overlap A source row
    (past ++ [stagingMove]) (move.2, move.1) target.2.1.2 hpending
  have hfresh := profiledBankRight_root_profile A target move
  unfold ProfiledBankLeftBoundaryCompatible
  simp only [switchProfiledBankLeftOwnerToBankRightReceiver,
    guardedEntryRowOfReceived]
  simp [continueProfiledBankRightReceiver,
    initialProfiledBankRightReceiver, initialProfiledBankRightOwner,
    profiledBankRightOwnerControlFor, profiledBankLeftOwnerControlFor,
    stepProfiledBankRightReceiverFor_output,
    stepProfiledBankLeftReceiverFor_output]
  rw [hfresh, hold]

/-! ## Exceptional first blocks -/

variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

theorem profiledGuardedFirstRight_real_both_compatible
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (stagingMove : In₂ × In₁)
    (move : In₁ × In₂) :
    ∃ target : ProfiledBankLeftMacro A,
      (stepProfiledGuardedFirstRightReceiverFor A firstBank key
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1 row
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2
        stagingMove).2.2 = some target ∧
      ProfiledFirstRightBoundaryCompatible A firstBank
        ⟨key, (profiledGuardedFirstRightFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).1⟩
        ⟨key, row, (profiledGuardedFirstRightFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).2, some target⟩
        move false := by
  classical
  have hsome := profiledGuardedFirstRight_real_close_staged A firstBank key row
    past stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepProfiledGuardedFirstRightReceiverFor_pending_of_staged A firstBank key
      (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1 row
      (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2
      stagingMove target hstage
  have hafter :
      profiledGuardedFirstRightFiniteStateAfter A firstBank key
          (past ++ [stagingMove]) =
        stepProfiledGuardedFirstRightFiniteState A firstBank key
          (profiledGuardedFirstRightFiniteStateAfter A firstBank key past)
          stagingMove := by
    simp [profiledGuardedFirstRightFiniteStateAfter, List.foldl_append]
  have hpending :
      (profiledGuardedFirstRightFiniteStateAfter A firstBank key
        (past ++ [stagingMove])).2.2.2.1 row = some target.2.1.2 := by
    rw [hafter]
    rw [stepProfiledGuardedFirstRightReceiverFor_monitor] at hpendingStep
    simpa [stepProfiledGuardedFirstRightFiniteState, narrowedRecord] using
      hpendingStep
  have hold := profiledGuardedFirstRight_real_overlap A firstBank key row
    (past ++ [stagingMove]) (move.2, move.1) target.2.1.2 hpending
  have hfresh := profiledBankLeft_root_profile A target move
  unfold ProfiledFirstRightBoundaryCompatible
  simp only [switchProfiledFirstRightOwnerToBankLeftReceiver,
    guardedEntryRowOfReceived]
  simp [continueProfiledBankLeftReceiver,
    initialProfiledBankLeftReceiver, initialProfiledBankLeftOwner,
    profiledBankLeftOwnerControlFor,
    profiledGuardedFirstRightOwnerControlFor,
    stepProfiledBankLeftReceiverFor_output,
    stepProfiledGuardedFirstRightReceiverFor_output]
  rw [hfresh, hold]

theorem profiledGuardedFirstLeft_real_both_compatible
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (stagingMove : In₁ × In₂)
    (move : In₂ × In₁) :
    ∃ target : ProfiledBankRightMacro A,
      (stepProfiledGuardedFirstLeftReceiverFor A firstBank key
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1 row
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2
        stagingMove).2.2 = some target ∧
      ProfiledFirstLeftBoundaryCompatible A firstBank
        ⟨key, (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).1⟩
        ⟨key, row, (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).2, some target⟩
        move false := by
  classical
  have hsome := profiledGuardedFirstLeft_real_close_staged A firstBank key row
    past stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepProfiledGuardedFirstLeftReceiverFor_pending_of_staged A firstBank key
      (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1 row
      (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2
      stagingMove target hstage
  have hafter :
      profiledGuardedFirstLeftFiniteStateAfter A firstBank key
          (past ++ [stagingMove]) =
        stepProfiledGuardedFirstLeftFiniteState A firstBank key
          (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past)
          stagingMove := by
    simp [profiledGuardedFirstLeftFiniteStateAfter, List.foldl_append]
  have hpending :
      (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
        (past ++ [stagingMove])).2.2.2.1 row = some target.2.1.2 := by
    rw [hafter]
    rw [stepProfiledGuardedFirstLeftReceiverFor_monitor] at hpendingStep
    simpa [stepProfiledGuardedFirstLeftFiniteState, narrowedRecord] using
      hpendingStep
  have hold := profiledGuardedFirstLeft_real_overlap A firstBank key row
    (past ++ [stagingMove]) (move.2, move.1) target.2.1.2 hpending
  have hfresh := profiledBankRight_root_profile A target move
  unfold ProfiledFirstLeftBoundaryCompatible
  simp only [switchProfiledFirstLeftOwnerToBankRightReceiver,
    guardedEntryRowOfReceived]
  simp [continueProfiledBankRightReceiver,
    initialProfiledBankRightReceiver, initialProfiledBankRightOwner,
    profiledBankRightOwnerControlFor,
    profiledGuardedFirstLeftOwnerControlFor,
    stepProfiledBankRightReceiverFor_output,
    stepProfiledGuardedFirstLeftReceiverFor_output]
  rw [hfresh, hold]

end

end

end DetParityAutomaton

end DistributedSynthesis
