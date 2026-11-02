/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBothOverlap

/-!
# The two-candidate invariant through `both` rounds

A process cannot tell at a synchronizing round which strict orientation will
follow.  The finite implementation therefore retains two shadow executions:
one matched right phase and one matched left phase.  Process one locally keeps
the right owner together with the left receiver; process two keeps the right
receiver together with the left owner.  These are precisely the two controls
each process can update from its own input and a received partner summary.

The physical output is the process-one component of the left shadow and the
process-two component of the right shadow.  A later strict round merely
selects the corresponding shadow.  On a consecutive `both`, the old strict
orientation remains the anchor and its newly staged close refreshes the
opposite shadow.  Neither local state contains the current strict leader or
the constructor of the proof-level invariant.
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
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-- Proof-only orientation predicate.  It is deliberately not stored in a
local controller. -/
def ProfiledMatchedPhase.IsRight :
    ProfiledMatchedPhase A firstBank → Prop
  | .firstRight .. => True
  | .bankRight .. => True
  | .firstLeft .. => False
  | .bankLeft .. => False

/-- Mirror proof-only orientation predicate. -/
def ProfiledMatchedPhase.IsLeft :
    ProfiledMatchedPhase A firstBank → Prop
  | .firstRight .. => False
  | .bankRight .. => False
  | .firstLeft .. => True
  | .bankLeft .. => True

/-- Advancing a matched right phase preserves its proof orientation. -/
theorem ProfiledMatchedPhase.continue_isRight
    (phase : ProfiledMatchedPhase A firstBank)
    (move : In₁ × In₂) (h : phase.IsRight) :
    (phase.continue A firstBank move).2.IsRight := by
  cases phase <;> simp_all [ProfiledMatchedPhase.IsRight,
    ProfiledMatchedPhase.continue]

/-- Advancing a matched left phase preserves its proof orientation. -/
theorem ProfiledMatchedPhase.continue_isLeft
    (phase : ProfiledMatchedPhase A firstBank)
    (move : In₁ × In₂) (h : phase.IsLeft) :
    (phase.continue A firstBank move).2.IsLeft := by
  cases phase <;> simp_all [ProfiledMatchedPhase.IsLeft,
    ProfiledMatchedPhase.continue]

/-- The proof-level pair retained while the communication graph remains
ambiguous.  Its projections, not this structure, are stored locally. -/
structure ProfiledBothCandidates where
  right : ProfiledMatchedPhase A firstBank
  left : ProfiledMatchedPhase A firstBank
  right_oriented : right.IsRight
  left_oriented : left.IsLeft

/-- Process one's two finite shadows: right owner and left receiver. -/
def ProfiledBothCandidates.oneControl
    (candidates : ProfiledBothCandidates A firstBank) :
    ProfiledPhaseOneControl A firstBank × ProfiledPhaseOneControl A firstBank :=
  (candidates.right.oneControl, candidates.left.oneControl)

/-- Process two's two finite shadows: right receiver and left owner. -/
def ProfiledBothCandidates.twoControl
    (candidates : ProfiledBothCandidates A firstBank) :
    ProfiledPhaseTwoControl A firstBank × ProfiledPhaseTwoControl A firstBank :=
  (candidates.right.twoControl, candidates.left.twoControl)

/-- The actual output at an ambiguous round is assembled locally from the
left candidate at process one and the right candidate at process two. -/
def profiledBothPhysicalOutput
    (rightOutput leftOutput : Out₁ × Out₂) : Out₁ × Out₂ :=
  (leftOutput.1, rightOutput.2)

/-- Advance both shadows hypothetically as strict blocks on the same input.
This supplies the two resolution branches, but is not the consecutive-`both`
transition: that transition refreshes from the retained anchor. -/
noncomputable def ProfiledBothCandidates.advanceShadows
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × ProfiledBothCandidates A firstBank :=
  let rightStep := candidates.right.continue A firstBank move
  let leftStep := candidates.left.continue A firstBank move
  (profiledBothPhysicalOutput rightStep.1 leftStep.1,
    ⟨rightStep.2, leftStep.2,
      candidates.right.continue_isRight A firstBank move
        candidates.right_oriented,
      candidates.left.continue_isLeft A firstBank move
        candidates.left_oriented⟩)

@[simp] theorem ProfiledBothCandidates.advanceShadows_output_one
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (candidates.advanceShadows A firstBank move).1.1 =
      (candidates.left.continue A firstBank move).1.1 := rfl

@[simp] theorem ProfiledBothCandidates.advanceShadows_output_two
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (candidates.advanceShadows A firstBank move).1.2 =
      (candidates.right.continue A firstBank move).1.2 := rfl

@[simp] theorem ProfiledBothCandidates.advanceShadows_right
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (candidates.advanceShadows A firstBank move).2.right =
      (candidates.right.continue A firstBank move).2 := rfl

@[simp] theorem ProfiledBothCandidates.advanceShadows_left
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (candidates.advanceShadows A firstBank move).2.left =
      (candidates.left.continue A firstBank move).2 := rfl

/-- A following strict-right round resolves to the right shadow. -/
noncomputable def ProfiledBothCandidates.resolveRight
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × ProfiledMatchedPhase A firstBank :=
  candidates.right.continue A firstBank move

/-- A following strict-left round resolves to the left shadow. -/
noncomputable def ProfiledBothCandidates.resolveLeft
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × ProfiledMatchedPhase A firstBank :=
  candidates.left.continue A firstBank move

theorem ProfiledBothCandidates.resolveRight_oriented
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (candidates.resolveRight A firstBank move).2.IsRight :=
  candidates.right.continue_isRight A firstBank move
    candidates.right_oriented

theorem ProfiledBothCandidates.resolveLeft_oriented
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (candidates.resolveLeft A firstBank move).2.IsLeft :=
  candidates.left.continue_isLeft A firstBank move candidates.left_oriented

/-! ## Entering the ambiguous carrier from either matched orientation -/

/-- Start a two-candidate interval after a right-oriented matched phase.  The
old right shadow advances normally; the strict-switch calculation supplies
the new left shadow.  The mixed physical output is what the two local receive
transitions actually emit on `both`. -/
noncomputable def ProfiledMatchedPhase.enterBothFromRight
    (phase : ProfiledMatchedPhase A firstBank)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (ProfiledBothCandidates A firstBank) := by
  classical
  exact
    let rightStep := phase.continue A firstBank move
    let leftStep := phase.reverseRightToLeft A firstBank move false
    let candidates := leftStep.2.bind fun left =>
      if hright : rightStep.2.IsRight then
        if hleft : left.IsLeft then
          some ⟨rightStep.2, left, hright, hleft⟩
        else none
      else none
    (profiledBothPhysicalOutput rightStep.1 leftStep.1, candidates)

/-- Left-to-right mirror. -/
noncomputable def ProfiledMatchedPhase.enterBothFromLeft
    (phase : ProfiledMatchedPhase A firstBank)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (ProfiledBothCandidates A firstBank) := by
  classical
  exact
    let leftStep := phase.continue A firstBank move
    let rightStep := phase.reverseLeftToRight A firstBank (move.2, move.1) false
    let candidates := rightStep.2.bind fun right =>
      if hright : right.IsRight then
        if hleft : leftStep.2.IsLeft then
          some ⟨right, leftStep.2, hright, hleft⟩
        else none
      else none
    (profiledBothPhysicalOutput rightStep.1 leftStep.1, candidates)

/-- A consecutive synchronization in a right-anchored overlap is computed
from the right shadow again. -/
noncomputable def ProfiledBothCandidates.repeatBothFromRight
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (ProfiledBothCandidates A firstBank) :=
  candidates.right.enterBothFromRight A firstBank move

/-- Left-anchored mirror. -/
noncomputable def ProfiledBothCandidates.repeatBothFromLeft
    (candidates : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option (ProfiledBothCandidates A firstBank) :=
  candidates.left.enterBothFromLeft A firstBank move

@[simp] theorem ProfiledMatchedPhase.enterBothFromRight_output_one
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂) :
    (phase.enterBothFromRight A firstBank move).1.1 =
      (phase.reverseRightToLeft A firstBank move false).1.1 := rfl

@[simp] theorem ProfiledMatchedPhase.enterBothFromRight_output_two
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂) :
    (phase.enterBothFromRight A firstBank move).1.2 =
      (phase.continue A firstBank move).1.2 := rfl

@[simp] theorem ProfiledMatchedPhase.enterBothFromLeft_output_one
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂) :
    (phase.enterBothFromLeft A firstBank move).1.1 =
      (phase.continue A firstBank move).1.1 := rfl

@[simp] theorem ProfiledMatchedPhase.enterBothFromLeft_output_two
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂) :
    (phase.enterBothFromLeft A firstBank move).1.2 =
      (phase.reverseLeftToRight A firstBank (move.2, move.1) false).1.2 := rfl

/-! ## Identification with the paired `.both` successor record -/

/-- At an exceptional right boundary, compatibility says that the hybrid
local output is exactly the synchronizing record used by the old right
block's `.both` close. -/
theorem enterBothFromFirstRight_record_eq_close
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (sameKey : owner.1 = receiver.1) (move : In₁ × In₂)
    (hcompatible : ProfiledFirstRightBoundaryCompatible A firstBank owner
      receiver move false) :
    let phase : ProfiledMatchedPhase A firstBank :=
      .firstRight owner receiver sameKey
    bothRoundRecord move
        (phase.enterBothFromRight A firstBank move).1.1
        (phase.enterBothFromRight A firstBank move).1.2 =
      bothRoundRecord move
        (pairedRightClosingForRow receiver.2.1
          (stepProfiledGuardedFirstRightReceiverFor A firstBank receiver.1
            (profiledGuardedFirstRightOwnerControlFor A firstBank receiver
              owner)
            receiver.2.1 receiver.2.2.1 (move.2, move.1)).1.physical)
        (continueProfiledGuardedFirstRightReceiver A firstBank receiver owner
          (move.2, move.1)).1 := by
  dsimp only
  rw [ProfiledMatchedPhase.enterBothFromRight_output_one,
    ProfiledMatchedPhase.enterBothFromRight_output_two]
  change bothRoundRecord move
      (switchProfiledFirstRightOwnerToBankLeftReceiver A firstBank owner
        receiver move false).1
      (continueProfiledGuardedFirstRightReceiver A firstBank receiver owner
        (move.2, move.1)).1 = _
  rw [hcompatible]

/-- Recurrent right-boundary version. -/
theorem enterBothFromBankRight_record_eq_close
    (owner : ProfiledBankRightOwnerControl A)
    (receiver : ProfiledBankRightReceiverControl A)
    (sameKey : owner.1 = receiver.1) (move : In₁ × In₂)
    (hcompatible : ProfiledBankRightBoundaryCompatible A owner receiver move
      false) :
    let phase : ProfiledMatchedPhase A firstBank :=
      .bankRight owner receiver sameKey
    bothRoundRecord move
        (phase.enterBothFromRight A firstBank move).1.1
        (phase.enterBothFromRight A firstBank move).1.2 =
      bothRoundRecord move
        (pairedRightClosingForRow receiver.2.1
          (stepProfiledBankRightReceiverFor A receiver.1
            (profiledBankRightOwnerControlFor A receiver owner)
            receiver.2.1 receiver.2.2.1 (move.2, move.1)).1.physical)
        (continueProfiledBankRightReceiver A receiver owner
          (move.2, move.1)).1 := by
  dsimp only
  rw [ProfiledMatchedPhase.enterBothFromRight_output_one,
    ProfiledMatchedPhase.enterBothFromRight_output_two]
  change bothRoundRecord move
      (switchProfiledBankRightOwnerToBankLeftReceiver A owner receiver move
        false).1
      (continueProfiledBankRightReceiver A receiver owner
        (move.2, move.1)).1 = _
  rw [hcompatible]

/-- Exceptional left-to-right mirror. -/
theorem enterBothFromFirstLeft_record_eq_close
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (sameKey : receiver.1 = owner.1) (move : In₁ × In₂)
    (hcompatible : ProfiledFirstLeftBoundaryCompatible A firstBank owner
      receiver (move.2, move.1) false) :
    let phase : ProfiledMatchedPhase A firstBank :=
      .firstLeft receiver owner sameKey
    bothRoundRecord move
        (phase.enterBothFromLeft A firstBank move).1.1
        (phase.enterBothFromLeft A firstBank move).1.2 =
      bothRoundRecord move
        (continueProfiledGuardedFirstLeftReceiver A firstBank receiver owner
          move).1
        (pairedLeftClosingForRow receiver.2.1
          (stepProfiledGuardedFirstLeftReceiverFor A firstBank receiver.1
            (profiledGuardedFirstLeftOwnerControlFor A firstBank receiver
              owner)
            receiver.2.1 receiver.2.2.1 move).1.physical) := by
  dsimp only
  rw [ProfiledMatchedPhase.enterBothFromLeft_output_one,
    ProfiledMatchedPhase.enterBothFromLeft_output_two]
  change bothRoundRecord move
      (continueProfiledGuardedFirstLeftReceiver A firstBank receiver owner
        move).1
      (switchProfiledFirstLeftOwnerToBankRightReceiver A firstBank owner
        receiver (move.2, move.1) false).1 = _
  rw [hcompatible]

/-- Recurrent left-boundary mirror. -/
theorem enterBothFromBankLeft_record_eq_close
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A)
    (sameKey : receiver.1 = owner.1) (move : In₁ × In₂)
    (hcompatible : ProfiledBankLeftBoundaryCompatible A owner receiver
      (move.2, move.1) false) :
    let phase : ProfiledMatchedPhase A firstBank :=
      .bankLeft receiver owner sameKey
    bothRoundRecord move
        (phase.enterBothFromLeft A firstBank move).1.1
        (phase.enterBothFromLeft A firstBank move).1.2 =
      bothRoundRecord move
        (continueProfiledBankLeftReceiver A receiver owner move).1
        (pairedLeftClosingForRow receiver.2.1
          (stepProfiledBankLeftReceiverFor A receiver.1
            (profiledBankLeftOwnerControlFor A receiver owner)
            receiver.2.1 receiver.2.2.1 move).1.physical) := by
  dsimp only
  rw [ProfiledMatchedPhase.enterBothFromLeft_output_one,
    ProfiledMatchedPhase.enterBothFromLeft_output_two]
  change bothRoundRecord move
      (continueProfiledBankLeftReceiver A receiver owner move).1
      (switchProfiledBankLeftOwnerToBankRightReceiver A owner receiver
        (move.2, move.1) false).1 = _
  rw [hcompatible]

/-! ## Successful candidate creation from a staged close -/

theorem enterBothFromFirstRight_isSome_of_staged
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (sameKey : owner.1 = receiver.1) (move : In₁ × In₂)
    (target : ProfiledBankLeftMacro A)
    (hstaged : receiver.2.2.2 = some target) :
    ((ProfiledMatchedPhase.firstRight owner receiver sameKey).enterBothFromRight
      A firstBank move).2.isSome := by
  classical
  rcases receiver with ⟨key, row, monitor, staged⟩
  simp only at hstaged
  subst staged
  simp [ProfiledMatchedPhase.enterBothFromRight,
    ProfiledMatchedPhase.continue, ProfiledMatchedPhase.reverseRightToLeft,
    switchProfiledFirstRightOwnerToBankLeftReceiver,
    switchProfiledFirstRightReceiverToBankLeftOwner,
    ProfiledMatchedPhase.IsRight, ProfiledMatchedPhase.IsLeft]

theorem enterBothFromBankRight_isSome_of_staged
    (owner : ProfiledBankRightOwnerControl A)
    (receiver : ProfiledBankRightReceiverControl A)
    (sameKey : owner.1 = receiver.1) (move : In₁ × In₂)
    (target : ProfiledBankLeftMacro A)
    (hstaged : receiver.2.2.2 = some target) :
    ((ProfiledMatchedPhase.bankRight owner receiver sameKey).enterBothFromRight
      A firstBank move).2.isSome := by
  classical
  rcases receiver with ⟨source, row, monitor, staged⟩
  simp only at hstaged
  subst staged
  simp [ProfiledMatchedPhase.enterBothFromRight,
    ProfiledMatchedPhase.continue, ProfiledMatchedPhase.reverseRightToLeft,
    switchProfiledBankRightOwnerToBankLeftReceiver,
    switchProfiledBankRightReceiverToBankLeftOwner,
    ProfiledMatchedPhase.IsRight, ProfiledMatchedPhase.IsLeft]

theorem enterBothFromFirstLeft_isSome_of_staged
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (sameKey : receiver.1 = owner.1) (move : In₁ × In₂)
    (target : ProfiledBankRightMacro A)
    (hstaged : receiver.2.2.2 = some target) :
    ((ProfiledMatchedPhase.firstLeft receiver owner sameKey).enterBothFromLeft
      A firstBank move).2.isSome := by
  classical
  rcases receiver with ⟨key, row, monitor, staged⟩
  simp only at hstaged
  subst staged
  simp [ProfiledMatchedPhase.enterBothFromLeft,
    ProfiledMatchedPhase.continue, ProfiledMatchedPhase.reverseLeftToRight,
    switchProfiledFirstLeftOwnerToBankRightReceiver,
    switchProfiledFirstLeftReceiverToBankRightOwner,
    ProfiledMatchedPhase.IsRight, ProfiledMatchedPhase.IsLeft]

theorem enterBothFromBankLeft_isSome_of_staged
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A)
    (sameKey : receiver.1 = owner.1) (move : In₁ × In₂)
    (target : ProfiledBankRightMacro A)
    (hstaged : receiver.2.2.2 = some target) :
    ((ProfiledMatchedPhase.bankLeft receiver owner sameKey).enterBothFromLeft
      A firstBank move).2.isSome := by
  classical
  rcases receiver with ⟨source, row, monitor, staged⟩
  simp only at hstaged
  subst staged
  simp [ProfiledMatchedPhase.enterBothFromLeft,
    ProfiledMatchedPhase.continue, ProfiledMatchedPhase.reverseLeftToRight,
    switchProfiledBankLeftOwnerToBankRightReceiver,
    switchProfiledBankLeftReceiverToBankRightOwner,
    ProfiledMatchedPhase.IsRight, ProfiledMatchedPhase.IsLeft]

/-! ## Reachable boundary packages -/

/-- Everything the global proof consumes at a right-anchored ambiguous
boundary: a finite candidate pair exists and the physical record is the
paired right close with the supplied closing output. -/
def ProfiledRightBothEntrySound
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂)
    (closing : Out₁) : Prop :=
  (phase.enterBothFromRight A firstBank move).2.isSome ∧
    bothRoundRecord move
        (phase.enterBothFromRight A firstBank move).1.1
        (phase.enterBothFromRight A firstBank move).1.2 =
      bothRoundRecord move closing
        (phase.continue A firstBank move).1.2

/-- Left-anchored mirror. -/
def ProfiledLeftBothEntrySound
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂)
    (closing : Out₂) : Prop :=
  (phase.enterBothFromLeft A firstBank move).2.isSome ∧
    bothRoundRecord move
        (phase.enterBothFromLeft A firstBank move).1.1
        (phase.enterBothFromLeft A firstBank move).1.2 =
      bothRoundRecord move
        (phase.continue A firstBank move).1.1 closing

/-- Every real recurrent right prefix produces a sound, nonempty ambiguous
entry package. -/
theorem profiledBankRight_real_both_entry_sound
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (stagingMove : In₂ × In₁)
    (move : In₁ × In₂) :
    ∃ target : ProfiledBankLeftMacro A,
      (stepProfiledBankRightReceiverFor A source
        (profiledBankRightFiniteStateAfter A source past).1 row
        (profiledBankRightFiniteStateAfter A source past).2
        stagingMove).2.2 = some target ∧
      let owner : ProfiledBankRightOwnerControl A :=
        ⟨source, (profiledBankRightFiniteStateAfter A source
          (past ++ [stagingMove])).1⟩
      let receiver : ProfiledBankRightReceiverControl A :=
        ⟨source, row, (profiledBankRightFiniteStateAfter A source
          (past ++ [stagingMove])).2, some target⟩
      ProfiledRightBothEntrySound A firstBank
        (.bankRight owner receiver rfl) move
        (pairedRightClosingForRow row
          (stepProfiledBankRightReceiverFor A source
            (profiledBankRightFiniteStateAfter A source
              (past ++ [stagingMove])).1 row
            (profiledBankRightFiniteStateAfter A source
              (past ++ [stagingMove])).2
            (move.2, move.1)).1.physical) := by
  obtain ⟨target, hstage, hcompatible⟩ :=
    profiledBankRight_real_both_compatible A source row past stagingMove move
  refine ⟨target, hstage, ?_⟩
  dsimp only
  constructor
  · exact enterBothFromBankRight_isSome_of_staged A firstBank _ _ rfl move
      target rfl
  · simpa [ProfiledMatchedPhase.continue,
        profiledBankRightOwnerControlFor] using
      (enterBothFromBankRight_record_eq_close A firstBank _ _ rfl move
        hcompatible)

/-- Every real recurrent left prefix produces the mirror package. -/
theorem profiledBankLeft_real_both_entry_sound
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (stagingMove : In₁ × In₂)
    (move : In₁ × In₂) :
    ∃ target : ProfiledBankRightMacro A,
      (stepProfiledBankLeftReceiverFor A source
        (profiledBankLeftFiniteStateAfter A source past).1 row
        (profiledBankLeftFiniteStateAfter A source past).2
        stagingMove).2.2 = some target ∧
      let receiver : ProfiledBankLeftReceiverControl A :=
        ⟨source, row, (profiledBankLeftFiniteStateAfter A source
          (past ++ [stagingMove])).2, some target⟩
      let owner : ProfiledBankLeftOwnerControl A :=
        ⟨source, (profiledBankLeftFiniteStateAfter A source
          (past ++ [stagingMove])).1⟩
      ProfiledLeftBothEntrySound A firstBank
        (.bankLeft receiver owner rfl) move
        (pairedLeftClosingForRow row
          (stepProfiledBankLeftReceiverFor A source
            (profiledBankLeftFiniteStateAfter A source
              (past ++ [stagingMove])).1 row
            (profiledBankLeftFiniteStateAfter A source
              (past ++ [stagingMove])).2 move).1.physical) := by
  obtain ⟨target, hstage, hcompatible⟩ :=
    profiledBankLeft_real_both_compatible A source row past stagingMove
      (move.2, move.1)
  refine ⟨target, hstage, ?_⟩
  dsimp only
  constructor
  · exact enterBothFromBankLeft_isSome_of_staged A firstBank _ _ rfl move
      target rfl
  · simpa [ProfiledMatchedPhase.continue,
        profiledBankLeftOwnerControlFor] using
      (enterBothFromBankLeft_record_eq_close A firstBank _ _ rfl move
        hcompatible)

/-- Exceptional first-right prefixes enter the same recurrent overlap
carrier. -/
theorem profiledGuardedFirstRight_real_both_entry_sound
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (stagingMove : In₂ × In₁)
    (move : In₁ × In₂) :
    ∃ target : ProfiledBankLeftMacro A,
      (stepProfiledGuardedFirstRightReceiverFor A firstBank key
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1 row
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2
        stagingMove).2.2 = some target ∧
      let owner : ProfiledGuardedFirstRightOwnerControl A firstBank :=
        ⟨key, (profiledGuardedFirstRightFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).1⟩
      let receiver : ProfiledGuardedFirstRightActiveReceiverControl A :=
        ⟨key, row, (profiledGuardedFirstRightFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).2, some target⟩
      ProfiledRightBothEntrySound A firstBank
        (.firstRight owner receiver rfl) move
        (pairedRightClosingForRow row
          (stepProfiledGuardedFirstRightReceiverFor A firstBank key
            (profiledGuardedFirstRightFiniteStateAfter A firstBank key
              (past ++ [stagingMove])).1 row
            (profiledGuardedFirstRightFiniteStateAfter A firstBank key
              (past ++ [stagingMove])).2
            (move.2, move.1)).1.physical) := by
  obtain ⟨target, hstage, hcompatible⟩ :=
    profiledGuardedFirstRight_real_both_compatible A firstBank key row past
      stagingMove move
  refine ⟨target, hstage, ?_⟩
  dsimp only
  constructor
  · exact enterBothFromFirstRight_isSome_of_staged A firstBank _ _ rfl move
      target rfl
  · simpa [ProfiledMatchedPhase.continue,
        profiledGuardedFirstRightOwnerControlFor] using
      (enterBothFromFirstRight_record_eq_close A firstBank _ _ rfl move
        hcompatible)

/-- Exceptional first-left mirror. -/
theorem profiledGuardedFirstLeft_real_both_entry_sound
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (stagingMove : In₁ × In₂)
    (move : In₁ × In₂) :
    ∃ target : ProfiledBankRightMacro A,
      (stepProfiledGuardedFirstLeftReceiverFor A firstBank key
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1 row
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2
        stagingMove).2.2 = some target ∧
      let receiver : ProfiledGuardedFirstLeftActiveReceiverControl A :=
        ⟨key, row, (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).2, some target⟩
      let owner : ProfiledGuardedFirstLeftOwnerControl A firstBank :=
        ⟨key, (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
          (past ++ [stagingMove])).1⟩
      ProfiledLeftBothEntrySound A firstBank
        (.firstLeft receiver owner rfl) move
        (pairedLeftClosingForRow row
          (stepProfiledGuardedFirstLeftReceiverFor A firstBank key
            (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
              (past ++ [stagingMove])).1 row
            (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
              (past ++ [stagingMove])).2 move).1.physical) := by
  obtain ⟨target, hstage, hcompatible⟩ :=
    profiledGuardedFirstLeft_real_both_compatible A firstBank key row past
      stagingMove (move.2, move.1)
  refine ⟨target, hstage, ?_⟩
  dsimp only
  constructor
  · exact enterBothFromFirstLeft_isSome_of_staged A firstBank _ _ rfl move
      target rfl
  · simpa [ProfiledMatchedPhase.continue,
        profiledGuardedFirstLeftOwnerControlFor] using
      (enterBothFromFirstLeft_record_eq_close A firstBank _ _ rfl move
        hcompatible)

/-! ## Anchor recurrence through consecutive synchronizations -/

/-- The right component returned by a right-anchored entry is exactly the
ordinary one-step continuation of the anchor. -/
theorem enterBothFromBankRight_candidate_right
    (owner : ProfiledBankRightOwnerControl A)
    (receiver : ProfiledBankRightReceiverControl A)
    (sameKey : owner.1 = receiver.1) (move : In₁ × In₂)
    (candidates : ProfiledBothCandidates A firstBank)
    (hentry :
      (ProfiledMatchedPhase.enterBothFromRight A firstBank
        (.bankRight owner receiver sameKey) move).2 = some candidates) :
    candidates.right =
      ((ProfiledMatchedPhase.bankRight owner receiver sameKey).continue
        A firstBank move).2 := by
  classical
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged <;>
    simp [ProfiledMatchedPhase.enterBothFromRight,
      ProfiledMatchedPhase.continue,
      ProfiledMatchedPhase.reverseRightToLeft,
      switchProfiledBankRightOwnerToBankLeftReceiver,
      switchProfiledBankRightReceiverToBankLeftOwner,
      ProfiledMatchedPhase.IsRight, ProfiledMatchedPhase.IsLeft] at hentry
  subst candidates
  rfl

/-- Left anchor mirror. -/
theorem enterBothFromBankLeft_candidate_left
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A)
    (sameKey : receiver.1 = owner.1) (move : In₁ × In₂)
    (candidates : ProfiledBothCandidates A firstBank)
    (hentry :
      (ProfiledMatchedPhase.enterBothFromLeft A firstBank
        (.bankLeft receiver owner sameKey) move).2 = some candidates) :
    candidates.left =
      ((ProfiledMatchedPhase.bankLeft receiver owner sameKey).continue
        A firstBank move).2 := by
  classical
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged <;>
    simp [ProfiledMatchedPhase.enterBothFromLeft,
      ProfiledMatchedPhase.continue,
      ProfiledMatchedPhase.reverseLeftToRight,
      switchProfiledBankLeftOwnerToBankRightReceiver,
      switchProfiledBankLeftReceiverToBankRightOwner,
      ProfiledMatchedPhase.IsRight, ProfiledMatchedPhase.IsLeft] at hentry
  subst candidates
  rfl

/-- Exact replay of the right anchor: its hypothetical continuation is the
real finite-controller state at the extended input prefix, including the
freshly staged target used by the next synchronization. -/
theorem bankRight_continue_eq_real_phase
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledBankLeftMacro A)) (move : In₂ × In₁)
    (target : ProfiledBankLeftMacro A)
    (hstaged :
      (stepProfiledBankRightReceiverFor A source
        (profiledBankRightFiniteStateAfter A source past).1 row
        (profiledBankRightFiniteStateAfter A source past).2 move).2.2 =
          some target) :
    let owner : ProfiledBankRightOwnerControl A :=
      ⟨source, (profiledBankRightFiniteStateAfter A source past).1⟩
    let receiver : ProfiledBankRightReceiverControl A :=
      ⟨source, row, (profiledBankRightFiniteStateAfter A source past).2,
        pending⟩
    ((ProfiledMatchedPhase.bankRight owner receiver rfl).continue A firstBank
      (move.2, move.1)).2 =
      .bankRight
        ⟨source, (profiledBankRightFiniteStateAfter A source
          (past ++ [move])).1⟩
        ⟨source, row, (profiledBankRightFiniteStateAfter A source
          (past ++ [move])).2, some target⟩ rfl := by
  dsimp only
  have hafter :
      profiledBankRightFiniteStateAfter A source (past ++ [move]) =
        stepProfiledBankRightFiniteState A source
          (profiledBankRightFiniteStateAfter A source past) move := by
    simp [profiledBankRightFiniteStateAfter, List.foldl_append]
  rw [hafter]
  simp [ProfiledMatchedPhase.continue, continueProfiledBankRightReceiver,
    profiledBankRightOwnerControlFor, stepProfiledBankRightOwner,
    stepProfiledBankRightFiniteState,
    stepProfiledBankRightReceiverFor_monitor, hstaged]

/-- Left anchor mirror. -/
theorem bankLeft_continue_eq_real_phase
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledBankRightMacro A)) (move : In₁ × In₂)
    (target : ProfiledBankRightMacro A)
    (hstaged :
      (stepProfiledBankLeftReceiverFor A source
        (profiledBankLeftFiniteStateAfter A source past).1 row
        (profiledBankLeftFiniteStateAfter A source past).2 move).2.2 =
          some target) :
    let receiver : ProfiledBankLeftReceiverControl A :=
      ⟨source, row, (profiledBankLeftFiniteStateAfter A source past).2,
        pending⟩
    let owner : ProfiledBankLeftOwnerControl A :=
      ⟨source, (profiledBankLeftFiniteStateAfter A source past).1⟩
    ((ProfiledMatchedPhase.bankLeft receiver owner rfl).continue A firstBank
      move).2 =
      .bankLeft
        ⟨source, row, (profiledBankLeftFiniteStateAfter A source
          (past ++ [move])).2, some target⟩
        ⟨source, (profiledBankLeftFiniteStateAfter A source
          (past ++ [move])).1⟩ rfl := by
  dsimp only
  have hafter :
      profiledBankLeftFiniteStateAfter A source (past ++ [move]) =
        stepProfiledBankLeftFiniteState A source
          (profiledBankLeftFiniteStateAfter A source past) move := by
    simp [profiledBankLeftFiniteStateAfter, List.foldl_append]
  rw [hafter]
  simp [ProfiledMatchedPhase.continue, continueProfiledBankLeftReceiver,
    profiledBankLeftOwnerControlFor, stepProfiledBankLeftOwner,
    stepProfiledBankLeftFiniteState,
    stepProfiledBankLeftReceiverFor_monitor, hstaged]

/-- Exact replay of an exceptional right phase at a concrete finite-controller
prefix.  This is the first-block analogue of
`bankRight_continue_eq_real_phase`. -/
theorem guardedFirstRight_continue_eq_real_phase
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledBankLeftMacro A)) (move : In₂ × In₁)
    (target : ProfiledBankLeftMacro A)
    (hstaged :
      (stepProfiledGuardedFirstRightReceiverFor A firstBank key
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1 row
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2
        move).2.2 = some target) :
    let owner : ProfiledGuardedFirstRightOwnerControl A firstBank :=
      ⟨key, (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1⟩
    let receiver : ProfiledGuardedFirstRightActiveReceiverControl A :=
      ⟨key, row,
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2,
        pending⟩
    ((ProfiledMatchedPhase.firstRight owner receiver rfl).continue A firstBank
      (move.2, move.1)).2 =
      .firstRight
        ⟨key, (profiledGuardedFirstRightFiniteStateAfter A firstBank key
          (past ++ [move])).1⟩
        ⟨key, row,
          (profiledGuardedFirstRightFiniteStateAfter A firstBank key
            (past ++ [move])).2, some target⟩ rfl := by
  dsimp only
  have hafter :
      profiledGuardedFirstRightFiniteStateAfter A firstBank key
          (past ++ [move]) =
        stepProfiledGuardedFirstRightFiniteState A firstBank key
          (profiledGuardedFirstRightFiniteStateAfter A firstBank key past)
          move := by
    simp [profiledGuardedFirstRightFiniteStateAfter, List.foldl_append]
  rw [hafter]
  simp [ProfiledMatchedPhase.continue,
    continueProfiledGuardedFirstRightReceiver,
    profiledGuardedFirstRightOwnerControlFor,
    stepProfiledGuardedFirstRightOwner,
    stepProfiledGuardedFirstRightFiniteState,
    stepProfiledGuardedFirstRightReceiverFor_monitor, hstaged]

/-- Exceptional left mirror. -/
theorem guardedFirstLeft_continue_eq_real_phase
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledBankRightMacro A)) (move : In₁ × In₂)
    (target : ProfiledBankRightMacro A)
    (hstaged :
      (stepProfiledGuardedFirstLeftReceiverFor A firstBank key
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1 row
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2
        move).2.2 = some target) :
    let receiver : ProfiledGuardedFirstLeftActiveReceiverControl A :=
      ⟨key, row,
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2,
        pending⟩
    let owner : ProfiledGuardedFirstLeftOwnerControl A firstBank :=
      ⟨key, (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1⟩
    ((ProfiledMatchedPhase.firstLeft receiver owner rfl).continue A firstBank
      move).2 =
      .firstLeft
        ⟨key, row,
          (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
            (past ++ [move])).2, some target⟩
        ⟨key, (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
          (past ++ [move])).1⟩ rfl := by
  dsimp only
  have hafter :
      profiledGuardedFirstLeftFiniteStateAfter A firstBank key
          (past ++ [move]) =
        stepProfiledGuardedFirstLeftFiniteState A firstBank key
          (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past)
          move := by
    simp [profiledGuardedFirstLeftFiniteStateAfter, List.foldl_append]
  rw [hafter]
  simp [ProfiledMatchedPhase.continue,
    continueProfiledGuardedFirstLeftReceiver,
    profiledGuardedFirstLeftOwnerControlFor,
    stepProfiledGuardedFirstLeftOwner,
    stepProfiledGuardedFirstLeftFiniteState,
    stepProfiledGuardedFirstLeftReceiverFor_monitor, hstaged]

/-- A concrete recurrent right anchor at a finite controller prefix. -/
def IsRealProfiledBankRightPhaseAt
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (target : ProfiledBankLeftMacro A)
    (phase : ProfiledMatchedPhase A firstBank) : Prop :=
  phase = .bankRight
    ⟨source, (profiledBankRightFiniteStateAfter A source past).1⟩
    ⟨source, row, (profiledBankRightFiniteStateAfter A source past).2,
      some target⟩ rfl

/-- Left anchor mirror. -/
def IsRealProfiledBankLeftPhaseAt
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (target : ProfiledBankRightMacro A)
    (phase : ProfiledMatchedPhase A firstBank) : Prop :=
  phase = .bankLeft
    ⟨source, row, (profiledBankLeftFiniteStateAfter A source past).2,
      some target⟩
    ⟨source, (profiledBankLeftFiniteStateAfter A source past).1⟩ rfl

/-- A concrete exceptional right phase at a finite controller prefix. -/
def IsRealProfiledFirstRightPhaseAt
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (target : ProfiledBankLeftMacro A)
    (phase : ProfiledMatchedPhase A firstBank) : Prop :=
  phase = .firstRight
    ⟨key, (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1⟩
    ⟨key, row,
      (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2,
      some target⟩ rfl

/-- Exceptional left mirror. -/
def IsRealProfiledFirstLeftPhaseAt
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (target : ProfiledBankRightMacro A)
    (phase : ProfiledMatchedPhase A firstBank) : Prop :=
  phase = .firstLeft
    ⟨key, row,
      (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2,
      some target⟩
    ⟨key, (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1⟩
    rfl

/-- A phase is real when it is a concrete prefix of one of the four selected
finite controllers.  This predicate is proof-only and reveals no orientation
to either process. -/
def IsRealProfiledPhase (phase : ProfiledMatchedPhase A firstBank) : Prop :=
  (∃ key row past target,
    IsRealProfiledFirstRightPhaseAt A firstBank key row past target phase) ∨
  (∃ key row past target,
    IsRealProfiledFirstLeftPhaseAt A firstBank key row past target phase) ∨
  (∃ source row past target,
    IsRealProfiledBankRightPhaseAt A firstBank source row past target phase) ∨
  (∃ source row past target,
    IsRealProfiledBankLeftPhaseAt A firstBank source row past target phase)

/-- Ordinary continuation preserves concrete-prefix reality in all four
phase modes. -/
theorem isRealProfiledPhase_continue
    (phase : ProfiledMatchedPhase A firstBank)
    (hreal : IsRealProfiledPhase A firstBank phase)
    (move : In₁ × In₂) :
    IsRealProfiledPhase A firstBank
      (phase.continue A firstBank move).2 := by
  rcases hreal with hfirstRight | hfirstLeft | hbankRight | hbankLeft
  · rcases hfirstRight with ⟨key, row, past, pending, rfl⟩
    obtain ⟨target, hstaged, _⟩ :=
      profiledGuardedFirstRight_real_both_entry_sound A firstBank key row past
        (move.2, move.1) (default, default)
    left
    refine ⟨key, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealProfiledFirstRightPhaseAt
    exact guardedFirstRight_continue_eq_real_phase A firstBank key row past
      (some pending) (move.2, move.1) target hstaged
  · rcases hfirstLeft with ⟨key, row, past, pending, rfl⟩
    obtain ⟨target, hstaged, _⟩ :=
      profiledGuardedFirstLeft_real_both_entry_sound A firstBank key row past
        move (default, default)
    right; left
    refine ⟨key, row, past ++ [move], target, ?_⟩
    unfold IsRealProfiledFirstLeftPhaseAt
    exact guardedFirstLeft_continue_eq_real_phase A firstBank key row past
      (some pending) move target hstaged
  · rcases hbankRight with ⟨source, row, past, pending, rfl⟩
    obtain ⟨target, hstaged, _⟩ :=
      profiledBankRight_real_both_entry_sound A firstBank source row past
        (move.2, move.1) (default, default)
    right; right; left
    refine ⟨source, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealProfiledBankRightPhaseAt
    exact bankRight_continue_eq_real_phase A firstBank source row past
      (some pending) (move.2, move.1) target hstaged
  · rcases hbankLeft with ⟨source, row, past, pending, rfl⟩
    obtain ⟨target, hstaged, _⟩ :=
      profiledBankLeft_real_both_entry_sound A firstBank source row past move
        (default, default)
    right; right; right
    refine ⟨source, row, past ++ [move], target, ?_⟩
    unfold IsRealProfiledBankLeftPhaseAt
    exact bankLeft_continue_eq_real_phase A firstBank source row past
      (some pending) move target hstaged

/-- A real right-oriented phase reverses into a real left-bank prefix. -/
theorem isRealProfiledPhase_reverseRightToLeft
    (phase : ProfiledMatchedPhase A firstBank)
    (hreal : IsRealProfiledPhase A firstBank phase)
    (hright : phase.IsRight) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    ∃ next,
      (phase.reverseRightToLeft A firstBank move previouslyReceived).2 =
          some next ∧
        IsRealProfiledPhase A firstBank next := by
  rcases hreal with hfirstRight | hfirstLeft | hbankRight | hbankLeft
  · rcases hfirstRight with ⟨key, row, past, target, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    obtain ⟨nextTarget, hstaged, _⟩ :=
      profiledBankLeft_real_both_entry_sound A firstBank target newRow [] move
        (default, default)
    let base : ProfiledMatchedPhase A firstBank := .bankLeft
      (initialProfiledBankLeftReceiver A target newRow)
      (initialProfiledBankLeftOwner A target) rfl
    have hbase := bankLeft_continue_eq_real_phase A firstBank target newRow []
      none move nextTarget hstaged
    refine ⟨(base.continue A firstBank move).2, ?_, ?_⟩
    · simp [newRow, ProfiledMatchedPhase.reverseRightToLeft,
        switchProfiledFirstRightOwnerToBankLeftReceiver,
        switchProfiledFirstRightReceiverToBankLeftOwner,
        ProfiledMatchedPhase.continue, base]
    · right; right; right
      refine ⟨target, newRow, [move], nextTarget, ?_⟩
      unfold IsRealProfiledBankLeftPhaseAt
      exact hbase
  · rcases hfirstLeft with ⟨key, row, past, target, hphase⟩
    rw [hphase] at hright
    simp [ProfiledMatchedPhase.IsRight] at hright
  · rcases hbankRight with ⟨source, row, past, target, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    obtain ⟨nextTarget, hstaged, _⟩ :=
      profiledBankLeft_real_both_entry_sound A firstBank target newRow [] move
        (default, default)
    let base : ProfiledMatchedPhase A firstBank := .bankLeft
      (initialProfiledBankLeftReceiver A target newRow)
      (initialProfiledBankLeftOwner A target) rfl
    have hbase := bankLeft_continue_eq_real_phase A firstBank target newRow []
      none move nextTarget hstaged
    refine ⟨(base.continue A firstBank move).2, ?_, ?_⟩
    · simp [newRow, ProfiledMatchedPhase.reverseRightToLeft,
        switchProfiledBankRightOwnerToBankLeftReceiver,
        switchProfiledBankRightReceiverToBankLeftOwner,
        ProfiledMatchedPhase.continue, base]
    · right; right; right
      refine ⟨target, newRow, [move], nextTarget, ?_⟩
      unfold IsRealProfiledBankLeftPhaseAt
      exact hbase
  · rcases hbankLeft with ⟨source, row, past, target, hphase⟩
    rw [hphase] at hright
    simp [ProfiledMatchedPhase.IsRight] at hright

/-- Left-to-right mirror. -/
theorem isRealProfiledPhase_reverseLeftToRight
    (phase : ProfiledMatchedPhase A firstBank)
    (hreal : IsRealProfiledPhase A firstBank phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    ∃ next,
      (phase.reverseLeftToRight A firstBank (move.2, move.1)
          previouslyReceived).2 = some next ∧
        IsRealProfiledPhase A firstBank next := by
  rcases hreal with hfirstRight | hfirstLeft | hbankRight | hbankLeft
  · rcases hfirstRight with ⟨key, row, past, target, hphase⟩
    rw [hphase] at hleft
    simp [ProfiledMatchedPhase.IsLeft] at hleft
  · rcases hfirstLeft with ⟨key, row, past, target, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    obtain ⟨nextTarget, hstaged, _⟩ :=
      profiledBankRight_real_both_entry_sound A firstBank target newRow []
        (move.2, move.1) (default, default)
    let base : ProfiledMatchedPhase A firstBank := .bankRight
      (initialProfiledBankRightOwner A target)
      (initialProfiledBankRightReceiver A target newRow) rfl
    have hbase := bankRight_continue_eq_real_phase A firstBank target newRow []
      none (move.2, move.1) nextTarget hstaged
    refine ⟨(base.continue A firstBank move).2, ?_, ?_⟩
    · simp [newRow, ProfiledMatchedPhase.reverseLeftToRight,
        switchProfiledFirstLeftOwnerToBankRightReceiver,
        switchProfiledFirstLeftReceiverToBankRightOwner,
        ProfiledMatchedPhase.continue, base]
    · right; right; left
      refine ⟨target, newRow, [(move.2, move.1)], nextTarget, ?_⟩
      unfold IsRealProfiledBankRightPhaseAt
      exact hbase
  · rcases hbankRight with ⟨source, row, past, target, hphase⟩
    rw [hphase] at hleft
    simp [ProfiledMatchedPhase.IsLeft] at hleft
  · rcases hbankLeft with ⟨source, row, past, target, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    obtain ⟨nextTarget, hstaged, _⟩ :=
      profiledBankRight_real_both_entry_sound A firstBank target newRow []
        (move.2, move.1) (default, default)
    let base : ProfiledMatchedPhase A firstBank := .bankRight
      (initialProfiledBankRightOwner A target)
      (initialProfiledBankRightReceiver A target newRow) rfl
    have hbase := bankRight_continue_eq_real_phase A firstBank target newRow []
      none (move.2, move.1) nextTarget hstaged
    refine ⟨(base.continue A firstBank move).2, ?_, ?_⟩
    · simp [newRow, ProfiledMatchedPhase.reverseLeftToRight,
        switchProfiledBankLeftOwnerToBankRightReceiver,
        switchProfiledBankLeftReceiverToBankRightOwner,
        ProfiledMatchedPhase.continue, base]
    · right; right; left
      refine ⟨target, newRow, [(move.2, move.1)], nextTarget, ?_⟩
      unfold IsRealProfiledBankRightPhaseAt
      exact hbase

/-- The consecutive-`both` fail-fast test, right anchored.  Any returned
candidate pair has a right component equal to the real finite-controller
prefix after the current synchronization, and refreshing from that component
on the next synchronization again yields a sound paired `.both` close. -/
theorem profiledBankRight_real_repeatBoth_sound
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (ProfiledBankLeftMacro A)) (move : In₂ × In₁)
    (candidates : ProfiledBothCandidates A firstBank)
    (hentry :
      let owner : ProfiledBankRightOwnerControl A :=
        ⟨source, (profiledBankRightFiniteStateAfter A source past).1⟩
      let receiver : ProfiledBankRightReceiverControl A :=
        ⟨source, row, (profiledBankRightFiniteStateAfter A source past).2,
          pending⟩
      (ProfiledMatchedPhase.enterBothFromRight A firstBank
        (.bankRight owner receiver rfl) (move.2, move.1)).2 =
          some candidates)
    (nextMove : In₁ × In₂) :
    ∃ target : ProfiledBankLeftMacro A,
      IsRealProfiledBankRightPhaseAt A firstBank source row
        (past ++ [move]) target candidates.right ∧
      ProfiledRightBothEntrySound A firstBank candidates.right nextMove
        (pairedRightClosingForRow row
          (stepProfiledBankRightReceiverFor A source
            (profiledBankRightFiniteStateAfter A source
              (past ++ [move])).1 row
            (profiledBankRightFiniteStateAfter A source
              (past ++ [move])).2
            (nextMove.2, nextMove.1)).1.physical) := by
  obtain ⟨target, hstaged, hsound⟩ :=
    profiledBankRight_real_both_entry_sound A firstBank source row past move
      nextMove
  let owner : ProfiledBankRightOwnerControl A :=
    ⟨source, (profiledBankRightFiniteStateAfter A source past).1⟩
  let receiver : ProfiledBankRightReceiverControl A :=
    ⟨source, row, (profiledBankRightFiniteStateAfter A source past).2,
      pending⟩
  have hanchor : candidates.right =
      ((ProfiledMatchedPhase.bankRight owner receiver rfl).continue A firstBank
        (move.2, move.1)).2 :=
    enterBothFromBankRight_candidate_right A firstBank owner receiver rfl
      (move.2, move.1) candidates hentry
  have hreplay := bankRight_continue_eq_real_phase A firstBank source row past
    pending move target hstaged
  have hreal : IsRealProfiledBankRightPhaseAt A firstBank source row
      (past ++ [move]) target candidates.right := by
    unfold IsRealProfiledBankRightPhaseAt
    exact hanchor.trans hreplay
  refine ⟨target, hreal, ?_⟩
  rw [hreal]
  exact hsound

/-- Consecutive-`both` mirror for a left anchor. -/
theorem profiledBankLeft_real_repeatBoth_sound
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (ProfiledBankRightMacro A)) (move : In₁ × In₂)
    (candidates : ProfiledBothCandidates A firstBank)
    (hentry :
      let receiver : ProfiledBankLeftReceiverControl A :=
        ⟨source, row, (profiledBankLeftFiniteStateAfter A source past).2,
          pending⟩
      let owner : ProfiledBankLeftOwnerControl A :=
        ⟨source, (profiledBankLeftFiniteStateAfter A source past).1⟩
      (ProfiledMatchedPhase.enterBothFromLeft A firstBank
        (.bankLeft receiver owner rfl) move).2 = some candidates)
    (nextMove : In₁ × In₂) :
    ∃ target : ProfiledBankRightMacro A,
      IsRealProfiledBankLeftPhaseAt A firstBank source row
        (past ++ [move]) target candidates.left ∧
      ProfiledLeftBothEntrySound A firstBank candidates.left nextMove
        (pairedLeftClosingForRow row
          (stepProfiledBankLeftReceiverFor A source
            (profiledBankLeftFiniteStateAfter A source
              (past ++ [move])).1 row
            (profiledBankLeftFiniteStateAfter A source
              (past ++ [move])).2 nextMove).1.physical) := by
  obtain ⟨target, hstaged, hsound⟩ :=
    profiledBankLeft_real_both_entry_sound A firstBank source row past move
      nextMove
  let receiver : ProfiledBankLeftReceiverControl A :=
    ⟨source, row, (profiledBankLeftFiniteStateAfter A source past).2,
      pending⟩
  let owner : ProfiledBankLeftOwnerControl A :=
    ⟨source, (profiledBankLeftFiniteStateAfter A source past).1⟩
  have hanchor : candidates.left =
      ((ProfiledMatchedPhase.bankLeft receiver owner rfl).continue A firstBank
        move).2 :=
    enterBothFromBankLeft_candidate_left A firstBank receiver owner rfl move
      candidates hentry
  have hreplay := bankLeft_continue_eq_real_phase A firstBank source row past
    pending move target hstaged
  have hreal : IsRealProfiledBankLeftPhaseAt A firstBank source row
      (past ++ [move]) target candidates.left := by
    unfold IsRealProfiledBankLeftPhaseAt
    exact hanchor.trans hreplay
  refine ⟨target, hreal, ?_⟩
  rw [hreal]
  exact hsound

end

end

end DetParityAutomaton

end DistributedSynthesis
