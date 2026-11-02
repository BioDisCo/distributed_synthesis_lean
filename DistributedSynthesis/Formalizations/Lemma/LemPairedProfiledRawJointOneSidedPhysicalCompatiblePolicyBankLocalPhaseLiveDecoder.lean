/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLive

/-!
# Decoding the bank-linked phase-live seam

The phase-live packet seam needs a control for the dormant receiver's exact
dependent physical move.  That control is not an oracle: in a deferred state
it is stored in the other endpoint's shared sender, while in a staged state
it is the initial owner contained in the staged packet successor.

This file performs that finite extraction with an explicit move-equality
check.  It first proves the most fragile closure case: after a simultaneous
close, the immediate opposite strict direction presents two deferred
controls.  The old receiver, its matching owner, and its dormant bank
coordinate are all recovered exactly.  The staged cases remain a separate
semantic closure obligation because their packet/receiver lineage must be
shown equal by the selected invariant.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

/-! ## Dependent owner alignment -/

/-- Check that a delivered left owner belongs to the dormant left receiver's
exact move, and return the correctly typed owner control. -/
noncomputable def profiledRawJointRecurrentAlignDormantLeftOwner?
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    Option ((receiver.1.memberController A false).Control) := by
  classical
  rcases owner with ⟨ownerMove, ownerControl⟩
  rcases receiver with ⟨receiverMove, row, receiverState, target⟩
  by_cases hmove : ownerMove = receiverMove
  · subst receiverMove
    exact some ownerControl
  · exact none

/-- Right-owner mirror. -/
noncomputable def profiledRawJointRecurrentAlignDormantRightOwner?
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    Option ((receiver.1.memberController A false).Control) := by
  classical
  rcases owner with ⟨ownerMove, ownerControl⟩
  rcases receiver with ⟨receiverMove, row, receiverState, target⟩
  by_cases hmove : ownerMove = receiverMove
  · subst receiverMove
    exact some ownerControl
  · exact none

/-! ## Runtime extraction from the opposite endpoint -/

/-- Recover the owner for a dormant left receiver from process two.  A
staged right receiver contributes the initial left owner from its packet;
a deferred left-to-right control contributes its stored left sender. -/
noncomputable def profiledRawJointRecurrentDormantLeftOwner?
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    Option ((receiver.1.memberController A false).Control) :=
  match two.1 with
  | .inl (.inl staged) =>
      match staged.2.2 with
      | none => none
      | some packet =>
          match packet.successor.2.1.2.2 with
          | none => none
          | some move =>
              profiledRawJointRecurrentAlignDormantLeftOwner? A
                ⟨move, (move.memberController A false).initial⟩ receiver
  | .inr deferred =>
      profiledRawJointRecurrentAlignDormantLeftOwner? A deferred.2.1 receiver
  | _ => none

/-- Mirrored extraction from process one. -/
noncomputable def profiledRawJointRecurrentDormantRightOwner?
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    Option ((receiver.1.memberController A false).Control) :=
  match one.1 with
  | .inl (.inl staged) =>
      match staged.2.2 with
      | none => none
      | some packet =>
          match packet.successor.2.1.2.1 with
          | none => none
          | some move =>
              profiledRawJointRecurrentAlignDormantRightOwner? A
                ⟨move, (move.memberController A false).initial⟩ receiver
  | .inr deferred =>
      profiledRawJointRecurrentAlignDormantRightOwner? A deferred.2.1 receiver
  | _ => none

/-! ## Phase-live aligned boundary data -/

/-- A decoded right boundary together with the bank coordinate and matching
owner of its dormant left receiver. -/
noncomputable abbrev ProfiledRawJointRecurrentRightPhaseLiveBoundaryData :=
  Sigma fun data :
      ProfiledRawJointRecurrentRightBoundaryData A strategy hwin ↦
    BankControl A strategy hwin ×
      (data.2.2.1.memberController A false).Control

/-- Mirrored left boundary package. -/
noncomputable abbrev ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData :=
  Sigma fun data :
      ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin ↦
    BankControl A strategy hwin ×
      (data.2.2.1.memberController A false).Control

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) := by
  classical
  infer_instance

/-- Decode the ordinary right-oriented data, then recover the dormant left
owner from process two.  The dormant bank coordinate is process one's local
left coordinate, stored beside the dormant receiver. -/
noncomputable def profiledRawJointRecurrentRightPhaseLiveBoundaryData?
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin) :
    Option
      (ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) :=
  match profiledRawJointRecurrentTrackedRightBoundaryData? A strategy hwin one
      two with
  | none => none
  | some data =>
      match profiledRawJointRecurrentDormantLeftOwner? A strategy hwin two
          data.2.2 with
      | none => none
      | some owner => some ⟨data, one.2.2, owner⟩

/-- Mirrored decoder.  The dormant right bank coordinate is process two's
local right coordinate. -/
noncomputable def profiledRawJointRecurrentLeftPhaseLiveBoundaryData?
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin) :
    Option
      (ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) :=
  match profiledRawJointRecurrentTrackedLeftBoundaryData? A strategy hwin one
      two with
  | none => none
  | some data =>
      match profiledRawJointRecurrentDormantRightOwner? A strategy hwin one
          data.2.2 with
      | none => none
      | some owner => some ⟨data, two.2.1, owner⟩

/-! ## The immediate-reversal fail-fast case -/

/-- In the right-oriented deferred/deferred shape, the decoder recovers the
matching dormant left owner and process one's exact left bank coordinate. -/
@[simp] theorem
    profiledRawJointRecurrentRightPhaseLiveBoundaryData?_deferredDeferred
    (rightState leftStateOne leftStateTwo : BankControl A strategy hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (rightOwner : (rightMove.memberController A false).Control)
    (rightRow : PairedEntryRow)
    (rightReceiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1 false).State)
    (rightTarget : Option (ProfiledRawJointUnitTarget A))
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (leftOwner : (leftMove.memberController A false).Control)
    (leftRow : PairedEntryRow)
    (leftReceiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false).State)
    (leftTarget : Option (ProfiledRawJointUnitTarget A)) :
    profiledRawJointRecurrentRightPhaseLiveBoundaryData? A strategy hwin
      ((.inr
          (true,
            (⟨rightMove, rightOwner⟩ :
              ProfiledRawJointRightPhysicalSiblingExceptional A),
            (⟨leftMove, leftRow, leftReceiverState, leftTarget⟩ :
              ProfiledRawJointLeftPhysicalSiblingReceiver A))),
        rightState, leftStateOne)
      ((.inr
          (false,
            (⟨leftMove, leftOwner⟩ :
              ProfiledRawJointLeftPhysicalSiblingExceptional A),
            (⟨rightMove, rightRow, rightReceiverState, rightTarget⟩ :
              ProfiledRawJointRightPhysicalSiblingReceiver A))),
        rightState, leftStateTwo) =
      some
        ⟨(rightState,
            ⟨⟨rightMove, rightRow, rightReceiverState, rightTarget⟩,
              rightOwner⟩,
            ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩),
          leftStateOne, leftOwner⟩ := by
  simp [profiledRawJointRecurrentRightPhaseLiveBoundaryData?,
    profiledRawJointRecurrentDormantLeftOwner?,
    profiledRawJointRecurrentAlignDormantLeftOwner?]

/-- Left-oriented mirror, with member pattern `(false,true)`. -/
@[simp] theorem
    profiledRawJointRecurrentLeftPhaseLiveBoundaryData?_deferredDeferred
    (rightStateOne rightStateTwo leftState : BankControl A strategy hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (leftOwner : (leftMove.memberController A false).Control)
    (leftRow : PairedEntryRow)
    (leftReceiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false).State)
    (leftTarget : Option (ProfiledRawJointUnitTarget A))
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (rightOwner : (rightMove.memberController A false).Control)
    (rightRow : PairedEntryRow)
    (rightReceiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1 false).State)
    (rightTarget : Option (ProfiledRawJointUnitTarget A)) :
    profiledRawJointRecurrentLeftPhaseLiveBoundaryData? A strategy hwin
      ((.inr
          (false,
            (⟨rightMove, rightOwner⟩ :
              ProfiledRawJointRightPhysicalSiblingExceptional A),
            (⟨leftMove, leftRow, leftReceiverState, leftTarget⟩ :
              ProfiledRawJointLeftPhysicalSiblingReceiver A))),
        rightStateOne, leftState)
      ((.inr
          (true,
            (⟨leftMove, leftOwner⟩ :
              ProfiledRawJointLeftPhysicalSiblingExceptional A),
            (⟨rightMove, rightRow, rightReceiverState, rightTarget⟩ :
              ProfiledRawJointRightPhysicalSiblingReceiver A))),
        rightStateTwo, leftState) =
      some
        ⟨(leftState,
            ⟨⟨leftMove, leftRow, leftReceiverState, leftTarget⟩,
              leftOwner⟩,
            ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩),
          rightStateTwo, rightOwner⟩ := by
  simp [profiledRawJointRecurrentLeftPhaseLiveBoundaryData?,
    profiledRawJointRecurrentDormantRightOwner?,
    profiledRawJointRecurrentAlignDormantRightOwner?]

end

end DetParityAutomaton

end DistributedSynthesis
