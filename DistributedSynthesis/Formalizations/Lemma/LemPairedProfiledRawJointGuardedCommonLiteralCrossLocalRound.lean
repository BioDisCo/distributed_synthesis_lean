/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossLocalCarrier

/-!
# Synchronized rounds of the literal cross carriers

This file specializes the generic cross-anchor round equation to the two
literal tables retained by the guarded common policy.  It also projects the
certificate-valued receiver result to its actual `informedBoth` physical
output.

The final synchronized-state wrappers are proof-side trace machines for a
fixed orientation.  Their two component transitions are the already defined
endpoint-local maps.  In particular, neither endpoint transition receives a
graph, an orientation, a leader bit, a strict-leader bit, or a semantic
history.  Switching orientations is deliberately outside this file.
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

/-! ## The concrete monitor families -/

private noncomputable abbrev RightBaseMonitor
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A) :=
  profiledRawJointRightPhysicalSiblingMonitor A descriptor false

private noncomputable abbrev RightMonitor :=
  finiteCrossAnchorLiteralPrefixMonitor (RightBaseMonitor A)

private abbrev RightFirstAllowed :=
  finiteCrossAnchorLiteralPrefixFirstAllowed (RightBaseMonitor A)

private abbrev RightSecondAllowed :=
  finiteCrossAnchorLiteralPrefixSecondAllowed (RightBaseMonitor A)

private noncomputable abbrev RightGuard
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily
    (fun member => RightMonitor A (move.1.descriptor member)) move.1.start
    (RightFirstAllowed A move.1) (RightSecondAllowed A move.1) anchor

private noncomputable abbrev LeftBaseMonitor
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A) :=
  profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor

private noncomputable abbrev LeftMonitor :=
  finiteCrossAnchorLiteralPrefixMonitor (LeftBaseMonitor A)

private abbrev LeftFirstAllowed :=
  finiteCrossAnchorLiteralPrefixFirstAllowed (LeftBaseMonitor A)

private abbrev LeftSecondAllowed :=
  finiteCrossAnchorLiteralPrefixSecondAllowed (LeftBaseMonitor A)

private noncomputable abbrev LeftGuard
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily
    (fun member => LeftMonitor A (move.1.descriptor member)) move.1.start
    (LeftFirstAllowed A move.1) (LeftSecondAllowed A move.1) anchor

/-! ## Exact right and left rounds -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

section
omit [Inhabited In₁] [Inhabited In₂]

/-- A synchronized right-oriented local round is exactly the narrowed record
of the installed literal table. -/
theorem profiledRawJointGuardedCommonRightLiteralCross_localRound_eq
    (sender : ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A)
    (receiver : ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₂) (delivered : In₁) :
    let senderStep :=
      profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A sender
        delivered
    let receiverStep :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiver own
        delivered
    ((own, delivered), receiverStep.1, senderStep.1) =
      narrowedRecord (RightGuard A receiver.1 receiver.2.1)
        ((receiver.1.memberController (RightMonitor A) receiver.2.1).labelOf
        receiver.2.2.1)
        receiver.2.2.2 (own, delivered) := by
  letI : Inhabited (ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) :=
    ⟨((receiver.1.memberController (RightMonitor A) receiver.2.1).labelOf
      receiver.2.2.1).2 receiver.2.2.2 (own, delivered)⟩
  exact finiteCrossAnchorDescriptorFirstTwo_localRound_eq
    (RightMonitor A) (RightFirstAllowed A) (RightSecondAllowed A)
    sender receiver hmove hsync own delivered

/-- A synchronized right round retains the same table identifier and equal
copies of its blind controller control. -/
theorem profiledRawJointGuardedCommonRightLiteralCross_localRound_preserves
    (sender : ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A)
    (receiver : ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₂) (delivered : In₁) :
    let senderNext :=
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A sender
        delivered).2
    let receiverNext :=
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiver own
        delivered).2
    senderNext.1 = receiverNext.1 ∧
      HEq senderNext.2 receiverNext.2.2.1 := by
  letI : Inhabited (ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) :=
    ⟨((receiver.1.memberController (RightMonitor A) receiver.2.1).labelOf
      receiver.2.2.1).2 receiver.2.2.2 (own, delivered)⟩
  exact finiteCrossAnchorDescriptorFirstTwo_localRound_preserves
    (RightMonitor A) (RightFirstAllowed A) (RightSecondAllowed A)
    sender receiver hmove hsync own delivered

/-- A synchronized left-oriented local round is the mirror narrowed record. -/
theorem profiledRawJointGuardedCommonLeftLiteralCross_localRound_eq
    (sender : ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A)
    (receiver : ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₁) (delivered : In₂) :
    let senderStep :=
      profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A sender
        delivered
    let receiverStep :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiver own
        delivered
    ((own, delivered), receiverStep.1, senderStep.1) =
      narrowedRecord (LeftGuard A receiver.1 receiver.2.1)
        ((receiver.1.memberController (LeftMonitor A) receiver.2.1).labelOf
        receiver.2.2.1)
        receiver.2.2.2 (own, delivered) := by
  letI : Inhabited (ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) :=
    ⟨((receiver.1.memberController (LeftMonitor A) receiver.2.1).labelOf
      receiver.2.2.1).2 receiver.2.2.2 (own, delivered)⟩
  exact finiteCrossAnchorDescriptorFirstTwo_localRound_eq
    (LeftMonitor A) (LeftFirstAllowed A) (LeftSecondAllowed A)
    sender receiver hmove hsync own delivered

/-- The left-oriented round preserves the same synchronization invariant. -/
theorem profiledRawJointGuardedCommonLeftLiteralCross_localRound_preserves
    (sender : ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A)
    (receiver : ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₁) (delivered : In₂) :
    let senderNext :=
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A sender
        delivered).2
    let receiverNext :=
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiver own
        delivered).2
    senderNext.1 = receiverNext.1 ∧
      HEq senderNext.2 receiverNext.2.2.1 := by
  letI : Inhabited (ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) :=
    ⟨((receiver.1.memberController (LeftMonitor A) receiver.2.1).labelOf
      receiver.2.2.1).2 receiver.2.2.2 (own, delivered)⟩
  exact finiteCrossAnchorDescriptorFirstTwo_localRound_preserves
    (LeftMonitor A) (LeftFirstAllowed A) (LeftSecondAllowed A)
    sender receiver hmove hsync own delivered

end

end

/-! ## Physical projections of the exact rounds -/

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
/-- The process-one sender output and process-two `informedBoth` receiver
output are the two physical coordinates of the right narrowed record. -/
theorem
    profiledRawJointGuardedCommonRightLiteralCross_localRound_physicalOutputs
    (sender : ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A)
    (receiver : ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₂) (delivered : In₁) :
    let senderStep :=
      profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A sender
        delivered
    let receiverStep :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        receiver own delivered
    let raw := narrowedRecord (RightGuard A receiver.1 receiver.2.1)
      ((receiver.1.memberController (RightMonitor A) receiver.2.1).labelOf
        receiver.2.2.1)
      receiver.2.2.2 (own, delivered)
    (senderStep.1, receiverStep.1) =
      (raw.2.2,
        profiledRawJointTargetRightReceiverBothPhysicalOutput raw.2.1) := by
  have hraw :=
    profiledRawJointGuardedCommonRightLiteralCross_localRound_eq A sender
      receiver hmove hsync own delivered
  have hphysical := congrArg
    (fun record =>
      (record.2.2,
        profiledRawJointTargetRightReceiverBothPhysicalOutput record.2.1))
    hraw
  simpa only
    [profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical,
      profiledRawJointTargetRightReceiverResultPhysicalOutput] using hphysical

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
/-- Process-one `informedBoth` and the process-two sender output are the two
physical coordinates of the left narrowed record. -/
theorem
    profiledRawJointGuardedCommonLeftLiteralCross_localRound_physicalOutputs
    (sender : ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A)
    (receiver : ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : In₁) (delivered : In₂) :
    let senderStep :=
      profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A sender
        delivered
    let receiverStep :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        receiver own delivered
    let raw := narrowedRecord (LeftGuard A receiver.1 receiver.2.1)
      ((receiver.1.memberController (LeftMonitor A) receiver.2.1).labelOf
        receiver.2.2.1)
      receiver.2.2.2 (own, delivered)
    (receiverStep.1, senderStep.1) =
      (profiledRawJointTargetLeftReceiverBothPhysicalOutput raw.2.1,
        raw.2.2) := by
  have hraw :=
    profiledRawJointGuardedCommonLeftLiteralCross_localRound_eq A sender
      receiver hmove hsync own delivered
  have hphysical := congrArg
    (fun record =>
      (profiledRawJointTargetLeftReceiverBothPhysicalOutput record.2.1,
        record.2.2))
    hraw
  simpa only
    [profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical,
      profiledRawJointTargetLeftReceiverResultPhysicalOutput] using hphysical

/-! ## Stable proof-side trace states -/

/-- Synchronized endpoint states for a right-oriented literal table.  This is
a trace invariant, not one process's executable state: its two projections
are exactly the separate local carrier states. -/
structure ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState where
  sender : ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A
  receiver : ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A
  move_eq : sender.1 = receiver.1
  controls_heq : HEq sender.2 receiver.2.2.1

noncomputable instance
    profiledRawJointGuardedCommonRightLiteralCrossSynchronizedStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState A) :=
  by
    classical
    let project := fun
        state : ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState A
        => (state.sender, state.receiver)
    letI : Finite
        (ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState A) :=
      Finite.of_injective project (by
        intro left right heq
        cases left with
        | mk leftSender leftReceiver leftMove leftControl =>
          cases right with
          | mk rightSender rightReceiver rightMove rightControl =>
            simp only [project, Prod.mk.injEq] at heq
            cases heq.1
            cases heq.2
            rfl)
    exact Fintype.ofFinite _

/-- Install both local roots of one right table and remember only their
mathematical synchronization proof. -/
noncomputable def
    profiledRawJointGuardedCommonRightLiteralCrossSynchronizedInitial
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState A where
  sender :=
    profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move
  receiver :=
    profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move anchor
  move_eq := rfl
  controls_heq := by
    apply heq_of_eq
    exact profiledRawJointGuardedCommonRightLiteralCross_initial_controls_eq A
      move anchor

/-- One stable right-oriented trace step, assembled from the two endpoint
local transitions.  Its output is ordered as `(process one, process two)`. -/
noncomputable def
    profiledRawJointGuardedCommonRightLiteralCrossSynchronizedStep
    (state : ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState A)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState A := by
  let senderResult :=
    profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A state.sender
      input.1
  let receiverResult :=
    profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A state.receiver
      input.2 input.1
  have hpreserve :=
    profiledRawJointGuardedCommonRightLiteralCross_localRound_preserves A
      state.sender state.receiver state.move_eq state.controls_heq input.2
      input.1
  exact
    ((senderResult.1,
        profiledRawJointTargetRightReceiverResultPhysicalOutput receiverResult),
      { sender := senderResult.2
        receiver := receiverResult.2
        move_eq := hpreserve.1
        controls_heq := hpreserve.2 })

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
/-- The stable right trace step emits exactly the physical projection of its
narrowed literal-table round. -/
theorem
    profiledRawJointGuardedCommonRightLiteralCrossSynchronizedStep_output_eq
    (state : ProfiledRawJointGuardedCommonRightLiteralCrossSynchronizedState A)
    (input : In₁ × In₂) :
    let raw := narrowedRecord
      (RightGuard A state.receiver.1 state.receiver.2.1)
      ((state.receiver.1.memberController (RightMonitor A)
        state.receiver.2.1).labelOf state.receiver.2.2.1)
      state.receiver.2.2.2 (input.2, input.1)
    (profiledRawJointGuardedCommonRightLiteralCrossSynchronizedStep A state
      input).1 =
      (raw.2.2,
        profiledRawJointTargetRightReceiverBothPhysicalOutput raw.2.1) := by
  have hphysical :=
    profiledRawJointGuardedCommonRightLiteralCross_localRound_physicalOutputs A
      state.sender state.receiver state.move_eq state.controls_heq input.2
      input.1
  simpa only
    [profiledRawJointGuardedCommonRightLiteralCrossSynchronizedStep] using
      hphysical

/-- Left-oriented mirror of the synchronized trace state. -/
structure ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState where
  sender : ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A
  receiver : ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A
  move_eq : sender.1 = receiver.1
  controls_heq : HEq sender.2 receiver.2.2.1

noncomputable instance
    profiledRawJointGuardedCommonLeftLiteralCrossSynchronizedStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState A) :=
  by
    classical
    let project := fun
        state : ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState A
        => (state.sender, state.receiver)
    letI : Finite
        (ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState A) :=
      Finite.of_injective project (by
        intro left right heq
        cases left with
        | mk leftSender leftReceiver leftMove leftControl =>
          cases right with
          | mk rightSender rightReceiver rightMove rightControl =>
            simp only [project, Prod.mk.injEq] at heq
            cases heq.1
            cases heq.2
            rfl)
    exact Fintype.ofFinite _

/-- Install the two roots of a left literal table. -/
noncomputable def
    profiledRawJointGuardedCommonLeftLiteralCrossSynchronizedInitial
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState A where
  sender := profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move
  receiver :=
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move anchor
  move_eq := rfl
  controls_heq := by
    apply heq_of_eq
    exact profiledRawJointGuardedCommonLeftLiteralCross_initial_controls_eq A
      move anchor

/-- One stable left-oriented trace step, again ordered as
`(process one, process two)`. -/
noncomputable def
    profiledRawJointGuardedCommonLeftLiteralCrossSynchronizedStep
    (state : ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState A)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState A := by
  let senderResult :=
    profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A state.sender
      input.2
  let receiverResult :=
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A state.receiver
      input.1 input.2
  have hpreserve :=
    profiledRawJointGuardedCommonLeftLiteralCross_localRound_preserves A
      state.sender state.receiver state.move_eq state.controls_heq input.1
      input.2
  exact
    ((profiledRawJointTargetLeftReceiverResultPhysicalOutput receiverResult,
        senderResult.1),
      { sender := senderResult.2
        receiver := receiverResult.2
        move_eq := hpreserve.1
        controls_heq := hpreserve.2 })

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
/-- The stable left trace emits the mirror physical narrowed record. -/
theorem
    profiledRawJointGuardedCommonLeftLiteralCrossSynchronizedStep_output_eq
    (state : ProfiledRawJointGuardedCommonLeftLiteralCrossSynchronizedState A)
    (input : In₁ × In₂) :
    let raw := narrowedRecord
      (LeftGuard A state.receiver.1 state.receiver.2.1)
      ((state.receiver.1.memberController (LeftMonitor A)
        state.receiver.2.1).labelOf state.receiver.2.2.1)
      state.receiver.2.2.2 input
    (profiledRawJointGuardedCommonLeftLiteralCrossSynchronizedStep A state
      input).1 =
      (profiledRawJointTargetLeftReceiverBothPhysicalOutput raw.2.1,
        raw.2.2) := by
  have hphysical :=
    profiledRawJointGuardedCommonLeftLiteralCross_localRound_physicalOutputs A
      state.sender state.receiver state.move_eq state.controls_heq input.1
      input.2
  simpa only
    [profiledRawJointGuardedCommonLeftLiteralCrossSynchronizedStep] using
      hphysical

end

end DetParityAutomaton

end DistributedSynthesis
