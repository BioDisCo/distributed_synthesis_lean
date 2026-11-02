/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshRightLiveStageAudit

/-!
# Phase-local activation of a live right stage

The pending-only audit found a constructor mismatch at a left-to-right
reversal: the old handler stayed in the pending table although the retained
right receiver already contained the exact stage needed to enter the checked
recurrent pair.

This file supplies the smallest repaired branch.  A process-one no-receive
whose local freshness tag says that it was a receiver activates the retained
right stage.  Process two makes the same choice in the open branch of its
receive fork, using the delivered process-one receiver.  Both maps inspect
only their stored finite phase tag and locally available controls.  They do
not receive a graph, orientation, hierarchy side, leader bit, history, or
view.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev RightReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev RightSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev RightStage (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

private abbrev RightOne (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
    package

private abbrev RightTwo (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
    package

private abbrev OneShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package (RightOne A strategy hwin package)

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package (RightTwo A strategy hwin package)

private abbrev LeftSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

/-! ## Updating the selected retained receiver -/

/-- Replace exactly the branch selected by the already resolved member bit.
The other branch is retained.  This is a local finite-state update, not a
choice based on the current graph. -/
def literalCombinedFreshReplaceCandidate {Control : Type*}
    (fork : FiniteDelayedFork Control) (member : Bool) (next : Control) :
    FiniteDelayedFork Control :=
  if member then
    ⟨fork.openControl, next⟩
  else
    ⟨next, fork.closedControl⟩

@[simp] theorem literalCombinedFreshReplaceCandidate_candidate
    {Control : Type*} (fork : FiniteDelayedFork Control) (member : Bool)
    (next : Control) :
    (literalCombinedFreshReplaceCandidate fork member next).candidate member =
      next := by
  cases member <;> rfl

@[simp] theorem literalCombinedFreshReplaceCandidate_other
    {Control : Type*} (fork : FiniteDelayedFork Control) (member : Bool)
    (next : Control) :
    (literalCombinedFreshReplaceCandidate fork member next).candidate (!member) =
      fork.candidate (!member) := by
  cases member <;> rfl

/-! ## Same-direction right continuation -/

/-- A right receive advances the selected retained left receiver instead of
discarding it and recreating two stage-free roots.  At the same time it
freshens only the dormant right sender.  The open receiver branch is the
advanced live receiver; the closed branch is the fresh `.both,true` root.
Thus a later strict right-to-left reversal has a reachable live stage to
consume, while a simultaneous round still has its fresh closed meaning. -/
noncomputable def literalCombinedFreshRightContinueRecvTwo
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    TwoPending A strategy hwin package × Out₂ :=
  let receiver := package.literalCombinedFreshTwoReceiver A strategy hwin
    two.1 two.2.1
  let result := package.literalLeftSeamStagedReceiverRecv A strategy hwin
    receiver own delivered
  let freshShared := package.literalCombinedFreshTwoReceiveShared A strategy
    hwin two.2.1 own one.2.1 delivered
  let nextShared : TwoShared A strategy hwin package :=
    (freshShared.1, freshShared.2.1,
      ⟨result.2, freshShared.2.2.closedControl⟩)
  ((false, nextShared, (none :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
        hwin package)),
    package.literalCombinedFreshTwoPendingReceiveOutput A strategy hwin two.1
      two.2.1 own delivered)

@[simp] theorem literalCombinedFreshRightContinueRecvTwo_member
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshRightContinueRecvTwo A strategy hwin two own
      one delivered).1.1 = false :=
  rfl

@[simp] theorem literalCombinedFreshRightContinueRecvTwo_selectedReceiver
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    package.literalCombinedFreshTwoReceiver A strategy hwin
        (package.literalCombinedFreshRightContinueRecvTwo A strategy hwin two
          own one delivered).1.1
        (package.literalCombinedFreshRightContinueRecvTwo A strategy hwin two
          own one delivered).1.2.1 =
      (package.literalLeftSeamStagedReceiverRecv A strategy hwin
        (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
          two.2.1) own delivered).2 := by
  rfl

@[simp] theorem literalCombinedFreshRightContinueRecvTwo_output
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshRightContinueRecvTwo A strategy hwin two own
      one delivered).2 =
      package.literalCombinedFreshTwoPendingReceiveOutput A strategy hwin
        two.1 two.2.1 own delivered :=
  rfl

/-- The dormant opposite sender is exactly the fresh sender for the current
receive occurrence; no old sender table is accidentally advanced twice. -/
@[simp] theorem literalCombinedFreshRightContinueRecvTwo_dormantSender
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshRightContinueRecvTwo A strategy hwin two own
      one delivered).1.2.1.2.1 =
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
        own one.2.1 delivered).2.1 :=
  rfl

/-- The alternative closed meaning is the fresh simultaneous receiver root,
not a second copy of the live strict receiver. -/
@[simp] theorem literalCombinedFreshRightContinueRecvTwo_closedReceiver
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshRightContinueRecvTwo A strategy hwin two own
      one delivered).1.2.1.2.2.closedControl =
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
        own one.2.1 delivered).2.2.closedControl :=
  rfl

@[simp] theorem literalCombinedFreshRightContinueRecvTwo_payload
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshRightContinueRecvTwo A strategy hwin two own
      one delivered).1.2.2 = none :=
  rfl

/-! ## The exact live-stage branch -/

/-- Activate process one's retained right stage and enter the recurrent
summand.  The selected receiver is determined by the already resolved old
member bit. -/
noncomputable def literalCombinedFreshRightSwitchNoRecvOne
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (input : In₁) :
    OneControl A strategy hwin package × Out₁ :=
  let receiver := package.literalCombinedFreshOneReceiver A strategy hwin
    one.1 one.2.1
  let next := package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
    receiver input
  (.inr next.2, next.1)

/-- Process-two's open receive branch reads the same receiver from the
delivered process-one control and enters its matching recurrent half. -/
noncomputable def literalCombinedFreshRightSwitchRecvTwo
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    TwoControl A strategy hwin package × Out₂ :=
  let receiver := package.literalCombinedFreshOneReceiver A strategy hwin
    one.1 one.2.1
  let sender := two.2.1.2.1
  let next := package.literalRightSeamStagedReversalRecvTwo A strategy hwin
    sender own receiver delivered
  (.inr next.2, next.1)

/-! ## Local phase dispatch -/

/-- A process-one no-receive uses only its stored local phase.  `true` means
that it was the receiver in the preceding left block, so this no-receive is a
right switch and consumes the live stage.  `false` continues the current
blind sender table. -/
noncomputable def literalCombinedFreshPhaseNoRecvOne
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (input : In₁) :
    OneControl A strategy hwin package × Out₁ :=
  if one.2.1.1.2 then
    package.literalCombinedFreshRightSwitchNoRecvOne A strategy hwin one input
  else
    let next := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one input
    (.inl next.1, next.2)

/-- Process two uses its own stored phase for the ordinary/open receive
interpretation.  A previous left-sender phase activates the delivered live
right stage; a previous right-receiver phase keeps the existing pending
receive behavior. -/
noncomputable def literalCombinedFreshPhaseOpenRecvTwo
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    TwoControl A strategy hwin package × Out₂ :=
  if two.2.1.1.2 then
    package.literalCombinedFreshRightSwitchRecvTwo A strategy hwin two own one
      delivered
  else
    let next := package.literalCombinedFreshRightContinueRecvTwo A strategy
      hwin two own one delivered
    (.inl next.1, next.2)

@[simp] theorem literalCombinedFreshPhaseNoRecvOne_of_receiverPhase
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (input : In₁)
    (hphase : one.2.1.1.2 = true) :
    package.literalCombinedFreshPhaseNoRecvOne A strategy hwin one input =
      package.literalCombinedFreshRightSwitchNoRecvOne A strategy hwin one
        input := by
  simp [literalCombinedFreshPhaseNoRecvOne, hphase]

@[simp] theorem literalCombinedFreshPhaseOpenRecvTwo_of_senderPhase
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁)
    (hphase : two.2.1.1.2 = true) :
    package.literalCombinedFreshPhaseOpenRecvTwo A strategy hwin two own one
        delivered =
      package.literalCombinedFreshRightSwitchRecvTwo A strategy hwin two own
        one delivered := by
  simp [literalCombinedFreshPhaseOpenRecvTwo, hphase]

@[simp] theorem literalCombinedFreshPhaseNoRecvOne_of_senderPhase
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (input : In₁)
    (hphase : one.2.1.1.2 = false) :
    package.literalCombinedFreshPhaseNoRecvOne A strategy hwin one input =
      let next := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalCombinedFreshOnePendingStep A strategy hwin) one input
      (.inl next.1, next.2) := by
  simp [literalCombinedFreshPhaseNoRecvOne, hphase]

@[simp] theorem literalCombinedFreshPhaseOpenRecvTwo_of_receiverPhase
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁)
    (hphase : two.2.1.1.2 = false) :
    package.literalCombinedFreshPhaseOpenRecvTwo A strategy hwin two own one
        delivered =
      let next := package.literalCombinedFreshRightContinueRecvTwo A strategy
        hwin two own one delivered
      (.inl next.1, next.2) := by
  simp [literalCombinedFreshPhaseOpenRecvTwo, hphase]

/-! ## Exact same-direction table alignment -/

@[simp] theorem literalCombinedFreshRightContinueNoRecvOne_sender
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (input : In₁) :
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one
      input).1.2.1.2.1 =
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin one.2.1.2.1
        input).2 :=
  rfl

/-- The active left sender at process one and the selected left receiver at
process two are two local presentations of the same table state.  This
relation contains no orientation or leader predicate. -/
def LiteralCombinedFreshRightSameDirectionAligned
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  let sender : LeftSender A strategy hwin package := one.2.1.2.1
  let receiver : LeftReceiver A strategy hwin package :=
    package.literalCombinedFreshTwoReceiver A strategy hwin two.1 two.2.1
  sender.1 = receiver.1 ∧ HEq sender.2 receiver.2.2.1.2.1

/-- One further right round advances the retained sender and exactly the
selected retained receiver, preserving their key and heterogeneous table
control equality.  In particular the receiver's newly produced live stage
remains reachable in the combined control. -/
theorem literalCombinedFreshRightSameDirectionAligned_step
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (haligned :
      package.LiteralCombinedFreshRightSameDirectionAligned A strategy hwin
        one two)
    (input : In₁ × In₂) :
    let oneNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one input.1
    let twoNext := package.literalCombinedFreshRightContinueRecvTwo A strategy
      hwin two input.2 one input.1
    package.LiteralCombinedFreshRightSameDirectionAligned A strategy hwin
      oneNext.1 twoNext.1 := by
  let sender : LeftSender A strategy hwin package := one.2.1.2.1
  let receiver : LeftReceiver A strategy hwin package :=
    package.literalCombinedFreshTwoReceiver A strategy hwin two.1 two.2.1
  have hkey : sender.1 = receiver.1 := haligned.1
  have hsync : HEq sender.2 receiver.2.2.1.2.1 := haligned.2
  have hnext := package.literalLeftSeamStaged_step_controls_eq A strategy hwin
    sender receiver hkey hsync input.2 input.1
  dsimp only
  unfold LiteralCombinedFreshRightSameDirectionAligned
  dsimp only
  rw [package.literalCombinedFreshRightContinueNoRecvOne_sender A strategy
    hwin one input.1]
  rw [package.literalCombinedFreshRightContinueRecvTwo_selectedReceiver A
    strategy hwin two input.2 one input.1]
  constructor
  · change (package.literalLeftSeamStagedSenderNoRecv A strategy hwin sender
      input.1).2.1 =
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin receiver
          input.2 input.1).2.1
    simpa using hkey
  · change HEq (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
      sender input.1).2.2
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin receiver
          input.2 input.1).2.2.2.1.2.1
    exact hnext

/-! ## The dangerous reversal pair is now exact -/

/-- On a live right stage, the two phase-local switch maps are exactly the
two endpoint maps of one checked recurrent transition.  This is the pair test
which the pending-only handler failed at the sum constructor. -/
theorem literalCombinedFreshRightPhaseSwitch_exact_pair
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (stage : RightStage A strategy hwin package)
    (hstage :
      (package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1).2.2.2 = some stage)
    (hphaseOne : one.2.1.1.2 = true)
    (hphaseTwo : two.2.1.1.2 = true)
    (input : In₁ × In₂) :
    let receiver := package.literalCombinedFreshOneReceiver A strategy hwin
      one.1 one.2.1
    let sender : RightSender A strategy hwin package := two.2.1.2.1
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    package.literalCombinedFreshPhaseNoRecvOne A strategy hwin one input.1 =
        (.inr
            (package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
              input.1).1,
          (package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
            input.1).2) ∧
      package.literalCombinedFreshPhaseOpenRecvTwo A strategy hwin two input.2
          one input.1 =
        (.inr
            (package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
              input.2 matched.1 input.1).1,
          (package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
            input.2 matched.1 input.1).2) := by
  dsimp only
  rw [package.literalCombinedFreshPhaseNoRecvOne_of_receiverPhase A strategy
    hwin one input.1 hphaseOne]
  rw [package.literalCombinedFreshPhaseOpenRecvTwo_of_senderPhase A strategy
    hwin two input.2 one input.1 hphaseTwo]
  let receiver := package.literalCombinedFreshOneReceiver A strategy hwin
    one.1 one.2.1
  let sender : RightSender A strategy hwin package := two.2.1.2.1
  have hexact := package.literalRightSeamStagedReversal_exact_pair A strategy
    hwin receiver sender stage hstage input
  change
    ((Sum.inr
        (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
          receiver input.1).2 : OneControl A strategy hwin package),
      (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
        receiver input.1).1) = _ ∧
    ((Sum.inr
        (package.literalRightSeamStagedReversalRecvTwo A strategy hwin sender
          input.2 receiver input.1).2 : TwoControl A strategy hwin package),
      (package.literalRightSeamStagedReversalRecvTwo A strategy hwin sender
        input.2 receiver input.1).1) = _
  constructor
  · rw [hexact.1]
  · rw [hexact.2]

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
