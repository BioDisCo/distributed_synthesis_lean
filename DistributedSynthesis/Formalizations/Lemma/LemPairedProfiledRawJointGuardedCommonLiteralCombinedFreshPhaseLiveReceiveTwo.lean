/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveReceiveOne

/-!
# Retaining the live left table at a process-two receive

This is the exact process-two mirror of the live process-one receive carrier.
On a repeated right round, process two advances its locally retained left
receiver.  On a left-to-right switch, it initializes that receiver from the
dormant left sender delivered by process one and advances the synchronized
pair once.  The open continuation retains the advanced live receiver; the
closed continuation stores the fresh `.both,true` receiver.  Only the dormant
right sender is replaced at the new key.

The phase test is process two's own finite Boolean.  No executable map
receives a graph, orientation, hierarchy side, leader bit, history, or view.
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

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
    hwin package

/-! ## Selecting the physically live receiver -/

/-- On a repeated right round (`false` phase), use the retained receiver.
After a left block (`true` phase), initialize from process one's delivered
dormant left sender. -/
noncomputable def literalCombinedFreshLiveLeftReceiverForRecvTwo
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package) :
    LeftReceiver A strategy hwin package :=
  if two.2.1.1.2 then
    package.literalLeftSeamStagedReceiverInitial A strategy hwin
      one.2.1.2.1.1 (literalCombinedFreshStrictSourceRowOfMember one.1) one.1
  else
    package.literalCombinedFreshTwoReceiver A strategy hwin two.1 two.2.1

@[simp] theorem literalCombinedFreshLiveLeftReceiverForRecvTwo_same
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = false) :
    package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy hwin
        two one =
      package.literalCombinedFreshTwoReceiver A strategy hwin two.1
        two.2.1 := by
  simp [literalCombinedFreshLiveLeftReceiverForRecvTwo, hphase]

@[simp] theorem literalCombinedFreshLiveLeftReceiverForRecvTwo_switch
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = true) :
    package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy hwin
        two one =
      package.literalLeftSeamStagedReceiverInitial A strategy hwin
        one.2.1.2.1.1
          (literalCombinedFreshStrictSourceRowOfMember one.1) one.1 := by
  simp [literalCombinedFreshLiveLeftReceiverForRecvTwo, hphase]

/-! ## Corrected retained receive -/

/-- Select the physical process-two coordinate of one advanced heterogeneous
receiver output. -/
noncomputable def literalCombinedFreshTwoSelectedPhysicalOutput
    (package : Package A strategy hwin (initial := initial))
    (member : Bool)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package) : Out₂ :=
  if member then
    profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.2
  else
    profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.1

/-- Advance the physically live left receiver.  Both returned candidates
share the new freshness state and dormant right sender; only their member bit
selects the advanced open receiver or the fresh simultaneous receiver. -/
noncomputable def literalCombinedFreshPhaseLiveRecvTwo
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    FiniteDelayedFork (TwoPending A strategy hwin package) × Out₂ :=
  let receiver :=
    package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy hwin
      two one
  let advanced :=
    package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
      receiver own delivered
  let freshShared := package.literalCombinedFreshTwoReceiveShared A strategy
    hwin two.2.1 own one.2.1 delivered
  let shared : TwoShared A strategy hwin package :=
    (freshShared.1, freshShared.2.1,
      ⟨advanced.2, freshShared.2.2.closedControl⟩)
  (⟨(false, shared, none), (true, shared, none)⟩,
    package.literalLeftSeamInternalPhysicalOutput A strategy hwin receiver
      advanced.1)

@[simp] theorem literalCombinedFreshPhaseLiveRecvTwo_open_receiver
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
          one delivered).1.openControl.2.1 =
      (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
        (package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy
          hwin two one) own delivered).2 :=
  rfl

@[simp] theorem literalCombinedFreshPhaseLiveRecvTwo_closed_receiver
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    package.literalCombinedFreshTwoReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
          one delivered).1.closedControl.2.1 =
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
        own one.2.1 delivered).2.2.closedControl :=
  rfl

@[simp] theorem literalCombinedFreshPhaseLiveRecvTwo_sender
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁)
    (member : Bool) :
    ((package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own one
      delivered).1.candidate member).2.1.2.1 =
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
        own one.2.1 delivered).2.1 := by
  cases member <;> rfl

@[simp] theorem literalCombinedFreshPhaseLiveRecvTwo_output
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own one
      delivered).2 =
      package.literalLeftSeamInternalPhysicalOutput A strategy hwin
        (package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy
          hwin two one)
        (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
          (package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy
            hwin two one) own delivered).1 :=
  rfl

/-! ## Weak table synchronization -/

/-- The left seam's sender and receiver carry the same key and executable
table control.  Exact-stage liveness is deliberately a separate invariant. -/
def LiteralLeftSeamStagedControlsAligned
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package) : Prop :=
  sender.1 = receiver.1 ∧ HEq sender.2 receiver.2.2.1.2.1

theorem literalLeftSeamStagedControls_initial_aligned
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralLeftSeamStagedControlsAligned A strategy hwin
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (package.literalLeftSeamStaged_initial_controls_eq A strategy hwin key row
      anchor)

theorem literalLeftSeamStagedControls_rightStep_preserves
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package)
    (haligned : package.LiteralLeftSeamStagedControlsAligned A strategy hwin
      receiver sender)
    (own : In₂) (delivered : In₁) :
    package.LiteralLeftSeamStagedControlsAligned A strategy hwin
      (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
        receiver own delivered).2
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin sender
        delivered).2 := by
  rcases haligned with ⟨hkey, hcontrols⟩
  refine ⟨?_, ?_⟩
  · simpa only [literalLeftSeamFrontSenderNoRecv_key,
      literalLeftSeamBranchRestartedReceiverRecv_key] using hkey
  · exact package.literalLeftSeamStaged_step_controls_eq A strategy hwin
      sender receiver hkey hcontrols own delivered

/-- A repeated right round preserves the live old left table exactly. -/
theorem literalCombinedFreshPhaseLiveRecvTwo_same_preserves
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = false)
    (haligned : package.LiteralLeftSeamStagedControlsAligned A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
        two.2.1) one.2.1.2.1)
    (input : In₁ × In₂) :
    package.LiteralLeftSeamStagedControlsAligned A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 input.1).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_same A strategy
    hwin two one hphase]
  exact package.literalLeftSeamStagedControls_rightStep_preserves A strategy
    hwin _ _ haligned input.2 input.1

/-- At a left-to-right switch, the delivered dormant left sender and the
newly initialized receiver execute one synchronized first table record. -/
theorem literalCombinedFreshPhaseLiveRecvTwo_switch_preserves
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = true)
    (hroot : one.2.1.2.1 =
      package.literalLeftSeamStagedSenderInitial A strategy hwin
        one.2.1.2.1.1)
    (input : In₁ × In₂) :
    package.LiteralLeftSeamStagedControlsAligned A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 input.1).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_switch A
    strategy hwin two one hphase]
  rw [hroot]
  apply package.literalLeftSeamStagedControls_rightStep_preserves A strategy
    hwin
  exact package.literalLeftSeamStagedControls_initial_aligned A strategy hwin
    one.2.1.2.1.1 (literalCombinedFreshStrictSourceRowOfMember one.1) one.1

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
