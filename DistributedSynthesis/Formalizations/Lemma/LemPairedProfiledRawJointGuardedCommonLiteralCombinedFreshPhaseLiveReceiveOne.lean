/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseSwitchActivation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRestartedBranchStagedFront

/-!
# Retaining the live right table at a process-one receive

The pending-only handler replaced the complete combined table at every
receive.  That is too early on a homogeneous left block: process two has not
received the fresh key and therefore continues the old right sender table.

This file gives the corrected process-one update.  The ordinary branch keeps
and advances the live right receiver, while the simultaneous branch installs
the fresh closed receiver.  Both branches share the newly prepared dormant
left sender.  At a right-to-left switch the live receiver is initialized from
the key of the delivered process-two sender; on a repeated left round it is
the locally retained receiver.  The distinction uses only process one's
stored local phase and the delivered finite control.

No executable map receives a graph, orientation, hierarchy side, leader bit,
history, or view.
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

private abbrev RightReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev RightSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

/-! ## Selecting the receiver which is physically live -/

/-- The receiver row associated with one resolved table member. -/
def literalCombinedFreshRowOfMember (member : Bool) : PairedEntryRow :=
  if member then .both else .first

@[simp] theorem literalCombinedFreshRowOfMember_false :
    literalCombinedFreshRowOfMember false = .first :=
  rfl

@[simp] theorem literalCombinedFreshRowOfMember_true :
    literalCombinedFreshRowOfMember true = .both :=
  rfl

/-- Every physical strict block starts from the simultaneous checker row of
the preceding common boundary.  The member bit selects a table coordinate;
it does not select the source checker row. -/
def literalCombinedFreshStrictSourceRowOfMember (_member : Bool) :
    PairedEntryRow :=
  .both

@[simp] theorem literalCombinedFreshStrictSourceRowOfMember_eq
    (member : Bool) :
    literalCombinedFreshStrictSourceRowOfMember member = .both :=
  rfl

/-- On a repeated left round process one advances its retained right
receiver.  After a right block it instead initializes the receiver from the
delivered process-two sender key.  The delivered sender is still at its root:
the simultaneous process-two no-receive advances it in the current round. -/
noncomputable def literalCombinedFreshLiveRightReceiverForRecvOne
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) :
    RightReceiver A strategy hwin package :=
  if one.2.1.1.2 then
    package.literalCombinedFreshOneReceiver A strategy hwin one.1 one.2.1
  else
    package.literalRightSeamStagedReceiverInitial A strategy hwin
      two.2.1.2.1.1 (literalCombinedFreshStrictSourceRowOfMember two.1) two.1

@[simp] theorem literalCombinedFreshLiveRightReceiverForRecvOne_same
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = true) :
    package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy hwin
        one two =
      package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1 := by
  simp [literalCombinedFreshLiveRightReceiverForRecvOne, hphase]

@[simp] theorem literalCombinedFreshLiveRightReceiverForRecvOne_switch
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = false) :
    package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy hwin
        one two =
      package.literalRightSeamStagedReceiverInitial A strategy hwin
        two.2.1.2.1.1
          (literalCombinedFreshStrictSourceRowOfMember two.1) two.1 := by
  simp [literalCombinedFreshLiveRightReceiverForRecvOne, hphase]

/-! ## Corrected retained receive -/

/-- Advance the physically live receiver and retain it as the ordinary
continuation.  The closed continuation is the fresh receiver at the current
common child.  Only the dormant left sender is replaced by that fresh key. -/
noncomputable def literalCombinedFreshPhaseLiveRecvOne
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    FiniteDelayedFork (OnePending A strategy hwin package) × Out₁ :=
  let receiver :=
    package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy hwin
      one two
  let advanced :=
    package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
      receiver own delivered
  let fresh := package.literalCombinedFreshOneReceiveFreshness A strategy hwin
    one.2.1 own two.2.1 delivered
  let key := package.literalCombinedFreshOneReceiveKey A strategy hwin
    one.2.1 own two.2.1 delivered
  let dormantLeft := package.literalLeftSeamStagedSenderInitial A strategy hwin
    key
  let closedRight := package.literalRightSeamStagedReceiverInitial A strategy
    hwin key .both true
  let sharedOpen : OneShared A strategy hwin package :=
    (fresh, dormantLeft, ⟨advanced.2, closedRight⟩)
  let sharedClosed : OneShared A strategy hwin package := sharedOpen
  (⟨(false, sharedOpen, none), (true, sharedClosed, none)⟩,
    package.literalRightSeamInternalPhysicalOutput A strategy hwin receiver
      advanced.1)

@[simp] theorem literalCombinedFreshPhaseLiveRecvOne_open_receiver
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
          two delivered).1.openControl.2.1 =
      (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
        (package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy
          hwin one two) own delivered).2 :=
  rfl

@[simp] theorem literalCombinedFreshPhaseLiveRecvOne_closed_receiver
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    package.literalCombinedFreshOneReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
          two delivered).1.closedControl.2.1 =
      package.literalRightSeamStagedReceiverInitial A strategy hwin
        (package.literalCombinedFreshOneReceiveKey A strategy hwin one.2.1 own
          two.2.1 delivered) .both true :=
  rfl

@[simp] theorem literalCombinedFreshPhaseLiveRecvOne_sender
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂)
    (member : Bool) :
    ((package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own two
      delivered).1.candidate member).2.1.2.1 =
      package.literalLeftSeamStagedSenderInitial A strategy hwin
        (package.literalCombinedFreshOneReceiveKey A strategy hwin one.2.1 own
          two.2.1 delivered) := by
  cases member <;> rfl

@[simp] theorem literalCombinedFreshPhaseLiveRecvOne_output
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own two
      delivered).2 =
      package.literalRightSeamInternalPhysicalOutput A strategy hwin
        (package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy
          hwin one two)
        (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
          (package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy
            hwin one two) own delivered).1 :=
  rfl

/-! ## The two table-synchronization laws -/

/-- Synchronization of the executable table controls, without requiring the
true exact-target anchor.  The open literal member legitimately carries the
false anchor; exact-stage liveness is a separate closed-branch invariant. -/
def LiteralRightSeamStagedControlsAligned
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package) : Prop :=
  sender.1 = receiver.1 ∧ HEq sender.2 receiver.2.2.1.2.1

theorem literalRightSeamStagedControls_initial_aligned
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralRightSeamStagedControlsAligned A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalRightSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (package.literalRightSeamStaged_initial_controls_eq A strategy hwin key row
      anchor)

theorem literalRightSeamStagedControls_leftStep_preserves
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package)
    (haligned : package.LiteralRightSeamStagedControlsAligned A strategy hwin
      receiver sender)
    (own : In₁) (delivered : In₂) :
    package.LiteralRightSeamStagedControlsAligned A strategy hwin
      (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
        receiver own delivered).2
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin sender
        delivered).2 := by
  rcases haligned with ⟨hkey, hcontrols⟩
  refine ⟨?_, ?_⟩
  · simpa only [literalRightSeamFrontSenderNoRecv_key,
      literalRightSeamBranchRestartedReceiverRecv_key] using hkey
  · exact package.literalRightSeamStaged_step_controls_eq A strategy hwin
      sender receiver hkey hcontrols own delivered

/-- A repeated left round preserves the old right table exactly. -/
theorem literalCombinedFreshPhaseLiveRecvOne_same_preserves
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = true)
    (haligned : package.LiteralRightSeamStagedControlsAligned A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1) two.2.1.2.1)
    (input : In₁ × In₂) :
    package.LiteralRightSeamStagedControlsAligned A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 input.2).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A strategy
    hwin one two hphase]
  exact package.literalRightSeamStagedControls_leftStep_preserves A strategy
    hwin _ _
    haligned input.1 input.2

/-- On a right-to-left switch, the delivered dormant right sender and the
newly initialized receiver execute one synchronized first table record. -/
theorem literalCombinedFreshPhaseLiveRecvOne_switch_preserves
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = false)
    (hroot : two.2.1.2.1 =
      package.literalRightSeamStagedSenderInitial A strategy hwin
        two.2.1.2.1.1)
    (input : In₁ × In₂) :
    package.LiteralRightSeamStagedControlsAligned A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 input.2).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A
    strategy hwin one two hphase]
  rw [hroot]
  apply package.literalRightSeamStagedControls_leftStep_preserves A strategy
    hwin
  exact package.literalRightSeamStagedControls_initial_aligned A strategy hwin
    two.2.1.2.1.1 (literalCombinedFreshStrictSourceRowOfMember two.1) two.1

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
