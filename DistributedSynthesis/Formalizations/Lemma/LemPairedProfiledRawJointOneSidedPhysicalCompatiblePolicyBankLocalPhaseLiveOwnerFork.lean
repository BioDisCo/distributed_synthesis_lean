/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLive

/-!
# Owner-split phase-live fail-fast carrier

The receiver fork alone is insufficient for the current matched-prefix
invariant.  At a reversal boundary, the strict-open history retains the old
opposite owner, whereas the simultaneous-closed history retains that owner
after its local step.  This file stores those two semantic owners dormantly,
in parallel with the old/new receiver fork.  A separate driver supplies the
member-independent blind output.

This is a local finite-state test, not yet a recurrent correctness theorem.
After a blind suffix, the selected semantic owner has remained dormant while
the driver has advanced.  A later proof must relate those states using the
occurrence-linked table, or replace this carrier by an equivalent common
control with a proved readback map.
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

/-! ## Process-one owner-split state -/

/-- The first coordinate is the executable blind driver.  The two forks are
semantic payloads and remain dormant during a blind suffix. -/
abbrev ProfiledRawJointRecurrentRightToLeftOwnerSplitShared :=
  ProfiledRawJointRightPhysicalSiblingExceptional A ×
    (FiniteDelayedFork (ProfiledRawJointRightPhysicalSiblingExceptional A) ×
      FiniteDelayedFork
        (ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin))

abbrev ProfiledRawJointRecurrentRightToLeftOwnerSplitPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentRightToLeftOwnerSplitShared A strategy hwin) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftOwnerSplitShared A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentRightToLeftOwnerSplitOwner
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin) :
    ProfiledRawJointRightPhysicalSiblingExceptional A :=
  if control.1 then control.2.1.2.1.closedControl
  else control.2.1.2.1.openControl

noncomputable def profiledRawJointRecurrentRightToLeftOwnerSplitReceiver
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin) :
    ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
  if control.1 then control.2.1.2.2.closedControl
  else control.2.1.2.2.openControl

/-- Actual right-to-left packet boundary with separate executable and semantic
owner states. -/
noncomputable def
    profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin) ×
      Out₁ :=
  let advancedReceiver :=
    profiledRawJointRecurrentRightToLeftAdvanceOldReceiver A strategy hwin
      oldState oldReceiver oldOwner input
  let senderNext := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    sender.1 false sender.2 input.1
  let advancedSender : ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨sender.1, senderNext.2⟩
  let newMove :=
    profiledRawJointRecurrentRightToLeftMove A strategy hwin packet oldReceiver
  let shared :
      ProfiledRawJointRecurrentRightToLeftOwnerSplitShared A strategy hwin :=
    (advancedSender,
      (⟨sender, advancedSender⟩,
        ⟨advancedReceiver.1,
          (packet.successor,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A newMove
              .both)⟩))
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork shared (),
    advancedReceiver.2)

@[simp] theorem
    profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork_open_owner
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentRightToLeftOwnerSplitOwner A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.openControl = sender :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork_closed_owner
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentRightToLeftOwnerSplitOwner A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.closedControl =
      ⟨sender.1,
        (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A sender.1 false
          sender.2 input.1).2⟩ :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork_open_receiver
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentRightToLeftOwnerSplitReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.openControl =
      (oldState,
        (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A oldReceiver.1
          oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).2) :=
  rfl

theorem
    profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork_closed_receiver
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.2 = some move) :
    profiledRawJointRecurrentRightToLeftOwnerSplitReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.closedControl =
      (packet.successor,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both) := by
  simp [profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork,
    profiledRawJointRecurrentRightToLeftOwnerSplitReceiver,
    profiledRawJointRecurrentRightToLeftMove, hmove]

noncomputable def profiledRawJointRecurrentRightToLeftOwnerSplitStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentRightToLeftOwnerSplitShared A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerSplitShared A strategy hwin ×
      Out₁ :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    shared.1.1 false shared.1.2 input
  ((⟨shared.1.1, next.2⟩, shared.2), next.1)

theorem profiledRawJointRecurrentRightToLeftOwnerSplitStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentRightToLeftOwnerSplitStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentRightToLeftOwnerSplitNoRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin ×
      Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentRightToLeftOwnerSplitStep A strategy hwin)
      control input

theorem profiledRawJointRecurrentRightToLeftOwnerSplitFork_blind
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet
          input).1.openControl
      (profiledRawJointRecurrentRightToLeftOwnerSplitPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet
          input).1.closedControl := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

@[simp] theorem profiledRawJointRecurrentRightToLeftOwnerSplitNoRecv_owner
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin)
    (input : In₁) :
    profiledRawJointRecurrentRightToLeftOwnerSplitOwner A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerSplitNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentRightToLeftOwnerSplitOwner A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

@[simp] theorem profiledRawJointRecurrentRightToLeftOwnerSplitNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerSplitPending A strategy hwin)
    (input : In₁) :
    profiledRawJointRecurrentRightToLeftOwnerSplitReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerSplitNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentRightToLeftOwnerSplitReceiver A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

/-! ## Process-two mirror -/

abbrev ProfiledRawJointRecurrentLeftToRightOwnerSplitShared :=
  ProfiledRawJointLeftPhysicalSiblingExceptional A ×
    (FiniteDelayedFork (ProfiledRawJointLeftPhysicalSiblingExceptional A) ×
      FiniteDelayedFork
        (ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin))

abbrev ProfiledRawJointRecurrentLeftToRightOwnerSplitPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentLeftToRightOwnerSplitShared A strategy hwin) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightOwnerSplitShared A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentLeftToRightOwnerSplitOwner
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin) :
    ProfiledRawJointLeftPhysicalSiblingExceptional A :=
  if control.1 then control.2.1.2.1.closedControl
  else control.2.1.2.1.openControl

noncomputable def profiledRawJointRecurrentLeftToRightOwnerSplitReceiver
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin) :
    ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
  if control.1 then control.2.1.2.2.closedControl
  else control.2.1.2.2.openControl

noncomputable def
    profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin) ×
      Out₂ :=
  let advancedReceiver :=
    profiledRawJointRecurrentLeftToRightAdvanceOldReceiver A strategy hwin
      oldState oldReceiver oldOwner input
  let senderNext := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    sender.1 false sender.2 input.1
  let advancedSender : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨sender.1, senderNext.2⟩
  let newMove :=
    profiledRawJointRecurrentLeftToRightMove A strategy hwin packet oldReceiver
  let shared :
      ProfiledRawJointRecurrentLeftToRightOwnerSplitShared A strategy hwin :=
    (advancedSender,
      (⟨sender, advancedSender⟩,
        ⟨advancedReceiver.1,
          (packet.successor,
            initialProfiledRawJointRightPhysicalSiblingReceiver A newMove
              .both)⟩))
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork shared (),
    advancedReceiver.2)

@[simp] theorem
    profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork_open_owner
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    profiledRawJointRecurrentLeftToRightOwnerSplitOwner A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.openControl = sender :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork_closed_owner
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    profiledRawJointRecurrentLeftToRightOwnerSplitOwner A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.closedControl =
      ⟨sender.1,
        (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A sender.1 false
          sender.2 input.1).2⟩ :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork_open_receiver
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    profiledRawJointRecurrentLeftToRightOwnerSplitReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.openControl =
      (oldState,
        (stepProfiledRawJointRightPhysicalSiblingReceiverFor A oldReceiver.1
          oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).2) :=
  rfl

theorem
    profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork_closed_receiver
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.2.1 = some move) :
    profiledRawJointRecurrentLeftToRightOwnerSplitReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet
            input).1.closedControl =
      (packet.successor,
        initialProfiledRawJointRightPhysicalSiblingReceiver A move .both) := by
  simp [profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork,
    profiledRawJointRecurrentLeftToRightOwnerSplitReceiver,
    profiledRawJointRecurrentLeftToRightMove, hmove]

noncomputable def profiledRawJointRecurrentLeftToRightOwnerSplitStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentLeftToRightOwnerSplitShared A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerSplitShared A strategy hwin ×
      Out₂ :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    shared.1.1 false shared.1.2 input
  ((⟨shared.1.1, next.2⟩, shared.2), next.1)

theorem profiledRawJointRecurrentLeftToRightOwnerSplitStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentLeftToRightOwnerSplitStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentLeftToRightOwnerSplitNoRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin ×
      Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentLeftToRightOwnerSplitStep A strategy hwin)
      control input

theorem profiledRawJointRecurrentLeftToRightOwnerSplitFork_blind
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet
          input).1.openControl
      (profiledRawJointRecurrentLeftToRightOwnerSplitPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet
          input).1.closedControl := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

@[simp] theorem profiledRawJointRecurrentLeftToRightOwnerSplitNoRecv_owner
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin)
    (input : In₂) :
    profiledRawJointRecurrentLeftToRightOwnerSplitOwner A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerSplitNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentLeftToRightOwnerSplitOwner A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

@[simp] theorem profiledRawJointRecurrentLeftToRightOwnerSplitNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerSplitPending A strategy hwin)
    (input : In₂) :
    profiledRawJointRecurrentLeftToRightOwnerSplitReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerSplitNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentLeftToRightOwnerSplitReceiver A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

end

end DetParityAutomaton

end DistributedSynthesis
