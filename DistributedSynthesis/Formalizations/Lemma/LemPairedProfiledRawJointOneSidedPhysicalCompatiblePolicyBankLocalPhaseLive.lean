/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalControllerTracked

/-!
# Bank-linked phase-live receiver forks

At an orientation reversal, the strict branch contains the old receiver after
processing the boundary input, whereas the simultaneous branch contains a
fresh receiver at the newly resolved bank successor.  The unresolved endpoint
must retain both branches.  It executes neither receiver during a blind
suffix; it executes one member-independent sender and keeps the receiver fork
dormant until a later delivery selects its member.

This file defines that finite payload and proves its purely local laws.  The
next seam theorem must construct the `old` argument by the actual boundary
receiver step and the `fresh` argument from the exact resolved successor.
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

abbrev ProfiledRawJointRecurrentBankedLeftReceiver :=
  BankControl A strategy hwin ×
    ProfiledRawJointLeftPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentBankedRightReceiver :=
  BankControl A strategy hwin ×
    ProfiledRawJointRightPhysicalSiblingReceiver A

/-! ## Right-to-left pending endpoint -/

/-- Process one's blind sender and dormant strict/simultaneous left-receiver
fork. -/
abbrev ProfiledRawJointRecurrentRightToLeftPhaseLiveShared :=
  ProfiledRawJointRightPhysicalSiblingExceptional A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)

abbrev ProfiledRawJointRecurrentRightToLeftPhaseLivePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentRightToLeftPhaseLiveShared A strategy hwin)
    Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftPhaseLiveShared A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin) := by
  classical
  infer_instance

/-- Build the exact dormant receiver fork.  `oldAdvanced` is already past the
boundary input; the closed branch is fresh at the new bank successor. -/
noncomputable def profiledRawJointRecurrentRightToLeftPhaseLiveShared
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentRightToLeftPhaseLiveShared A strategy hwin :=
  (sender,
    ⟨oldAdvanced,
      (newState,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A newMove .both)⟩)

noncomputable def profiledRawJointRecurrentRightToLeftPhaseLivePendingFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointRecurrentRightToLeftPhaseLiveShared A strategy hwin sender
      oldAdvanced newState newMove) ()

/-- A later delivery selects the already-advanced strict receiver or the fresh
simultaneous receiver. -/
noncomputable def profiledRawJointRecurrentRightToLeftPhaseLiveReceiver
    (control :
      ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin) :
    ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

@[simp] theorem
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver_open
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftPhaseLivePendingFork A strategy
          hwin sender oldAdvanced newState newMove).openControl =
      oldAdvanced :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver_closed
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftPhaseLivePendingFork A strategy
          hwin sender oldAdvanced newState newMove).closedControl =
      (newState,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A newMove .both) :=
  rfl

/-! ### The actual bank-packet seam -/

/-- Advance the old left receiver on the boundary input, retaining the bank
state in which that receiver was installed.  This is the open continuation
of an actual right-to-left reversal. -/
noncomputable def
    profiledRawJointRecurrentRightToLeftAdvanceOldReceiver
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin × Out₁ :=
  let next := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A
    oldReceiver.1 oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input
  ((oldState, next.2), next.1)

/-- Construct the phase-live fork from the finite packet delivered by the
informed endpoint.  The open receiver is the old receiver after its genuine
boundary step.  The closed receiver is fresh at the packet successor.  The
opposite right owner is also advanced on its local input: its output is not
used at a simultaneous boundary, but this state update is necessary for that
owner to remain prefix-aligned with the advanced dormant right receiver.
The `getD` branch only totalizes malformed packets; legal packets eliminate it
by the `closed_of_move` theorem below. -/
noncomputable def
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy
          hwin) ×
      Out₁ :=
  let advanced :=
    profiledRawJointRecurrentRightToLeftAdvanceOldReceiver A strategy hwin
      oldState oldReceiver oldOwner input
  let senderNext := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    sender.1 false sender.2 input.1
  let newMove :=
    profiledRawJointRecurrentRightToLeftMove A strategy hwin packet oldReceiver
  (profiledRawJointRecurrentRightToLeftPhaseLivePendingFork A strategy hwin
      ⟨sender.1, senderNext.2⟩ advanced.1 packet.successor newMove,
    advanced.2)

/-- The open member contains exactly the receiver step performed at this
boundary, including its old bank coordinate. -/
@[simp] theorem
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork_open
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
        (FiniteDelayedFork.openControl
          (profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A
            strategy hwin sender oldState oldReceiver oldOwner packet
              input).1) =
      (oldState,
        (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A oldReceiver.1
          oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).2) :=
  rfl

/-- A legal packet installs the exact left move carried by its successor;
the closed member is the fresh simultaneous receiver at that successor. -/
theorem
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork_closed_of_move
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
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
        (FiniteDelayedFork.closedControl
          (profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A
            strategy hwin sender oldState oldReceiver oldOwner packet
              input).1) =
      (packet.successor,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both) := by
  simp [profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
    profiledRawJointRecurrentRightToLeftMove, hmove]

/-- The boundary output is produced by the same old receiver step retained in
the open member. -/
@[simp] theorem
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork_output
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    (profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A
      strategy hwin sender oldState oldReceiver oldOwner packet input).2 =
      (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A oldReceiver.1
        oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).1 :=
  rfl

/-- Both unresolved members carry the right owner after its local step.  This
is the correct owner state for the simultaneous member; the later strict-open
closure audit must separately account for the old-owner alternative. -/
@[simp] theorem
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork_senders
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    let fork :=
      (profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    fork.openControl.2.1.1 =
        ⟨sender.1,
          (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A sender.1
            false sender.2 input.1).2⟩ ∧
      fork.closedControl.2.1.1 =
        ⟨sender.1,
          (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A sender.1
            false sender.2 input.1).2⟩ :=
  ⟨rfl, rfl⟩

/-- The actual old/new packet seam creates a blind-related local fork even
when the old and successor bank coordinates differ. -/
theorem
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork_blind
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (FiniteDelayedFork.openControl
        (profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input).1)
      (FiniteDelayedFork.closedControl
        (profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input).1) := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

/-- Blind evolution advances only the shared old sender. -/
noncomputable def profiledRawJointRecurrentRightToLeftPhaseLiveStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentRightToLeftPhaseLiveShared A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftPhaseLiveShared A strategy hwin ×
      Out₁ :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    shared.1.1 false shared.1.2 input
  ((⟨shared.1.1, next.2⟩, shared.2), next.1)

theorem profiledRawJointRecurrentRightToLeftPhaseLiveStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentRightToLeftPhaseLiveStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin ×
      Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentRightToLeftPhaseLiveStep A strategy hwin)
      control input

theorem profiledRawJointRecurrentRightToLeftPhaseLive_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin)
    (input : In₁)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin
          right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin
          left input).1
        (profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin
          right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentRightToLeftPhaseLiveStep A strategy hwin)
    (profiledRawJointRecurrentRightToLeftPhaseLiveStep_laws A strategy hwin)
    left right input hblind

@[simp] theorem
    profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin)
    (input : In₁) :
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

/-! ## Left-to-right mirror -/

abbrev ProfiledRawJointRecurrentLeftToRightPhaseLiveShared :=
  ProfiledRawJointLeftPhysicalSiblingExceptional A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)

abbrev ProfiledRawJointRecurrentLeftToRightPhaseLivePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentLeftToRightPhaseLiveShared A strategy hwin)
    Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightPhaseLiveShared A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentLeftToRightPhaseLiveShared
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentLeftToRightPhaseLiveShared A strategy hwin :=
  (sender,
    ⟨oldAdvanced,
      (newState,
        initialProfiledRawJointRightPhysicalSiblingReceiver A newMove .both)⟩)

noncomputable def profiledRawJointRecurrentLeftToRightPhaseLivePendingFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointRecurrentLeftToRightPhaseLiveShared A strategy hwin sender
      oldAdvanced newState newMove) ()

noncomputable def profiledRawJointRecurrentLeftToRightPhaseLiveReceiver
    (control :
      ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin) :
    ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

@[simp] theorem profiledRawJointRecurrentLeftToRightPhaseLiveReceiver_open
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightPhaseLivePendingFork A strategy
          hwin sender oldAdvanced newState newMove).openControl =
      oldAdvanced :=
  rfl

@[simp] theorem profiledRawJointRecurrentLeftToRightPhaseLiveReceiver_closed
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (newState : BankControl A strategy hwin)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightPhaseLivePendingFork A strategy
          hwin sender oldAdvanced newState newMove).closedControl =
      (newState,
        initialProfiledRawJointRightPhysicalSiblingReceiver A newMove .both) :=
  rfl

/-! ### Mirrored bank-packet seam -/

noncomputable def
    profiledRawJointRecurrentLeftToRightAdvanceOldReceiver
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin × Out₂ :=
  let next := stepProfiledRawJointRightPhysicalSiblingReceiverFor A
    oldReceiver.1 oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input
  ((oldState, next.2), next.1)

noncomputable def
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy
          hwin) ×
      Out₂ :=
  let advanced :=
    profiledRawJointRecurrentLeftToRightAdvanceOldReceiver A strategy hwin
      oldState oldReceiver oldOwner input
  let senderNext := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    sender.1 false sender.2 input.1
  let newMove :=
    profiledRawJointRecurrentLeftToRightMove A strategy hwin packet oldReceiver
  (profiledRawJointRecurrentLeftToRightPhaseLivePendingFork A strategy hwin
      ⟨sender.1, senderNext.2⟩ advanced.1 packet.successor newMove,
    advanced.2)

@[simp] theorem
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork_open
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
        (FiniteDelayedFork.openControl
          (profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A
            strategy hwin sender oldState oldReceiver oldOwner packet
              input).1) =
      (oldState,
        (stepProfiledRawJointRightPhysicalSiblingReceiverFor A oldReceiver.1
          oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).2) :=
  rfl

theorem
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork_closed_of_move
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
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
        (FiniteDelayedFork.closedControl
          (profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A
            strategy hwin sender oldState oldReceiver oldOwner packet
              input).1) =
      (packet.successor,
        initialProfiledRawJointRightPhysicalSiblingReceiver A move .both) := by
  simp [profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
    profiledRawJointRecurrentLeftToRightMove, hmove]

@[simp] theorem
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork_output
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    (profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A
      strategy hwin sender oldState oldReceiver oldOwner packet input).2 =
      (stepProfiledRawJointRightPhysicalSiblingReceiverFor A oldReceiver.1
        oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).1 :=
  rfl

/-- Mirrored exact shared-owner state in the two unresolved members. -/
@[simp] theorem
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork_senders
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    let fork :=
      (profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    fork.openControl.2.1.1 =
        ⟨sender.1,
          (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A sender.1
            false sender.2 input.1).2⟩ ∧
      fork.closedControl.2.1.1 =
        ⟨sender.1,
          (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A sender.1
            false sender.2 input.1).2⟩ :=
  ⟨rfl, rfl⟩

theorem
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork_blind
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (FiniteDelayedFork.openControl
        (profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input).1)
      (FiniteDelayedFork.closedControl
        (profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input).1) := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

noncomputable def profiledRawJointRecurrentLeftToRightPhaseLiveStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentLeftToRightPhaseLiveShared A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightPhaseLiveShared A strategy hwin ×
      Out₂ :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    shared.1.1 false shared.1.2 input
  ((⟨shared.1.1, next.2⟩, shared.2), next.1)

theorem profiledRawJointRecurrentLeftToRightPhaseLiveStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentLeftToRightPhaseLiveStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin ×
      Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentLeftToRightPhaseLiveStep A strategy hwin)
      control input

theorem profiledRawJointRecurrentLeftToRightPhaseLive_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin)
    (input : In₂)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin
          right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin
          left input).1
        (profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin
          right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentLeftToRightPhaseLiveStep A strategy hwin)
    (profiledRawJointRecurrentLeftToRightPhaseLiveStep_laws A strategy hwin)
    left right input hblind

@[simp] theorem profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin)
    (input : In₂) :
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

/-! ## Reachable boundary specialization

The preceding packet seams are total finite maps.  We now connect them to
the matched-prefix invariant of the recurrent bank.  This removes the last
provisional input in the seam: at every reachable boundary the packet really
contains the physical move needed by its fresh closed receiver.
-/

/-- Use the target emitted by an aligned right block, the current right
sender, and the retained old left receiver to form the actual process-one
phase-live receive fork.  The separate `oldState` is the dormant receiver's
bank coordinate, which need not equal the current right-bank coordinate. -/
noncomputable def ProfiledRawJointRecurrentRightBoundaryData.phaseLiveReceive
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy
          hwin) ×
      Out₁ :=
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin data.1 (data.target A strategy hwin input)
  profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A strategy
    hwin
      ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
      oldState data.2.2 oldOwner packet input

/-- The right matched-prefix invariant proves that the newly resolved packet
contains an actual left physical move. -/
theorem ProfiledRawJointRecurrentRightBoundaryInvariant.phaseLive_move_exists
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin data.1 (data.target A strategy hwin input)
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.2.2 = some move := by
  dsimp only
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy hwin
      data hinvariant) input
  have hrealizes' :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin data.1 (data.target A strategy hwin input)
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin data.1 (data.target A strategy hwin input)) := by
    simpa only [ProfiledRawJointRecurrentRightBoundaryData.target] using
      hrealizes
  have hroot' :
      profiledRawJointOneSidedCurrentSlots A .left
        (data.target A strategy hwin input) () = some root := by
    simpa only [ProfiledRawJointRecurrentRightBoundaryData.target] using hroot
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin data.1 (data.target A strategy hwin input) hrealizes'
        root hroot'

/-- Consequently the closed member of the reachable right-to-left seam is
fresh at the exact bank successor, while the open member has already taken
the old receiver step by construction. -/
theorem ProfiledRawJointRecurrentRightBoundaryInvariant.phaseLive_closed
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin data.1 (data.target A strategy hwin input)
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
          (FiniteDelayedFork.closedControl
            (data.phaseLiveReceive A strategy hwin oldState oldOwner input).1) =
        (packet.successor,
          initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    hinvariant.phaseLive_move_exists A strategy hwin data input
  refine ⟨move, ?_⟩
  exact
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork_closed_of_move
      A strategy hwin
        ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
        oldState data.2.2 oldOwner _ input move hmove

/-- Reachability is not needed for the blind law: the two candidates share
their sender and the complete old/new receiver fork definitionally. -/
theorem ProfiledRawJointRecurrentRightBoundaryData.phaseLive_blind
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (FiniteDelayedFork.openControl
        (data.phaseLiveReceive A strategy hwin oldState oldOwner input).1)
      (FiniteDelayedFork.closedControl
        (data.phaseLiveReceive A strategy hwin oldState oldOwner input).1) := by
  apply
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork_blind A
      strategy hwin

/-- Mirrored specialization for an aligned left block. -/
noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.phaseLiveReceive
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy
          hwin) ×
      Out₂ :=
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin data.1 (data.target A strategy hwin input)
  profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A strategy
    hwin
      ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
      oldState data.2.2 oldOwner packet (input.2, input.1)

theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.phaseLive_move_exists
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin data.1 (data.target A strategy hwin input)
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.2.1 = some move := by
  dsimp only
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy hwin data
      hinvariant) input
  have hrealizes' :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin data.1 (data.target A strategy hwin input)
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin data.1 (data.target A strategy hwin input)) := by
    simpa only [ProfiledRawJointRecurrentLeftBoundaryData.target] using
      hrealizes
  have hroot' :
      profiledRawJointOneSidedCurrentSlots A .right
        (data.target A strategy hwin input) () = some root := by
    simpa only [ProfiledRawJointRecurrentLeftBoundaryData.target] using hroot
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin data.1 (data.target A strategy hwin input) hrealizes'
        root hroot'

theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.phaseLive_closed
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin data.1 (data.target A strategy hwin input)
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
          (FiniteDelayedFork.closedControl
            (data.phaseLiveReceive A strategy hwin oldState oldOwner input).1) =
        (packet.successor,
          initialProfiledRawJointRightPhysicalSiblingReceiver A move .both) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    hinvariant.phaseLive_move_exists A strategy hwin data input
  refine ⟨move, ?_⟩
  exact
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork_closed_of_move
      A strategy hwin
        ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
        oldState data.2.2 oldOwner _ (input.2, input.1) move hmove

theorem ProfiledRawJointRecurrentLeftBoundaryData.phaseLive_blind
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (FiniteDelayedFork.openControl
        (data.phaseLiveReceive A strategy hwin oldState oldOwner input).1)
      (FiniteDelayedFork.closedControl
        (data.phaseLiveReceive A strategy hwin oldState oldOwner input).1) := by
  apply
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork_blind A
      strategy hwin

end

end DetParityAutomaton

end DistributedSynthesis
