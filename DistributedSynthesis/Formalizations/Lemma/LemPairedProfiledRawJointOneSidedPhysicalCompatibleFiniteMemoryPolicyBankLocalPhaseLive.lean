/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalBoundary
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLive

/-!
# Phase-live forks for a recurrent bank with finite policy memory

A direct reversal leaves the uninformed endpoint with two candidates.  The
strict candidate retains the old bank lineage after advancing its receiver;
the simultaneous candidate installs a fresh receiver at the resolved bank
successor.  These lineages can have different policy memories.  This file
stores each memory in its own bank coordinate and proves that the delayed
fork copies and preserves those coordinates exactly.

Only the bank state and packet type change from the unit-memory construction.
The physical receiver and blind-output arguments are unchanged.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

private abbrev Packet :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
    (Memory := Memory) A strategy

abbrev ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver :=
  BankControl (Memory := Memory) A strategy ×
    ProfiledRawJointLeftPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver :=
  BankControl (Memory := Memory) A strategy ×
    ProfiledRawJointRightPhysicalSiblingReceiver A

/-! ## Right-to-left fork -/

abbrev ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLiveShared :=
  ProfiledRawJointRightPhysicalSiblingExceptional A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)

abbrev ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLiveShared
      (Memory := Memory) A strategy) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLiveShared
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentFiniteMemoryRightToLeftShared
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLiveShared
      (Memory := Memory) A strategy :=
  (sender,
    ⟨oldAdvanced,
      (newState,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A newMove .both)⟩)

noncomputable def profiledRawJointRecurrentFiniteMemoryRightToLeftPendingFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
        (Memory := Memory) A strategy) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointRecurrentFiniteMemoryRightToLeftShared
      (Memory := Memory) A strategy sender oldAdvanced newState newMove) ()

noncomputable def profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
        (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
      (Memory := Memory) A strategy :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver_open
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryRightToLeftPendingFork
          (Memory := Memory) A strategy sender oldAdvanced newState
            newMove).openControl =
      oldAdvanced :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver_closed
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryRightToLeftPendingFork
          (Memory := Memory) A strategy sender oldAdvanced newState
            newMove).closedControl =
      (newState,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A newMove .both) :=
  rfl

noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftAdvanceOldReceiver
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy × Out₁ :=
  let next := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A
    oldReceiver.1 oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input
  ((oldState, next.2), next.1)

noncomputable def profiledRawJointRecurrentFiniteMemoryRightToLeftMove
    (packet : Packet (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointLeftPhysicalSiblingMove A :=
  packet.successor.2.1.1.2.2.getD oldReceiver.1

noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
          (Memory := Memory) A strategy) × Out₁ :=
  let advanced :=
    profiledRawJointRecurrentFiniteMemoryRightToLeftAdvanceOldReceiver
      (Memory := Memory) A strategy oldState oldReceiver oldOwner input
  let senderNext := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    sender.1 false sender.2 input.1
  let newMove :=
    profiledRawJointRecurrentFiniteMemoryRightToLeftMove
      (Memory := Memory) A strategy packet oldReceiver
  (profiledRawJointRecurrentFiniteMemoryRightToLeftPendingFork
      (Memory := Memory) A strategy ⟨sender.1, senderNext.2⟩ advanced.1
        packet.successor newMove,
    advanced.2)

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory]

@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork_open
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
          (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
            packet input).1.openControl =
      (oldState,
        (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A oldReceiver.1
          oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).2) :=
  rfl

theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork_closed_of_move
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.2 = some move) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
          (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
            packet input).1.closedControl =
      (packet.successor,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both) := by
  simp [profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryRightToLeftMove, hmove]

@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork_output
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    (profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
      (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
        packet input).2 =
      (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A oldReceiver.1
        oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).1 :=
  rfl

/-- The two candidates retain different lineage-local bank controls: the
strict branch keeps `oldState`, while the simultaneous branch copies the
packet successor, including its updated memory. -/
theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork_coordinates
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    (profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy fork.openControl).1 = oldState ∧
      (profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy fork.closedControl).1 =
          packet.successor :=
  ⟨rfl, rfl⟩

theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork_blind
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1.openControl
      (profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1.closedControl := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

end

noncomputable def profiledRawJointRecurrentFiniteMemoryRightToLeftStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLiveShared
        (Memory := Memory) A strategy)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLiveShared
        (Memory := Memory) A strategy × Out₁ :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    shared.1.1 false shared.1.2 input
  ((⟨shared.1.1, next.2⟩, shared.2), next.1)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryRightToLeftStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentFiniteMemoryRightToLeftStep
        (Memory := Memory) A strategy) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentFiniteMemoryRightToLeftNoRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
        (Memory := Memory) A strategy)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
        (Memory := Memory) A strategy × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentFiniteMemoryRightToLeftStep
      (Memory := Memory) A strategy) control input

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryRightToLeft_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
        (Memory := Memory) A strategy)
    (input : In₁)
    (hblind :
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentFiniteMemoryRightToLeftNoRecv
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryRightToLeftNoRecv
          (Memory := Memory) A strategy right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentFiniteMemoryRightToLeftNoRecv
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryRightToLeftNoRecv
          (Memory := Memory) A strategy right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentFiniteMemoryRightToLeftStep
      (Memory := Memory) A strategy)
    (profiledRawJointRecurrentFiniteMemoryRightToLeftStep_laws
      (Memory := Memory) A strategy) left right input hblind

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftPhaseLivePending
        (Memory := Memory) A strategy)
    (input : In₁) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryRightToLeftNoRecv
          (Memory := Memory) A strategy control input).1 =
      profiledRawJointRecurrentFiniteMemoryRightToLeftReceiver
        (Memory := Memory) A strategy control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

/-! ## Left-to-right mirror -/

abbrev ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLiveShared :=
  ProfiledRawJointLeftPhysicalSiblingExceptional A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)

abbrev ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLiveShared
      (Memory := Memory) A strategy) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLiveShared
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentFiniteMemoryLeftToRightShared
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLiveShared
      (Memory := Memory) A strategy :=
  (sender,
    ⟨oldAdvanced,
      (newState,
        initialProfiledRawJointRightPhysicalSiblingReceiver A newMove .both)⟩)

noncomputable def profiledRawJointRecurrentFiniteMemoryLeftToRightPendingFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
        (Memory := Memory) A strategy) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointRecurrentFiniteMemoryLeftToRightShared
      (Memory := Memory) A strategy sender oldAdvanced newState newMove) ()

noncomputable def profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
        (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
      (Memory := Memory) A strategy :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver_open
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryLeftToRightPendingFork
          (Memory := Memory) A strategy sender oldAdvanced newState
            newMove).openControl =
      oldAdvanced :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver_closed
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldAdvanced :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (newState : BankControl (Memory := Memory) A strategy)
    (newMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryLeftToRightPendingFork
          (Memory := Memory) A strategy sender oldAdvanced newState
            newMove).closedControl =
      (newState,
        initialProfiledRawJointRightPhysicalSiblingReceiver A newMove .both) :=
  rfl

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightAdvanceOldReceiver
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy × Out₂ :=
  let next := stepProfiledRawJointRightPhysicalSiblingReceiverFor A
    oldReceiver.1 oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input
  ((oldState, next.2), next.1)

noncomputable def profiledRawJointRecurrentFiniteMemoryLeftToRightMove
    (packet : Packet (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRightPhysicalSiblingMove A :=
  packet.successor.2.1.1.2.1.getD oldReceiver.1

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
          (Memory := Memory) A strategy) × Out₂ :=
  let advanced :=
    profiledRawJointRecurrentFiniteMemoryLeftToRightAdvanceOldReceiver
      (Memory := Memory) A strategy oldState oldReceiver oldOwner input
  let senderNext := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    sender.1 false sender.2 input.1
  let newMove :=
    profiledRawJointRecurrentFiniteMemoryLeftToRightMove
      (Memory := Memory) A strategy packet oldReceiver
  (profiledRawJointRecurrentFiniteMemoryLeftToRightPendingFork
      (Memory := Memory) A strategy ⟨sender.1, senderNext.2⟩ advanced.1
        packet.successor newMove,
    advanced.2)

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory]

@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork_open
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
          (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
            packet input).1.openControl =
      (oldState,
        (stepProfiledRawJointRightPhysicalSiblingReceiverFor A oldReceiver.1
          oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).2) :=
  rfl

theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork_closed_of_move
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.1 = some move) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
          (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
            packet input).1.closedControl =
      (packet.successor,
        initialProfiledRawJointRightPhysicalSiblingReceiver A move .both) := by
  simp [profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryLeftToRightMove, hmove]

@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork_output
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    (profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
      (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
        packet input).2 =
      (stepProfiledRawJointRightPhysicalSiblingReceiverFor A oldReceiver.1
        oldOwner oldReceiver.2.1 oldReceiver.2.2.1 input).1 :=
  rfl

theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork_coordinates
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    (profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy fork.openControl).1 = oldState ∧
      (profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy fork.closedControl).1 =
          packet.successor :=
  ⟨rfl, rfl⟩

theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork_blind
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1.openControl
      (profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1.closedControl := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

end

noncomputable def profiledRawJointRecurrentFiniteMemoryLeftToRightStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLiveShared
        (Memory := Memory) A strategy)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLiveShared
        (Memory := Memory) A strategy × Out₂ :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    shared.1.1 false shared.1.2 input
  ((⟨shared.1.1, next.2⟩, shared.2), next.1)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryLeftToRightStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentFiniteMemoryLeftToRightStep
        (Memory := Memory) A strategy) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentFiniteMemoryLeftToRightNoRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
        (Memory := Memory) A strategy)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
        (Memory := Memory) A strategy × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentFiniteMemoryLeftToRightStep
      (Memory := Memory) A strategy) control input

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryLeftToRight_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
        (Memory := Memory) A strategy)
    (input : In₂)
    (hblind :
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentFiniteMemoryLeftToRightNoRecv
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryLeftToRightNoRecv
          (Memory := Memory) A strategy right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentFiniteMemoryLeftToRightNoRecv
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryLeftToRightNoRecv
          (Memory := Memory) A strategy right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentFiniteMemoryLeftToRightStep
      (Memory := Memory) A strategy)
    (profiledRawJointRecurrentFiniteMemoryLeftToRightStep_laws
      (Memory := Memory) A strategy) left right input hblind

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightPhaseLivePending
        (Memory := Memory) A strategy)
    (input : In₂) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryLeftToRightNoRecv
          (Memory := Memory) A strategy control input).1 =
      profiledRawJointRecurrentFiniteMemoryLeftToRightReceiver
        (Memory := Memory) A strategy control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> rfl

end

end DetParityAutomaton

end DistributedSynthesis
