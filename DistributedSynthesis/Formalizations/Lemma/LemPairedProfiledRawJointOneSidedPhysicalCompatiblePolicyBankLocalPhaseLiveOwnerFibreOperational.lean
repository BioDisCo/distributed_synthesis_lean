/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreStrict

/-!
# Operational closure of the owner-fibre boundary carrier

This file turns the fibre-aware transition tests into relation-level closure
facts.  We begin with simultaneous close because it selects the closed member
of the new owner fibre.  These member-`true` states are independent of the
strict-direction tests and therefore form the first remaining fail-fast case.
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

/-! ## Exact simultaneous successors -/

/-- The left-oriented semantic state decoded after a right-oriented close.
The freshly installed left boundary keeps the stepped right receiver only as
a row template; its monitor is replaced by the monitor carried with the
advanced right owner fibre. -/
noncomputable def
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.afterOwnerFibreBoth
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
  let data := phaseData.1
  let rightReceiver := data.receiver A strategy hwin
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightReceiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
        false (data.owner A strategy hwin) input.1).2⟩
  let rightFibre :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let freshLeft := data.freshLeftDataAt A strategy hwin input move .both
  let activeLeft :
      ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
    (freshLeft.1, freshLeft.2.1,
      rightFibre.receiverAt A
        ((data.step A strategy hwin input).receiver A strategy hwin))
  ⟨activeLeft, data.1, rightFibre.2.1⟩

/-- Mirrored fibre-aware simultaneous successor. -/
noncomputable def
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.afterOwnerFibreBoth
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
  let data := phaseData.1
  let leftReceiver := data.receiver A strategy hwin
  let leftAdvancedOwner :
      ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false (data.owner A strategy hwin) input.2).2⟩
  let leftFibre :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let freshRight := data.freshRightDataAt A strategy hwin input move .both
  let activeRight :
      ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
    (freshRight.1, freshRight.2.1,
      leftFibre.receiverAt A
        ((data.step A strategy hwin input).receiver A strategy hwin))
  ⟨activeRight, data.1, leftFibre.2.1⟩

set_option maxHeartbeats 4000000 in
theorem
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreClose_decodes_left
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove :
      (phaseData.1.successor A strategy hwin input).2.1.2.2 = some move) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        result.1.1.closedControl result.2.1.closedControl =
      some (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨rightMove, row, receiverState, lastTarget⟩
  rcases oldReceiver with
    ⟨leftMove, oldRow, oldReceiverState, oldLastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((rightMove.memberController A false).labelOf owner).2 receiverState
      (input.2, input.1)).target row)
  have hmove' :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target).successor.2.1.2.2 = some move := by
    simpa only [target,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hmove
  dsimp only [target,
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] at hmove'
  have hnewMove :
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target)).2.1.2.2.getD leftMove = move := by
    dsimp only [target]
    simp [hmove']
  dsimp only [target] at hnewMove
  simp [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.afterOwnerFibreBoth,
    ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt,
    ProfiledRawJointRecurrentRightBoundaryData.target,
    ProfiledRawJointRecurrentRightBoundaryData.successor,
    ProfiledRawJointRecurrentRightBoundaryData.step,
    ProfiledRawJointRecurrentRightBoundaryData.receiver,
    ProfiledRawJointRecurrentRightBoundaryData.owner,
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
    profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
    profiledRawJointRecurrentRightToLeftMove,
    profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
    profiledRawJointRecurrentRightToLeftPhaseLiveShared,
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
    profiledRawJointRecurrentRightReceiveFor,
    profiledRawJointRightOwnerFibreControlOfOwner,
    initialProfiledRawJointLeftPhysicalSiblingReceiver,
    target, hmove']
  rw [hnewMove]
  exact
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled A
      strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
          state
            (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
              strategy hwin state target))
        (initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both)
        (move.memberController A false).initial
        (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove owner
          row receiverState (input.2, input.1)).2
        (profiledRawJointRightOwnerFibreControlOfOwner A
          ⟨rightMove,
            (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove
              false owner input.1).2⟩)
        (oldState,
          (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove
            oldOwner oldRow oldReceiverState input).2)
        (state,
          profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target))
        (state,
          profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target))

set_option maxHeartbeats 4000000 in
theorem
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreClose_decodes_right
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove :
      (phaseData.1.successor A strategy hwin input).2.1.2.1 = some move) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        result.1.1.closedControl result.2.1.closedControl =
      some (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨leftMove, row, receiverState, lastTarget⟩
  rcases oldReceiver with
    ⟨rightMove, oldRow, oldReceiverState, oldLastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((leftMove.memberController A false).labelOf owner).2 receiverState
      input).target row)
  have hmove' :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target).successor.2.1.2.1 = some move := by
    simpa only [target,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner] using hmove
  dsimp only [target,
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] at hmove'
  have hnewMove :
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target)).2.1.2.1.getD rightMove = move := by
    dsimp only [target]
    simp [hmove']
  dsimp only [target] at hnewMove
  simp [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.afterOwnerFibreBoth,
    ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt,
    ProfiledRawJointRecurrentLeftBoundaryData.target,
    ProfiledRawJointRecurrentLeftBoundaryData.successor,
    ProfiledRawJointRecurrentLeftBoundaryData.step,
    ProfiledRawJointRecurrentLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentLeftBoundaryData.owner,
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
    profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
    profiledRawJointRecurrentLeftToRightMove,
    profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
    profiledRawJointRecurrentLeftToRightPhaseLiveShared,
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
    profiledRawJointRecurrentLeftReceiveFor,
    profiledRawJointLeftOwnerFibreControlOfOwner,
    initialProfiledRawJointRightPhysicalSiblingReceiver,
    target, hmove']
  rw [hnewMove]
  exact
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibreClosed
      A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
          state
            (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
              strategy hwin state target))
        (initialProfiledRawJointRightPhysicalSiblingReceiver A move .both)
        (move.memberController A false).initial
        (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove owner row
          receiverState input).2
        (profiledRawJointLeftOwnerFibreControlOfOwner A
          ⟨leftMove,
            (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove
              false owner input.2).2⟩)
        (oldState,
          (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove
            oldOwner oldRow oldReceiverState (input.2, input.1)).2)
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
            state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target),
          state)
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
            state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target),
          state)

/- The closed fibre/installed shape produced from a right phase is disjoint
from every right-decoder branch. -/
theorem
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreClose_rejects_right
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove :
      (phaseData.1.successor A strategy hwin input).2.1.2.2 = some move) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        result.1.1.closedControl result.2.1.closedControl = none := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨rightMove, row, receiverState, lastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((rightMove.memberController A false).labelOf owner).2 receiverState
      (input.2, input.1)).target row)
  have hmove' :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target).successor.2.1.2.2 = some move := by
    simpa only [target,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hmove
  simp only [
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
    FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
    ProfiledRawJointRecurrentRightBoundaryData.target,
    ProfiledRawJointRecurrentRightBoundaryData.receiver,
    ProfiledRawJointRecurrentRightBoundaryData.owner, target, hmove',
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_reject_fibreInstalled]

/-- The mirror closed installed/fibre shape is disjoint from every
left-decoder branch. -/
theorem
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreClose_rejects_left
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove :
      (phaseData.1.successor A strategy hwin input).2.1.2.1 = some move) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        result.1.1.closedControl result.2.1.closedControl = none := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨leftMove, row, receiverState, lastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((leftMove.memberController A false).labelOf owner).2 receiverState
      input).target row)
  have hmove' :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target).successor.2.1.2.1 = some move := by
    simpa only [target,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner] using hmove
  simp only [
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
    FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
    ProfiledRawJointRecurrentLeftBoundaryData.target,
    ProfiledRawJointRecurrentLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentLeftBoundaryData.owner, target, hmove',
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_reject_installedFibre]

/-! ## Simultaneous-close invariant reconstruction -/

/-- A right-oriented joint close installs a fresh left boundary and records a
valid fibre over the advanced right owner.  The fibre reconstructs the
dormant right invariant at the original right bank coordinate. -/
theorem
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant.afterOwnerFibreBoth
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        phaseData)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (phaseData.1.successor A strategy hwin input).2.1.2.2 = some move ∧
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases hinvariant with ⟨hactive, hdormant⟩
  obtain ⟨move, hmove, hfresh⟩ :=
    hactive.exists_freshLeftAt A strategy hwin data input .both
  let rightReceiver := data.receiver A strategy hwin
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightReceiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
        false (data.owner A strategy hwin) input.1).2⟩
  let rightFibre :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  have hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre := by
    simpa only [rightFibre, rightAdvancedOwner, rightReceiver,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin data input.1
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, _past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightMonitor⟩
  have hrightMove' : data.1.2.1.2.1 = some rightFibre.1 := by
    simpa only [rightFibre, rightAdvancedOwner, rightReceiver,
      profiledRawJointRightOwnerFibreControlOfOwner] using hrightMove
  refine ⟨move, hmove, ?_⟩
  simpa only [
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.afterOwnerFibreBoth,
    rightReceiver, rightAdvancedOwner, rightFibre] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreInstalled
        A strategy hwin
          (data.successor A strategy hwin input)
          (initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both)
          (move.memberController A false).initial
          ((data.step A strategy hwin input).receiver A strategy hwin)
          rightFibre data.1 hfresh hrightFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove'

/-- Mirrored reconstruction after a left-oriented joint close. -/
theorem
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant.afterOwnerFibreBoth
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        phaseData)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (phaseData.1.successor A strategy hwin input).2.1.2.1 = some move ∧
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases hinvariant with ⟨hactive, hdormant⟩
  obtain ⟨move, hmove, hfresh⟩ :=
    hactive.exists_freshRightAt A strategy hwin data input .both
  let leftReceiver := data.receiver A strategy hwin
  let leftAdvancedOwner :
      ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false (data.owner A strategy hwin) input.2).2⟩
  let leftFibre :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  have hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre := by
    simpa only [leftFibre, leftAdvancedOwner, leftReceiver,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin data input.2
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, _past, hleftState, hleftCode, hleftRoot,
      hleftMove, _hleftOwner, _hleftMonitor⟩
  have hleftMove' : data.1.2.1.2.2 = some leftFibre.1 := by
    simpa only [leftFibre, leftAdvancedOwner, leftReceiver,
      profiledRawJointLeftOwnerFibreControlOfOwner] using hleftMove
  refine ⟨move, hmove, ?_⟩
  simpa only [
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.afterOwnerFibreBoth,
    leftReceiver, leftAdvancedOwner, leftFibre] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_installedFibre
        A strategy hwin
          (data.successor A strategy hwin input)
          (initialProfiledRawJointRightPhysicalSiblingReceiver A move .both)
          (move.memberController A false).initial
          ((data.step A strategy hwin input).receiver A strategy hwin)
          leftFibre data.1 hfresh hleftFibre hleftState leftCode hleftCode
            leftRoot hleftRoot hleftMove'

/-! ## Relation-level simultaneous closure -/

/-- The semantic selected relation is closed under the actual simultaneous
close map.  Each source orientation supplies the opposite move through its
active invariant; the two exact decoder equations then identify the closed
endpoint controls with the fibre-aware semantic successor. -/
theorem profiledRawJointRecurrentOwnerFibreBoundarySelected_both
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let result :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        inputOne two inputTwo
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      result.1 result.2 := by
  let input : In₁ × In₂ := (inputOne, inputTwo)
  cases hselected with
  | right phaseData hright hinvariant =>
      obtain ⟨move, hmove, hnextInvariant⟩ :=
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant.afterOwnerFibreBoth
          A strategy hwin phaseData hinvariant input
      let receiveResult :=
        phaseData.ownerFibreReceive A strategy hwin input
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two input = some receiveResult := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          receiveResult]
      have hleftDecode :
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
              receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl =
            some
              (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
        simpa only [receiveResult] using
          phaseData.ownerFibreClose_decodes_left A strategy hwin input move
            hmove
      have hrightReject :
          profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy
              hwin receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl = none := by
        simpa only [receiveResult] using
          phaseData.ownerFibreClose_rejects_right A strategy hwin input move
            hmove
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      exact .left
        (phaseData.afterOwnerFibreBoth A strategy hwin input move)
          hrightReject hleftDecode hnextInvariant
  | left phaseData hright hleft hinvariant =>
      obtain ⟨move, hmove, hnextInvariant⟩ :=
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant.afterOwnerFibreBoth
          A strategy hwin phaseData hinvariant input
      let receiveResult :=
        phaseData.ownerFibreReceive A strategy hwin input
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two input = some receiveResult := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft, receiveResult]
      have hrightDecode :
          profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy
              hwin receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl =
            some
              (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
        simpa only [receiveResult] using
          phaseData.ownerFibreClose_decodes_right A strategy hwin input move
            hmove
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      exact .right
        (phaseData.afterOwnerFibreBoth A strategy hwin input move)
          hrightDecode hnextInvariant

/-! ## Missing same-direction operational shapes -/

/-- An installed/staged right boundary is closed under another strict-right
round.  The installed owner and staged receiver take the same physical step,
and the resolved packet refreshes the dormant left root. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_installedStaged
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldLeftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (holdLeftMove : oldPacket.successor.2.1.2.2 = some oldLeftMove)
    (hsourceInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A oldLeftMove
              .first),
          oldPacket.successor,
          (oldLeftMove.memberController A false).initial⟩)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let oldLeftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A oldLeftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩, oldLeftInitial),
      oldPacket.successor,
      (oldLeftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, oldLeftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged A
        strategy hwin rightState rightReceiver rightOwner leftTemplate
          oldPacket oldLeftMove holdLeftMove
            oneCoordinates twoCoordinates
  refine ⟨.right currentPhase hcurrentRight (by
    simpa only [currentPhase, oldLeftInitial] using hsourceInvariant), ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightReceiver.1
      rightOwner rightReceiver.2.1 rightReceiver.2.2.1
        (inputTwo, inputOne)).2
  let rightAdvancedOwner :=
    (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
      false rightOwner inputOne).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightReceiver.1.memberController A false).labelOf rightOwner).2
          rightReceiver.2.2.1 (inputTwo, inputOne) |>.target
            rightReceiver.2.1)
  obtain ⟨leftMove, hleftMove, hfreshLeft⟩ :=
    hsourceInvariant.1.exists_freshLeftAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightAdvanced, rightAdvancedOwner⟩, leftInitial),
      packet.successor, (leftMove.memberController A false).initial⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne).1 =
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightAdvancedOwner⟩,
                leftTemplate)),
          oneCoordinates) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
      profiledRawJointRecurrentLeftToRightBridgeNoRecv,
      rightAdvancedOwner]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne).1 =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase, oldLeftInitial,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
      profiledRawJointRecurrentRightReceiveFor,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      rightAdvanced, packet]
    split <;> rfl
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightAdvancedOwner⟩,
                leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightAdvanced, some packet)),
            (rightState, packet.successor)) = some nextPhase := by
    have hleftMove' : packet.successor.2.1.2.2 = some leftMove := by
      simpa only [packet, currentPhase,
        ProfiledRawJointRecurrentRightBoundaryData.successor,
        ProfiledRawJointRecurrentRightBoundaryData.target,
        ProfiledRawJointRecurrentRightBoundaryData.receiver,
        ProfiledRawJointRecurrentRightBoundaryData.owner,
        profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
          hleftMove
    simpa only [nextPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged A
        strategy hwin rightState rightAdvanced rightAdvancedOwner leftTemplate
          packet leftMove hleftMove' oneCoordinates
            (rightState, packet.successor)
  have hactiveStepped :=
    hsourceInvariant.1.step A strategy hwin currentPhase.1
      (inputOne, inputTwo)
  have hactiveNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (rightState, ⟨rightAdvanced, rightAdvancedOwner⟩, leftInitial) := by
    have hreplaced :=
      ProfiledRawJointRecurrentRightBoundaryInvariant.replaceOldReceiver A
        strategy hwin _ hactiveStepped leftInitial
    simpa only [currentPhase, oldLeftInitial, rightAdvanced,
      rightAdvancedOwner,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hreplaced
  have hdormantNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (nextPhase.dormantLeftData A strategy hwin) := by
    simpa only [nextPhase, leftInitial, packet, currentPhase, oldLeftInitial,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hfreshLeft
  exact .right nextPhase hnextDecode ⟨hactiveNext, hdormantNext⟩

/-! ## Remaining member-bit transitions -/

/-- The open-member fibre/installed left phase crosses under strict-right to
the right-priority `(false,false)` two-fibre phase. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_openFibreInstalled
    (leftState rightState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightCoordinate : twoCoordinates.1 = rightState)
    (hactive :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate))
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr
        (false,
          (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ()),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
        rightFibre.receiverAt A rightTemplate),
      rightState, rightFibre.2.1⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ()),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, hrightCoordinate] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_openFibreInstalled
        A strategy hwin leftState leftReceiver leftOwner rightTemplate
          rightFibre newLeft oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ()),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    rfl
  have hcurrentInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreInstalled
        A strategy hwin leftState leftReceiver leftOwner rightTemplate
          rightFibre rightState hactive hrightFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ()),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]
  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let leftAdvancedOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false leftOwner inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftReceiver.1.memberController A false).labelOf leftOwner).2
          leftReceiver.2.2.1 (inputOne, inputTwo) |>.target leftReceiver.2.1)
  let newRightMove := packet.successor.2.1.2.1.getD rightFibre.1
  let newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A newRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightNext.receiverAt A rightAdvanced, rightNext.2.1⟩,
        leftNext.receiverAt A leftReceiver),
      leftState, leftNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr
          (false,
            (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
          (false, (rightNext, ⟨(leftState, leftReceiver), newLeft⟩), ()),
          oneCoordinates) := by
    rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo
        (.inr
          (false,
            (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
          (false, (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
      profiledRawJointRecurrentLeftToRightPhaseLiveShared,
      profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentLeftToRightMove,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      leftNext, leftAdvancedOwner, rightAdvanced, packet, newRight,
      newRightMove]
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftReceiver), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
            (rightState, leftState)) = some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
        strategy hwin rightState leftState rightAdvanced leftReceiver
          rightNext leftNext newLeft newRight oneCoordinates
            (rightState, leftState)
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext :=
    ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre hrightFibre
      inputOne
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin
          (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate) inputTwo
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, _past, hleftState, hleftCode, hleftRoot,
      hleftMove, _hleftOwner, _hleftMonitor⟩
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightAdvanced leftReceiver
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .right nextPhase hnextDecode hnextInvariant

/-- The closed-member fibre/installed left phase crosses under strict-right
to the right-priority `(true,false)` two-fibre phase.  This is the reachable
counterpart of `strictRight_openFibreInstalled`: the nonreceiving first
endpoint preserves its closed member and its selected fork arm. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_closedFibreInstalled
    (leftState rightState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightCoordinate : twoCoordinates.1 = rightState)
    (hactive :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate))
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr
        (true,
          (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
        rightFibre.receiverAt A rightTemplate),
      rightState, rightFibre.2.1⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, hrightCoordinate] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled
        A strategy hwin leftState leftReceiver leftOwner rightTemplate
          rightFibre oldLeft oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    rfl
  have hcurrentInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreInstalled
        A strategy hwin leftState leftReceiver leftOwner rightTemplate
          rightFibre rightState hactive hrightFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]
  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let leftAdvancedOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false leftOwner inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftReceiver.1.memberController A false).labelOf leftOwner).2
          leftReceiver.2.2.1 (inputOne, inputTwo) |>.target leftReceiver.2.1)
  let newRightMove := packet.successor.2.1.2.1.getD rightFibre.1
  let newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A newRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightNext.receiverAt A rightAdvanced, rightNext.2.1⟩,
        leftNext.receiverAt A leftReceiver),
      leftState, leftNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr
          (true,
            (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
          (true, (rightNext, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          oneCoordinates) := by
    rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo
        (.inr
          (true,
            (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
          (false, (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
      profiledRawJointRecurrentLeftToRightPhaseLiveShared,
      profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentLeftToRightMove,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      leftNext, leftAdvancedOwner, rightAdvanced, packet, newRight,
      newRightMove]
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightNext, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
            (rightState, leftState)) = some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightAdvanced leftReceiver
          rightNext leftNext oldLeft newRight oneCoordinates
            (rightState, leftState)
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext :=
    ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre hrightFibre
      inputOne
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin
          (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate) inputTwo
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, _past, hleftState, hleftCode, hleftRoot,
      hleftMove, _hleftOwner, _hleftMonitor⟩
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightAdvanced leftReceiver
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .right nextPhase hnextDecode hnextInvariant

/-- Mirror of the preceding member-bit case: an installed/open-fibre right
phase crosses under strict-left to the right-priority `(false,false)` phase. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_installedOpenFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hleftCoordinate : oneCoordinates.2 = leftState)
    (hactive :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate))
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr
        (false,
          (leftFibre, ⟨(rightState, rightReceiver), newRight⟩), ()),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightReceiver), newRight⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, hleftCoordinate] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre A
        strategy hwin rightState rightReceiver rightOwner leftTemplate
          leftFibre newRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_installedFibre
        A strategy hwin rightState rightReceiver rightOwner leftTemplate
          leftFibre leftState hactive hleftFibre hleftState leftCode hleftCode
            leftRoot hleftRoot hleftMove
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightReceiver), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftTemplate.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightReceiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
        false rightOwner inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightReceiver.1.memberController A false).labelOf rightOwner).2
          rightReceiver.2.2.1 (inputTwo, inputOne) |>.target
            rightReceiver.2.1)
  let newLeftMove := packet.successor.2.1.2.2.getD leftFibre.1
  let newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A newLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightNext.receiverAt A rightReceiver, rightNext.2.1⟩,
        leftNext.receiverAt A leftAdvanced),
      leftState, leftNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne
        (.inr
          (false,
            (leftFibre, ⟨(rightState, rightReceiver), newRight⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
          (false, (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
      profiledRawJointRecurrentRightToLeftPhaseLiveShared,
      profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentRightToLeftMove,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightNext, rightAdvancedOwner, leftAdvanced, packet, newLeft,
      newLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr
          (false,
            (leftFibre, ⟨(rightState, rightReceiver), newRight⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
          (false, (leftNext, ⟨(rightState, rightReceiver), newRight⟩), ()),
          twoCoordinates) := by
    rfl
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
            (rightState, leftState))
          (.inr
            (false,
              (leftNext, ⟨(rightState, rightReceiver), newRight⟩), ()),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
        strategy hwin rightState leftState rightReceiver leftAdvanced
          rightNext leftNext newLeft newRight (rightState, leftState)
            twoCoordinates
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext :=
    ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre inputTwo
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin
          (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate) inputOne
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, _past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightMonitor⟩
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightReceiver leftAdvanced
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .right nextPhase hnextDecode hnextInvariant

/-- The closed-member installed/fibre right phase crosses under strict-left
to the left-priority `(false,true)` two-fibre phase.  The nonreceiving second
endpoint preserves both its closed member bit and the selected arm of its
stored receiver fork. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_installedClosedFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hleftCoordinate : oneCoordinates.2 = leftState)
    (hactive :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate))
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr
        (true,
          (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, hleftCoordinate] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibreClosed
        A strategy hwin rightState rightReceiver rightOwner leftTemplate
          leftFibre oldRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_installedFibre
        A strategy hwin rightState rightReceiver rightOwner leftTemplate
          leftFibre leftState hactive hleftFibre hleftState leftCode hleftCode
            leftRoot hleftRoot hleftMove
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftTemplate.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightReceiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
        false rightOwner inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightReceiver.1.memberController A false).labelOf rightOwner).2
          rightReceiver.2.2.1 (inputTwo, inputOne) |>.target
            rightReceiver.2.1)
  let newLeftMove := packet.successor.2.1.2.2.getD leftFibre.1
  let newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A newLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftNext.receiverAt A leftAdvanced, leftNext.2.1⟩,
        rightNext.receiverAt A rightReceiver),
      rightState, rightNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne
        (.inr
          (true,
            (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
          (false, (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
      profiledRawJointRecurrentRightToLeftPhaseLiveShared,
      profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentRightToLeftMove,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightNext, rightAdvancedOwner, leftAdvanced, packet, newLeft,
      newLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr
          (true,
            (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
          (true, (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          twoCoordinates) := by
    rfl
  rw [honeNext, htwoNext]
  have hnextRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
            (rightState, leftState))
          (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            twoCoordinates) = none := by
    rfl
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
            (rightState, leftState))
          (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightReceiver leftAdvanced
          rightNext leftNext newLeft oldRight (rightState, leftState)
            twoCoordinates
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext :=
    ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre inputTwo
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin
          (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate) inputOne
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, _past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightMonitor⟩
  have hnextInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightReceiver leftAdvanced
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .left nextPhase hnextRight hnextDecode hnextInvariant

/-- Mirrored member-uniform transition from fibre/installed to
staged/installed under a strict-left round. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreInstalled_toStaged
    (rightState leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate oldRightReceiver :
      ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (oldRightReceiver.1.memberController A false).Control)
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightReject :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr pendingOne, oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr pendingOne, oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) =
        some
          ⟨(leftState, ⟨leftReceiver, leftOwner⟩, oldRightReceiver),
            rightState, rightOwner⟩)
    (hinvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩, oldRightReceiver),
          rightState, rightOwner⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) inputOne
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo).1 := by
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩, oldRightReceiver),
      rightState, rightOwner⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr pendingOne, oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hrightReject,
      hdecode, currentPhase]
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftReceiver.1
      leftOwner leftReceiver.2.1 leftReceiver.2.2.1
        (inputOne, inputTwo)).2
  let leftAdvancedOwner :=
    (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
      false leftOwner inputTwo).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftReceiver.1.memberController A false).labelOf leftOwner).2
          leftReceiver.2.2.1 (inputOne, inputTwo) |>.target
            leftReceiver.2.1)
  obtain ⟨rightMove, hrightMove, hfreshRight⟩ :=
    hinvariant.1.exists_freshRightAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftAdvanced, leftAdvancedOwner⟩, rightInitial),
      packet.successor, (rightMove.memberController A false).initial⟩
  rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
  rw [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo]
  simp only [profiledRawJointRecurrentRightToLeftBridgeNoRecv]
  change ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
    ((currentPhase.ownerFibreReceive A strategy hwin
      (inputOne, inputTwo)).1.1.openControl)
    (.inl
      (.inr
        (leftState, ⟨leftReceiver.1, leftAdvancedOwner⟩, rightTemplate)),
      twoCoordinates)
  have honeShape :
      (currentPhase.ownerFibreReceive A strategy hwin
        (inputOne, inputTwo)).1.1.openControl =
        (.inl (.inl (leftState, leftAdvanced, some packet)),
          (packet.successor, leftState)) := by
    dsimp [currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
      profiledRawJointRecurrentLeftReceiveFor,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      leftAdvanced, packet]
    split <;> rfl
  rw [honeShape]
  have hrightMove' : packet.successor.2.1.2.1 = some rightMove := by
    simpa only [packet, currentPhase,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
        hrightMove
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftAdvanced, some packet)),
            (packet.successor, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftAdvancedOwner⟩,
                rightTemplate)),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase, rightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled A
        strategy hwin leftState leftAdvanced leftAdvancedOwner rightTemplate
          packet rightMove hrightMove' (packet.successor, leftState)
            twoCoordinates
  have hactiveStepped :=
    hinvariant.1.step A strategy hwin currentPhase.1 (inputOne, inputTwo)
  have hactiveNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftAdvanced, leftAdvancedOwner⟩, rightInitial) := by
    have hreplaced :=
      ProfiledRawJointRecurrentLeftBoundaryInvariant.replaceOldReceiver A
        strategy hwin _ hactiveStepped rightInitial
    simpa only [currentPhase, leftAdvanced, leftAdvancedOwner,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner] using hreplaced
  have hdormantNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (nextPhase.dormantRightData A strategy hwin) := by
    simpa only [nextPhase, rightInitial, packet, currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner] using hfreshRight
  exact .left nextPhase (by rfl) hnextDecode
    ⟨hactiveNext, hdormantNext⟩

/-- Any installed/fibre control pair that decodes to the displayed valid
right phase moves to an installed/staged right phase on a strict-right
round.  This formulation covers both selected member bits of the fibre
payload. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_installedFibre_toStaged
    (rightState leftState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate oldLeftReceiver :
      ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (oldLeftReceiver.1.memberController A false).Control)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inr pendingTwo, twoCoordinates) =
        some
          ⟨(rightState, ⟨rightReceiver, rightOwner⟩, oldLeftReceiver),
            leftState, leftOwner⟩)
    (hinvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩, oldLeftReceiver),
          leftState, leftOwner⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) inputTwo
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne).1 := by
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩, oldLeftReceiver),
      leftState, leftOwner⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inr pendingTwo, twoCoordinates) (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hdecode,
      currentPhase]
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightReceiver.1
      rightOwner rightReceiver.2.1 rightReceiver.2.2.1
        (inputTwo, inputOne)).2
  let rightAdvancedOwner :=
    (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
      false rightOwner inputOne).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightReceiver.1.memberController A false).labelOf rightOwner).2
          rightReceiver.2.2.1 (inputTwo, inputOne) |>.target
            rightReceiver.2.1)
  obtain ⟨leftMove, hleftMove, hfreshLeft⟩ :=
    hinvariant.1.exists_freshLeftAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightAdvanced, rightAdvancedOwner⟩, leftInitial),
      packet.successor, (leftMove.memberController A false).initial⟩
  rw [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne]
  simp only [profiledRawJointRecurrentLeftToRightBridgeNoRecv]
  rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
  change ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
    (.inl
      (.inr
        (rightState, ⟨rightReceiver.1, rightAdvancedOwner⟩, leftTemplate)),
      oneCoordinates)
    ((currentPhase.ownerFibreReceive A strategy hwin
      (inputOne, inputTwo)).2.1.openControl)
  have htwoShape :
      (currentPhase.ownerFibreReceive A strategy hwin
        (inputOne, inputTwo)).2.1.openControl =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
      profiledRawJointRecurrentRightReceiveFor,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      rightAdvanced, packet]
    split <;> rfl
  rw [htwoShape]
  have hleftMove' : packet.successor.2.1.2.2 = some leftMove := by
    simpa only [packet, currentPhase,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
        hleftMove
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightAdvancedOwner⟩,
                leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightAdvanced, some packet)),
            (rightState, packet.successor)) = some nextPhase := by
    simpa only [nextPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged A
        strategy hwin rightState rightAdvanced rightAdvancedOwner leftTemplate
          packet leftMove hleftMove' oneCoordinates
            (rightState, packet.successor)
  have hactiveStepped :=
    hinvariant.1.step A strategy hwin currentPhase.1 (inputOne, inputTwo)
  have hactiveNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (rightState, ⟨rightAdvanced, rightAdvancedOwner⟩, leftInitial) := by
    have hreplaced :=
      ProfiledRawJointRecurrentRightBoundaryInvariant.replaceOldReceiver A
        strategy hwin _ hactiveStepped leftInitial
    simpa only [currentPhase, rightAdvanced, rightAdvancedOwner,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hreplaced
  have hdormantNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (nextPhase.dormantLeftData A strategy hwin) := by
    simpa only [nextPhase, leftInitial, packet, currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hfreshLeft
  exact .right nextPhase hnextDecode ⟨hactiveNext, hdormantNext⟩

/-- Mirrored same-direction closure of the reachable staged/fibre left shape.
The left decoder requires the retained second-endpoint member to be closed. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_stagedFibre_loop
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight newRight :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldRightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (holdRightMove : oldPacket.successor.2.1.2.1 = some oldRightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hsourceInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(leftState,
            ⟨leftFibre.receiverAt A leftReceiver, leftFibre.2.1⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A oldRightMove
              .first),
          oldPacket.successor,
          (oldRightMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl (.inl (leftState, leftReceiver, some oldPacket)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let oldRightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A oldRightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState,
        ⟨leftFibre.receiverAt A leftReceiver, leftFibre.2.1⟩,
        oldRightInitial),
      oldPacket.successor,
      (oldRightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, oldRightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedFibre A
        strategy hwin leftState leftReceiver leftFibre oldRight newRight
          oldPacket oldRightMove holdRightMove
            oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
            twoCoordinates) = none := by
    rfl
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft (by
    simpa only [currentPhase, oldRightInitial] using hsourceInvariant), ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]
  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftReceiver.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftFibre.1.memberController A false).labelOf leftFibre.2.1).2
          leftFibre.2.2 (inputOne, inputTwo) |>.target leftReceiver.2.1)
  obtain ⟨rightMove, hrightMove, hfreshRight⟩ :=
    hsourceInvariant.1.exists_freshRightAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftNext.receiverAt A leftAdvanced, leftNext.2.1⟩,
        rightInitial),
      packet.successor, (rightMove.memberController A false).initial⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne
        (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inl (.inl (leftState, leftAdvanced, some packet)),
          (packet.successor, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase, oldRightInitial,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
      profiledRawJointRecurrentLeftReceiveFor,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      leftAdvanced, packet]
    split <;> rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr (true, (leftNext, ⟨oldRight, newRight⟩), ()),
          twoCoordinates) := by
    rfl
  rw [honeNext, htwoNext]
  have hrightMove' : packet.successor.2.1.2.1 = some rightMove := by
    simpa only [packet, currentPhase,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
        hrightMove
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftAdvanced, some packet)),
            (packet.successor, leftState))
          (.inr (true, (leftNext, ⟨oldRight, newRight⟩), ()),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase, rightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedFibre A
        strategy hwin leftState leftAdvanced leftNext oldRight newRight packet
          rightMove hrightMove' (packet.successor, leftState)
            twoCoordinates
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext :=
    ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre inputTwo
  have hactiveCopy := hsourceInvariant.1
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, _past, hleftState, hleftCode, hleftRoot,
      hleftMove, _hleftOwner, _hleftMonitor⟩
  have hleftNextMove : leftState.2.1.2.2 = some leftNext.1 := by
    simpa only [leftNext, profiledRawJointLeftOwnerFibreNoRecv] using hleftMove
  have hactiveNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftNext.receiverAt A leftAdvanced, leftNext.2.1⟩,
          rightInitial) := by
    simpa only [ProfiledRawJointLeftOwnerFibreControl.boundaryData,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] using
        hleftNext.boundaryInvariant A strategy hwin leftNext leftState
          hleftState leftCode hleftCode leftRoot hleftRoot hleftNextMove
            leftAdvanced.2.1 rightInitial
  have hfreshReplaced :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        ((currentPhase.1.freshRightDataAt A strategy hwin
          (inputOne, inputTwo) rightMove .first).1,
        (currentPhase.1.freshRightDataAt A strategy hwin
          (inputOne, inputTwo) rightMove .first).2.1,
        leftNext.receiverAt A leftAdvanced) :=
    ProfiledRawJointRecurrentRightBoundaryInvariant.replaceOldReceiver A
      strategy hwin _ hfreshRight (leftNext.receiverAt A leftAdvanced)
  have hdormantNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (nextPhase.dormantRightData A strategy hwin) := by
    simpa only [nextPhase, rightInitial, packet, currentPhase, oldRightInitial,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] using hfreshReplaced
  exact .left nextPhase (by rfl) hnextDecode
    ⟨hactiveNext, hdormantNext⟩

/-- Mirrored same-direction closure of a staged/installed left boundary under
another strict-left round. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_stagedInstalled
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldRightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (holdRightMove : oldPacket.successor.2.1.2.1 = some oldRightMove)
    (hsourceInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A oldRightMove
              .first),
          oldPacket.successor,
          (oldRightMove.memberController A false).initial⟩)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl (.inl (leftState, leftReceiver, some oldPacket)), oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let oldRightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A oldRightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩, oldRightInitial),
      oldPacket.successor,
      (oldRightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, oldRightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled A
        strategy hwin leftState leftReceiver leftOwner rightTemplate
          oldPacket oldRightMove holdRightMove
            oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    rfl
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft (by
    simpa only [currentPhase, oldRightInitial] using hsourceInvariant), ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftReceiver.1
      leftOwner leftReceiver.2.1 leftReceiver.2.2.1
        (inputOne, inputTwo)).2
  let leftAdvancedOwner :=
    (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
      false leftOwner inputTwo).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftReceiver.1.memberController A false).labelOf leftOwner).2
          leftReceiver.2.2.1 (inputOne, inputTwo) |>.target
            leftReceiver.2.1)
  obtain ⟨rightMove, hrightMove, hfreshRight⟩ :=
    hsourceInvariant.1.exists_freshRightAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftAdvanced, leftAdvancedOwner⟩, rightInitial),
      packet.successor, (rightMove.memberController A false).initial⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo).1 =
        (.inl (.inl (leftState, leftAdvanced, some packet)),
          (packet.successor, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase, oldRightInitial,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
      profiledRawJointRecurrentLeftReceiveFor,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      leftAdvanced, packet]
    split <;> rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo).1 =
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftAdvancedOwner⟩,
                rightTemplate)),
          twoCoordinates) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
      profiledRawJointRecurrentRightToLeftBridgeNoRecv,
      leftAdvancedOwner]
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftAdvanced, some packet)),
            (packet.successor, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftAdvancedOwner⟩,
                rightTemplate)),
            twoCoordinates) = some nextPhase := by
    have hrightMove' : packet.successor.2.1.2.1 = some rightMove := by
      simpa only [packet, currentPhase,
        ProfiledRawJointRecurrentLeftBoundaryData.successor,
        ProfiledRawJointRecurrentLeftBoundaryData.target,
        ProfiledRawJointRecurrentLeftBoundaryData.receiver,
        ProfiledRawJointRecurrentLeftBoundaryData.owner,
        profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
          hrightMove
    simpa only [nextPhase, rightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled A
        strategy hwin leftState leftAdvanced leftAdvancedOwner rightTemplate
          packet rightMove hrightMove' (packet.successor, leftState)
            twoCoordinates
  have hactiveStepped :=
    hsourceInvariant.1.step A strategy hwin currentPhase.1
      (inputOne, inputTwo)
  have hactiveNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftAdvanced, leftAdvancedOwner⟩, rightInitial) := by
    have hreplaced :=
      ProfiledRawJointRecurrentLeftBoundaryInvariant.replaceOldReceiver A
        strategy hwin _ hactiveStepped rightInitial
    simpa only [currentPhase, oldRightInitial, leftAdvanced,
      leftAdvancedOwner,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner] using hreplaced
  have hdormantNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (nextPhase.dormantRightData A strategy hwin) := by
    simpa only [nextPhase, rightInitial, packet, currentPhase, oldRightInitial,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner] using hfreshRight
  exact .left nextPhase (by rfl) hnextDecode
    ⟨hactiveNext, hdormantNext⟩

/-- A fibre/staged right boundary is closed under a same-direction
strict-right round for either retained member bit.  The blind fibre step may
use a different hidden input from the staged physical receiver; decoding
therefore keeps only the staged row and installs the fibre monitor. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_fibreStaged
    (member : Bool)
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (oldLeftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (holdLeftMove : oldPacket.successor.2.1.2.2 = some oldLeftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hsourceInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(rightState,
            ⟨rightFibre.receiverAt A rightReceiver, rightFibre.2.1⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A oldLeftMove
              .first),
          oldPacket.successor,
          (oldLeftMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let oldLeftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A oldLeftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightReceiver, rightFibre.2.1⟩,
        oldLeftInitial),
      oldPacket.successor,
      (oldLeftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, oldLeftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged A
        strategy hwin rightState rightReceiver rightFibre oldLeft newLeft
          oldPacket oldLeftMove holdLeftMove
            oneCoordinates twoCoordinates
  refine ⟨.right currentPhase hcurrentRight (by
    simpa only [currentPhase, oldLeftInitial] using hsourceInvariant), ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightReceiver.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
          rightFibre.2.2 (inputTwo, inputOne) |>.target rightReceiver.2.1)
  obtain ⟨leftMove, hleftMove, hfreshLeft⟩ :=
    hsourceInvariant.1.exists_freshLeftAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightNext.receiverAt A rightAdvanced, rightNext.2.1⟩,
        leftInitial),
      packet.successor, (leftMove.memberController A false).initial⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr (member, (rightNext, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) := by
    rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo
        (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase, oldLeftInitial,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
      profiledRawJointRecurrentRightReceiveFor,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      rightAdvanced, packet]
    split <;> rfl
  rw [honeNext, htwoNext]
  have hleftMove' : packet.successor.2.1.2.2 = some leftMove := by
    simpa only [packet, currentPhase,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
        hleftMove
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr (member, (rightNext, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightAdvanced, some packet)),
            (rightState, packet.successor)) = some nextPhase := by
    simpa only [nextPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged A
        strategy hwin rightState rightAdvanced rightNext oldLeft newLeft
          packet leftMove hleftMove' oneCoordinates
            (rightState, packet.successor)
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext :=
    ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre hrightFibre
      inputOne
  have hactiveCopy := hsourceInvariant.1
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, _past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightMonitor⟩
  have hrightNextMove : rightState.2.1.2.1 = some rightNext.1 := by
    simpa only [rightNext, profiledRawJointRightOwnerFibreNoRecv] using
      hrightMove
  have hactiveNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (rightState, ⟨rightNext.receiverAt A rightAdvanced, rightNext.2.1⟩,
          leftInitial) := by
    simpa only [ProfiledRawJointRightOwnerFibreControl.boundaryData,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using
        hrightNext.boundaryInvariant A strategy hwin rightNext rightState
          hrightState rightCode hrightCode rightRoot hrightRoot hrightNextMove
            rightAdvanced.2.1 leftInitial
  have hfreshReplaced :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        ((currentPhase.1.freshLeftDataAt A strategy hwin
          (inputOne, inputTwo) leftMove .first).1,
        (currentPhase.1.freshLeftDataAt A strategy hwin
          (inputOne, inputTwo) leftMove .first).2.1,
        rightNext.receiverAt A rightAdvanced) :=
    ProfiledRawJointRecurrentLeftBoundaryInvariant.replaceOldReceiver A
      strategy hwin _ hfreshLeft (rightNext.receiverAt A rightAdvanced)
  have hdormantNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (nextPhase.dormantLeftData A strategy hwin) := by
    simpa only [nextPhase, leftInitial, packet, currentPhase, oldLeftInitial,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using hfreshReplaced
  exact .right nextPhase hnextDecode ⟨hactiveNext, hdormantNext⟩

/-! ## Nonzero two-fibre transitions -/

/-- In a fibre/staged right shape, the decoder uses the fibre itself and the
staged receiver.  It does not inspect the retained member bit or either arm
of the obsolete receiver fork stored beside the fibre. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.fibreStaged_of_sameFibre
    (sourceMember targetMember : Bool)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (sourceFork targetFork :
      FiniteDelayedFork
        (ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin))
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr (sourceMember, (rightFibre, sourceFork), ()), oneCoordinates)
        (.inl (.inl staged), twoCoordinates)) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (.inr (targetMember, (rightFibre, targetFork), ()), oneCoordinates)
      (.inl (.inl staged), twoCoordinates) := by
  cases hselected with
  | right phaseData hdata hinvariant =>
      exact .right phaseData (by
        simpa [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
          profiledRawJointRecurrentRightToLeftOwnerFibreReceiver] using hdata)
        hinvariant
  | left phaseData hright hdata hinvariant =>
      exact .left phaseData (by
        simpa [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
          profiledRawJointRecurrentRightToLeftOwnerFibreReceiver] using hright)
        (by
          simpa [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
            profiledRawJointRecurrentRightToLeftOwnerFibreReceiver] using
              hdata)
        hinvariant

/-- In the right-priority `(true,false)` state, a strict-left round opens the
right pending endpoint and hence reaches `(false,false)`.  Reversing the
irrelevant arms of the right receiver fork reduces this transition to the
already proved open/open round without changing the decoded semantic receive. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre oldLeft newRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  have hsource :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates)
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) :=
    .right currentPhase hcurrentRight hcurrentInvariant

  have hbase :=
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_openOpen A
      strategy hwin rightState leftState rightTemplate leftTemplate
        rightFibre leftFibre oldLeft newRight oneCoordinates twoCoordinates
          hrightFibre hleftFibre hrightState rightCode hrightCode rightRoot
            hrightRoot hrightMove hleftState leftCode hleftCode leftRoot
              hleftRoot hleftMove inputOne inputTwo
  have hcurrentOpen :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A strategy
        hwin rightState leftState rightTemplate leftTemplate rightFibre
          leftFibre oldLeft newRight oneCoordinates twoCoordinates
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  have hreceiveOpen :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentOpen]
  have hopen :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates) inputOne
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo).1 =
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) inputOne
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo).1 := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
      profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive,
      hreceiveOpen]
  refine ⟨hsource, ?_⟩
  rw [hopen]
  exact hbase.2

/-- In the right-priority `(true,false)` state, a strict-right round preserves
the closed right member and crosses to fibre/staged form.  Its semantic
receive is the same as for the open/open representative with the selected
fork arm moved to the other side; the fibre/staged decoder then discards the
retained bit and obsolete fork. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_fibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre oldLeft newRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  have hsource :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates)
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) :=
    .right currentPhase hcurrentRight hcurrentInvariant
  have hbase :=
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_openOpen A
      strategy hwin rightState leftState rightTemplate leftTemplate
        rightFibre leftFibre oldLeft newRight oneCoordinates twoCoordinates
          hrightFibre hleftFibre
          hrightState rightCode hrightCode rightRoot hrightRoot hrightMove
            hleftState leftCode hleftCode leftRoot hleftRoot hleftMove
              inputOne inputTwo
  have hcurrentOpen :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A strategy
        hwin rightState leftState rightTemplate leftTemplate rightFibre
          leftFibre oldLeft newRight oneCoordinates twoCoordinates
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  have hreceiveOpen :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentOpen]
  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
          rightFibre.2.2 (inputTwo, inputOne) |>.target rightTemplate.2.1)
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
            (true,
              (rightNext, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates) := by
    rfl
  have honeOpen :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (rightNext, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) := by
    rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
      profiledRawJointRecurrentRightReceiveFor,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightAdvanced, packet]
    split <;> rfl
  have htwoOpen :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceiveOpen]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
      profiledRawJointRecurrentRightReceiveFor,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightAdvanced, packet]
    split <;> rfl
  have hbaseTarget := hbase.2
  rw [honeOpen, htwoOpen] at hbaseTarget
  refine ⟨hsource, ?_⟩
  rw [honeNext, htwoNext]
  exact
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.fibreStaged_of_sameFibre
      A strategy hwin false true rightNext
        ⟨(leftState, leftTemplate), oldLeft⟩
        ⟨oldLeft, (leftState, leftTemplate)⟩
        (rightState, rightAdvanced, some packet) oneCoordinates
          (rightState, packet.successor) hbaseTarget

/-- A strict-left round changes the right-priority `(true,true)` two-fibre
state into the left-priority `(false,true)` state.  The receiving endpoint
creates a fresh right fibre, while the nonreceiving endpoint advances the
left fibre without changing its selected member. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_closedClosed
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true, (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_closedClosed A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre oldLeft oldRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]

  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftTemplate.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightFibre.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightFibre.1
        false rightFibre.2.1 inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
          rightFibre.2.2 (inputTwo, inputOne) |>.target rightTemplate.2.1)
  let newLeftMove := packet.successor.2.1.2.2.getD leftFibre.1
  let nextNewLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A newLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState,
        ⟨leftNext.receiverAt A leftAdvanced, leftNext.2.1⟩,
        rightNext.receiverAt A rightTemplate),
      rightState, rightNext.2.1⟩

  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates) inputOne
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), nextNewLeft⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
      profiledRawJointRecurrentRightToLeftPhaseLiveShared,
      profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentRightToLeftMove,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightNext, rightAdvancedOwner, leftAdvanced, packet, nextNewLeft,
      newLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) := by
    rfl
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), nextNewLeft⟩), ()),
            (rightState, leftState))
          (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftAdvanced
          rightNext leftNext nextNewLeft oldRight (rightState, leftState)
            twoCoordinates
  have hrightReject :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), nextNewLeft⟩), ()),
            (rightState, leftState))
          (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = none := by
    rfl
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hcurrentInvariant.1.advancedOwnerFibreControl_valid A strategy hwin
          currentPhase.1 inputOne
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    exact ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre
      inputTwo
  have hnextInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftAdvanced
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .left nextPhase hrightReject hnextDecode hnextInvariant

/-- A strict-right round from `(true,true)` has the same semantic receive as
the `(true,false)` representative obtained by swapping the selected arm of
the left fibre's receiver fork.  Since process one is unchanged by that
comparison, both rounds have exactly the same fibre/staged target. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_closedClosed
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true, (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_closedClosed A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre oldLeft oldRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  have hsource :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates)
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) :=
    .right currentPhase hcurrentRight hcurrentInvariant
  have hbase :=
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_fibreFibre
      A strategy hwin rightState leftState rightTemplate leftTemplate
        rightFibre leftFibre oldLeft oldRight oneCoordinates twoCoordinates
          hrightFibre hleftFibre
          hrightState rightCode hrightCode rightRoot hrightRoot hrightMove
            hleftState leftCode hleftCode leftRoot hleftRoot hleftMove
              inputOne inputTwo
  have hcurrentBase :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), oldRight⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre oldLeft oldRight oneCoordinates twoCoordinates
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  have hreceiveBase :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), oldRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentBase]
  have hopen :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates) inputOne).1 =
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), oldRight⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ()),
          oneCoordinates) inputOne).1 := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
      profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive,
      hreceiveBase]
  refine ⟨hsource, ?_⟩
  rw [hopen]
  exact hbase.2

/-- A strict-right round from the left-priority `(false,true)` two-fibre
state advances the right fibre blindly and installs the freshly advanced
left owner fibre.  Both selected members are then open, so the target is the
right-priority `(false,false)` state. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_leftFibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true, (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState,
        ⟨leftFibre.receiverAt A leftTemplate, leftFibre.2.1⟩,
        rightFibre.receiverAt A rightTemplate),
      rightState, rightFibre.2.1⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre oldLeft oldRight oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = none := by
    rfl
  have hcurrentInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  refine
    ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]
  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let leftAdvancedOwner :
      ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftFibre.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftFibre.1
        false leftFibre.2.1 inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftFibre.1.memberController A false).labelOf leftFibre.2.1).2
          leftFibre.2.2 (inputOne, inputTwo) |>.target leftTemplate.2.1)
  let newRightMove := packet.successor.2.1.2.1.getD rightFibre.1
  let newRight :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A newRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightNext.receiverAt A rightAdvanced, rightNext.2.1⟩,
        leftNext.receiverAt A leftTemplate),
      leftState, leftNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (rightNext, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) := by
    rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
      profiledRawJointRecurrentLeftToRightPhaseLiveShared,
      profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentLeftToRightMove,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      leftNext, leftAdvancedOwner, rightAdvanced, packet, newRight,
      newRightMove]
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
            (rightState, leftState)) = some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
        strategy hwin rightState leftState rightAdvanced leftTemplate
          rightNext leftNext oldLeft newRight oneCoordinates
            (rightState, leftState)
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext :=
    ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre hrightFibre
      inputOne
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        hcurrentInvariant.1.advancedOwnerFibreControl_valid A strategy hwin
          currentPhase.1 inputTwo
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightAdvanced leftTemplate
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .right nextPhase hnextDecode hnextInvariant

/-- A strict-left round from the left-priority `(false,true)` state keeps the
closed left member and crosses to staged/fibre form.  The staged control
records the active physical step, while decoding replaces its monitor by the
one carried by the blindly advanced left fibre. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_leftFibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () = some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true, (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState,
        ⟨leftFibre.receiverAt A leftTemplate, leftFibre.2.1⟩,
        rightFibre.receiverAt A rightTemplate),
      rightState, rightFibre.2.1⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre oldLeft oldRight oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = none := by
    rfl
  have hcurrentInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  refine
    ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
            oneCoordinates)
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]
  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftTemplate.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftFibre.1.memberController A false).labelOf leftFibre.2.1).2
          leftFibre.2.2 (inputOne, inputTwo) |>.target leftTemplate.2.1)
  obtain ⟨rightMove, hrightMoveAt, hfreshRight⟩ :=
    hcurrentInvariant.1.exists_freshRightAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftNext.receiverAt A leftAdvanced, leftNext.2.1⟩,
        rightInitial),
      packet.successor, (rightMove.memberController A false).initial⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ()),
          oneCoordinates) inputOne
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inl (.inl (leftState, leftAdvanced, some packet)),
          (packet.successor, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
      profiledRawJointRecurrentLeftReceiveFor,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      leftAdvanced, packet]
    split <;> rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
          twoCoordinates) := by
    rfl
  rw [honeNext, htwoNext]
  have hrightMove' : packet.successor.2.1.2.1 = some rightMove := by
    simpa only [packet, currentPhase,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
        hrightMoveAt
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftAdvanced, some packet)),
            (packet.successor, leftState))
          (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightTemplate)⟩), ()),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase, rightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedFibre A
        strategy hwin leftState leftAdvanced leftNext oldRight
          (rightState, rightTemplate) packet rightMove hrightMove'
            (packet.successor, leftState) twoCoordinates
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext :=
    ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre inputTwo
  have hleftNextMove : leftState.2.1.2.2 = some leftNext.1 := by
    simpa only [leftNext, profiledRawJointLeftOwnerFibreNoRecv] using hleftMove
  have hactiveNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftNext.receiverAt A leftAdvanced, leftNext.2.1⟩,
          rightInitial) := by
    simpa only [ProfiledRawJointLeftOwnerFibreControl.boundaryData,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] using
        hleftNext.boundaryInvariant A strategy hwin leftNext leftState
          hleftState leftCode hleftCode leftRoot hleftRoot hleftNextMove
            leftAdvanced.2.1 rightInitial
  have hfreshReplaced :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        ((currentPhase.1.freshRightDataAt A strategy hwin
          (inputOne, inputTwo) rightMove .first).1,
        (currentPhase.1.freshRightDataAt A strategy hwin
          (inputOne, inputTwo) rightMove .first).2.1,
        leftNext.receiverAt A leftAdvanced) :=
    ProfiledRawJointRecurrentRightBoundaryInvariant.replaceOldReceiver A
      strategy hwin _ hfreshRight (leftNext.receiverAt A leftAdvanced)
  have hdormantNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (nextPhase.dormantRightData A strategy hwin) := by
    simpa only [nextPhase, rightInitial, packet, currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] using hfreshReplaced
  exact .left nextPhase (by rfl) hnextDecode
    ⟨hactiveNext, hdormantNext⟩

/-- The strict-left bridge handoff from fibre/staged is independent of the
retained member bit and obsolete receiver fork.  Opening process one selects
the same semantic receive fork in either case. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreStaged_member
    (member : Bool)
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightCoordinate : twoCoordinates.1 = rightState)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hsourceInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(rightState,
            ⟨rightFibre.receiverAt A rightReceiver, rightFibre.2.1⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          oldPacket.successor,
          (leftMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightReceiver, rightFibre.2.1⟩,
        leftInitial),
      oldPacket.successor, (leftMove.memberController A false).initial⟩
  have hcurrent :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged A
        strategy hwin rightState rightReceiver rightFibre oldLeft newLeft
          oldPacket leftMove hleftMove oneCoordinates twoCoordinates
  have hsource :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates)
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) :=
    .right currentPhase hcurrent (by
      simpa only [currentPhase, leftInitial] using hsourceInvariant)
  have hbase :=
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreStaged
      A strategy hwin rightState rightReceiver rightFibre oldLeft newLeft
        oldPacket leftMove hleftMove oneCoordinates twoCoordinates
          hrightCoordinate hrightFibre hsourceInvariant inputOne inputTwo
  have hcurrentOpen :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged A
        strategy hwin rightState rightReceiver rightFibre oldLeft newLeft
          oldPacket leftMove hleftMove oneCoordinates twoCoordinates
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrent]
  have hreceiveOpen :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (currentPhase.ownerFibreReceive A strategy hwin
          (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentOpen]
  have hopen :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr (member, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 =
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
      profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive,
      hreceiveOpen]
  refine ⟨hsource, ?_⟩
  rw [hopen]
  exact hbase.2

/-- The opposite-direction exit from installed/staged.  Process one opens a
fresh right owner fibre while process two turns the staged packet into an
installed left owner. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_installedStaged
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightCoordinate : twoCoordinates.1 = rightState)
    (hsourceInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          oldPacket.successor,
          (leftMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftInitial),
      oldPacket.successor, (leftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged A
        strategy hwin rightState rightReceiver rightOwner leftTemplate
          oldPacket leftMove hleftMove oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase, leftInitial] using hsourceInvariant
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove
      (leftMove.memberController A false).initial leftInitial.2.1
        leftInitial.2.2.1 (inputOne, inputTwo)).2
  let leftAdvancedOwner :=
    (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove false
      (leftMove.memberController A false).initial inputTwo).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightReceiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
        false rightOwner inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightReceiver.1.memberController A false).labelOf rightOwner).2
          rightReceiver.2.2.1 (inputTwo, inputOne) |>.target
            rightReceiver.2.1)
  let nextLeftMove := packet.successor.2.1.2.2.getD leftMove
  let nextNewLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A nextLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(oldPacket.successor, ⟨leftAdvanced, leftAdvancedOwner⟩,
        rightNext.receiverAt A rightReceiver),
      rightState, rightNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 =
        (.inr
            (false,
              (rightNext,
                ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ()),
          (rightState, oldPacket.successor)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase, leftInitial,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
      profiledRawJointRecurrentRightToLeftPhaseLiveShared,
      profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentRightToLeftMove,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      initialProfiledRawJointLeftPhysicalSiblingReceiver,
      leftAdvanced, rightNext, rightAdvancedOwner, packet, nextNewLeft,
      nextLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 =
        (.inl
            (.inr
              (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
                rightReceiver)),
          twoCoordinates) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
      profiledRawJointRecurrentRightToLeftBridgeNoRecv, hleftMove,
      leftAdvancedOwner]
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext,
                ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ()),
            (rightState, oldPacket.successor))
          (.inl
            (.inr
              (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
                rightReceiver)),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase, hrightCoordinate] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_openFibreInstalled
        A strategy hwin oldPacket.successor leftAdvanced leftAdvancedOwner
          rightReceiver rightNext nextNewLeft (rightState, oldPacket.successor)
            twoCoordinates
  have hleftStepped :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        ((currentPhase.dormantLeftData A strategy hwin).step A strategy hwin
          (inputOne, inputTwo)) := by
    exact hcurrentInvariant.2.step A strategy hwin
      (currentPhase.dormantLeftData A strategy hwin) (inputOne, inputTwo)
  have hleftActive :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (oldPacket.successor,
          ⟨leftAdvanced, leftAdvancedOwner⟩, rightReceiver) := by
    simpa only [currentPhase, leftInitial, leftAdvanced, leftAdvancedOwner,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      initialProfiledRawJointLeftPhysicalSiblingReceiver] using hleftStepped
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hcurrentInvariant.1.advancedOwnerFibreControl_valid A strategy hwin
          currentPhase.1 inputOne
  have hactiveCopy := hcurrentInvariant.1
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, _past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightMonitor⟩
  have hrightNextMove : rightState.2.1.2.1 = some rightNext.1 := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using hrightMove
  have hnextInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreInstalled
        A strategy hwin oldPacket.successor leftAdvanced leftAdvancedOwner
          rightReceiver rightNext rightState hleftActive hrightNext hrightState
            rightCode hrightCode rightRoot hrightRoot hrightNextMove
  exact .left nextPhase (by
    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]) hnextDecode
      hnextInvariant

/-- Mirrored opposite-direction exit from staged/installed.  Process one
installs the right owner carried by the staged packet, while process two
opens a fresh left owner fibre. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_stagedInstalled
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.2.1 = some rightMove)
    (hsourceInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          oldPacket.successor,
          (rightMove.memberController A false).initial⟩)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (honeLeftState : oneCoordinates.2 = leftState)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl (.inl (leftState, leftReceiver, some oldPacket)), oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩, rightInitial),
      oldPacket.successor, (rightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, rightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled A
        strategy hwin leftState leftReceiver leftOwner rightTemplate oldPacket
          rightMove hrightMove oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    rfl
  have hcurrentInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase, rightInitial] using hsourceInvariant
  refine
    ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentInvariant, ?_⟩
  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove
      (rightMove.memberController A false).initial rightInitial.2.1
        rightInitial.2.2.1 (inputTwo, inputOne)).2
  let rightAdvancedOwner :=
    (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove false
      (rightMove.memberController A false).initial inputOne).2
  let leftAdvancedOwner :
      ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false leftOwner inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftReceiver.1.memberController A false).labelOf leftOwner).2
          leftReceiver.2.2.1 (inputOne, inputTwo) |>.target leftReceiver.2.1)
  let nextRightMove := packet.successor.2.1.2.1.getD rightMove
  let nextNewRight :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A nextRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(oldPacket.successor, ⟨rightAdvanced, rightAdvancedOwner⟩,
        leftNext.receiverAt A leftReceiver),
      leftState, leftNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne).1 =
        (.inl
            (.inr
              (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩,
                leftReceiver)),
          oneCoordinates) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
      profiledRawJointRecurrentLeftToRightBridgeNoRecv, hrightMove,
      rightAdvancedOwner]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (leftNext,
                ⟨(oldPacket.successor, rightAdvanced), nextNewRight⟩), ()),
          (oldPacket.successor, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase, rightInitial,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
      profiledRawJointRecurrentLeftToRightPhaseLiveShared,
      profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentLeftToRightMove,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      initialProfiledRawJointRightPhysicalSiblingReceiver,
      rightAdvanced, leftNext, leftAdvancedOwner, packet, nextNewRight,
      nextRightMove]
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩,
                leftReceiver)),
            oneCoordinates)
          (.inr
            (false,
              (leftNext,
                ⟨(oldPacket.successor, rightAdvanced), nextNewRight⟩), ()),
            (oldPacket.successor, leftState)) = some nextPhase := by
    have hdecode :=
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre A
        strategy hwin oldPacket.successor rightAdvanced rightAdvancedOwner
          leftReceiver leftNext nextNewRight oneCoordinates
            (oldPacket.successor, leftState)
    rw [honeLeftState] at hdecode
    simpa only [nextPhase] using hdecode
  have hrightStepped :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        ((currentPhase.dormantRightData A strategy hwin).step A strategy hwin
          (inputOne, inputTwo)) := by
    exact hcurrentInvariant.2.step A strategy hwin
      (currentPhase.dormantRightData A strategy hwin) (inputOne, inputTwo)
  have hrightActive :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (oldPacket.successor,
          ⟨rightAdvanced, rightAdvancedOwner⟩, leftReceiver) := by
    simpa only [currentPhase, rightInitial, rightAdvanced,
      rightAdvancedOwner,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      initialProfiledRawJointRightPhysicalSiblingReceiver] using hrightStepped
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        hcurrentInvariant.1.advancedOwnerFibreControl_valid A strategy hwin
          currentPhase.1 inputTwo
  have hactiveCopy := hcurrentInvariant.1
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, _past, hleftState, hleftCode, hleftRoot,
      hleftMove, _hleftOwner, _hleftMonitor⟩
  have hleftNextMove : leftState.2.1.2.2 = some leftNext.1 := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using hleftMove
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_installedFibre
        A strategy hwin oldPacket.successor rightAdvanced rightAdvancedOwner
          leftReceiver leftNext leftState hrightActive hleftNext hleftState
            leftCode hleftCode leftRoot hleftRoot hleftNextMove
  exact .right nextPhase hnextDecode hnextInvariant

end

end DetParityAutomaton

end DistributedSynthesis
