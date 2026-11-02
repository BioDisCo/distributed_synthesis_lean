/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalController

/-!
# Bank-coordinate completion of the recurrent local controller

The first boundary controller has correct one-round forks but loses the bank
coordinate belonging to a dormant orientation.  The loss is observable after
a simultaneous close followed immediately by the opposite strict direction:
both endpoints are deferred and the original decoders reject the pair.

This file tests the first finite-state repair of that interface.  Each
endpoint carries one finite bank coordinate for each orientation.  A
receiving endpoint may copy the coordinate contained in the delivered finite
control.  This repairs decoding and bank-state recovery, but not by itself
the receiver-timing defect: the old complementary map retains the dormant
receiver instead of advancing the selected open receiver on the boundary
input.  Accordingly the constructions below are diagnostic infrastructure,
not yet a recurrent relation law.  No transition is given a graph, a semantic
source, a history, or a proof witness.
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

/-- The two bank coordinates associated with the two dormant orientations. -/
abbrev ProfiledRawJointRecurrentBoundaryBankCoordinates :=
  BankControl A strategy hwin × BankControl A strategy hwin

/-- Process one's original finite boundary state, completed by its right and
left bank coordinates, in that order. -/
abbrev ProfiledRawJointRecurrentTrackedBoundaryOneControl :=
  ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin ×
    ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin

/-- Process-two mirror. -/
abbrev ProfiledRawJointRecurrentTrackedBoundaryTwoControl :=
  ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin ×
    ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin) := by
  classical
  infer_instance

/-! ## Eight-shape tracked decoder -/

private noncomputable def profiledRawJointRecurrentTrackedAlignRight?
    (state : BankControl A strategy hwin)
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    Option (ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) := by
  classical
  rcases owner with ⟨ownerMove, ownerControl⟩
  rcases receiver with ⟨receiverMove, row, receiverState, target⟩
  by_cases hmove : receiverMove = ownerMove
  · subst receiverMove
    exact some
      (state, ⟨⟨ownerMove, row, receiverState, target⟩, ownerControl⟩,
        oldReceiver)
  · exact none

private noncomputable def profiledRawJointRecurrentTrackedAlignLeft?
    (state : BankControl A strategy hwin)
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    Option (ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) := by
  classical
  rcases owner with ⟨ownerMove, ownerControl⟩
  rcases receiver with ⟨receiverMove, row, receiverState, target⟩
  by_cases hmove : receiverMove = ownerMove
  · subst receiverMove
    exact some
      (state, ⟨⟨ownerMove, row, receiverState, target⟩, ownerControl⟩,
        oldReceiver)
  · exact none

/-- Decode the explicit, installed/deferred, deferred/deferred, and
deferred/staged right shapes.  In a deferred/deferred pair the member pattern
`(true,false)` says that the old right owner and old right receiver are the
selected pair. -/
noncomputable def profiledRawJointRecurrentTrackedRightBoundaryData?
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin) :
    Option (ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) :=
  match one.1, two.1 with
  | .inl (.inr installed), .inl (.inl staged) =>
      profiledRawJointRecurrentTrackedAlignRight? A strategy hwin one.2.1
        installed.2.1 staged.2.1 installed.2.2
  | .inl (.inr installed), .inr deferred =>
      let receiver := if deferred.1 then
          initialProfiledRawJointRightPhysicalSiblingReceiver A
            installed.2.1.1 .both
        else deferred.2.2
      let state := if deferred.1 then one.2.1 else two.2.1
      profiledRawJointRecurrentTrackedAlignRight? A strategy hwin state
        installed.2.1 receiver installed.2.2
  | .inr deferredOne, .inr deferredTwo =>
      if deferredOne.1 && !deferredTwo.1 then
        profiledRawJointRecurrentTrackedAlignRight? A strategy hwin one.2.1
          deferredOne.2.1 deferredTwo.2.2 deferredOne.2.2
      else none
  | .inr deferred, .inl (.inl staged) =>
      if deferred.1 then
        profiledRawJointRecurrentTrackedAlignRight? A strategy hwin one.2.1
          deferred.2.1 staged.2.1 deferred.2.2
      else none
  | _, _ => none

/-- Mirrored four-shape decoder.  Its deferred/deferred member pattern is
`(false,true)`, disjoint from the right pattern. -/
noncomputable def profiledRawJointRecurrentTrackedLeftBoundaryData?
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin) :
    Option (ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) :=
  match one.1, two.1 with
  | .inl (.inl staged), .inl (.inr installed) =>
      profiledRawJointRecurrentTrackedAlignLeft? A strategy hwin two.2.2
        installed.2.1 staged.2.1 installed.2.2
  | .inr deferred, .inl (.inr installed) =>
      let receiver := if deferred.1 then
          initialProfiledRawJointLeftPhysicalSiblingReceiver A
            installed.2.1.1 .both
        else deferred.2.2
      let state := if deferred.1 then two.2.2 else one.2.2
      profiledRawJointRecurrentTrackedAlignLeft? A strategy hwin state
        installed.2.1 receiver installed.2.2
  | .inr deferredOne, .inr deferredTwo =>
      if !deferredOne.1 && deferredTwo.1 then
        profiledRawJointRecurrentTrackedAlignLeft? A strategy hwin two.2.2
          deferredTwo.2.1 deferredOne.2.2 deferredTwo.2.2
      else none
  | .inl (.inl staged), .inr deferred =>
      if deferred.1 then
        profiledRawJointRecurrentTrackedAlignLeft? A strategy hwin two.2.2
          deferred.2.1 staged.2.1 deferred.2.2
      else none
  | _, _ => none

/-! ## The right-oriented pending/pending shape -/

@[simp] theorem
    profiledRawJointRecurrentTrackedRightBoundaryData?_deferredDeferred
    (rightState leftStateOne leftStateTwo : BankControl A strategy hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (oldLeftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldLeftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A) :
    profiledRawJointRecurrentTrackedRightBoundaryData? A strategy hwin
      ((.inr
          (true,
            (⟨move, owner⟩ : ProfiledRawJointRightPhysicalSiblingExceptional A),
            oldLeftReceiver)),
        rightState, leftStateOne)
      ((.inr
          (false, oldLeftOwner,
            (⟨move, row, receiverState, target⟩ :
              ProfiledRawJointRightPhysicalSiblingReceiver A))),
        rightState, leftStateTwo) =
      some
        (rightState,
          ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldLeftReceiver) := by
  simp [profiledRawJointRecurrentTrackedRightBoundaryData?,
    profiledRawJointRecurrentTrackedAlignRight?]

@[simp] theorem
    profiledRawJointRecurrentTrackedLeftBoundaryData?_deferredDeferred
    (rightStateOne rightStateTwo leftState : BankControl A strategy hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (oldRightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldRightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A) :
    profiledRawJointRecurrentTrackedLeftBoundaryData? A strategy hwin
      ((.inr
          (false, oldRightOwner,
            (⟨move, row, receiverState, target⟩ :
              ProfiledRawJointLeftPhysicalSiblingReceiver A))),
        rightStateOne, leftState)
      ((.inr
          (true,
            (⟨move, owner⟩ : ProfiledRawJointLeftPhysicalSiblingExceptional A),
            oldRightReceiver)),
        rightStateTwo, leftState) =
      some
        (leftState,
          ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldRightReceiver) := by
  simp [profiledRawJointRecurrentTrackedLeftBoundaryData?,
    profiledRawJointRecurrentTrackedAlignLeft?]

/-- The two deferred/deferred orientations are separated by their locally
stored member bits; the right shape cannot also decode as left. -/
@[simp] theorem
    profiledRawJointRecurrentTrackedLeftBoundaryData?_rightDeferredDeferred
    (rightStateOne rightStateTwo leftStateOne leftStateTwo :
      BankControl A strategy hwin)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldLeftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldRightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentTrackedLeftBoundaryData? A strategy hwin
      ((.inr (true, rightOwner, oldLeftReceiver)),
        rightStateOne, leftStateOne)
      ((.inr (false, leftOwner, oldRightReceiver)),
        rightStateTwo, leftStateTwo) = none :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentTrackedRightBoundaryData?_deferredStaged
    (rightState leftStateOne leftStateTwo : BankControl A strategy hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (packet : Option
      (ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin))
    (oldLeftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentTrackedRightBoundaryData? A strategy hwin
      ((.inr
          (true,
            (⟨move, owner⟩ : ProfiledRawJointRightPhysicalSiblingExceptional A),
            oldLeftReceiver)),
        rightState, leftStateOne)
      ((.inl (.inl
          (rightState,
            (⟨move, row, receiverState, target⟩ :
              ProfiledRawJointRightPhysicalSiblingReceiver A), packet))),
        rightState, leftStateTwo) =
      some
        (rightState,
          ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldLeftReceiver) := by
  simp [profiledRawJointRecurrentTrackedRightBoundaryData?,
    profiledRawJointRecurrentTrackedAlignRight?]

@[simp] theorem
    profiledRawJointRecurrentTrackedLeftBoundaryData?_stagedDeferred
    (rightStateOne rightStateTwo leftState : BankControl A strategy hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (packet : Option
      (ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin))
    (oldRightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentTrackedLeftBoundaryData? A strategy hwin
      ((.inl (.inl
          (leftState,
            (⟨move, row, receiverState, target⟩ :
              ProfiledRawJointLeftPhysicalSiblingReceiver A), packet))),
        rightStateOne, leftState)
      ((.inr
          (true,
            (⟨move, owner⟩ : ProfiledRawJointLeftPhysicalSiblingExceptional A),
            oldRightReceiver)),
        rightStateTwo, leftState) =
      some
        (leftState,
          ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldRightReceiver) := by
  simp [profiledRawJointRecurrentTrackedLeftBoundaryData?,
    profiledRawJointRecurrentTrackedAlignLeft?]

/-! ## Total tracked transition maps -/

/-- Advance the aligned right owner and receiver through one strict-right
round while retaining the dormant left receiver. -/
noncomputable def ProfiledRawJointRecurrentRightBoundaryData.step
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
  let receiver := data.receiver A strategy hwin
  let ownerNext := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    receiver.1 false (data.owner A strategy hwin) input.1
  let receiverNext := stepProfiledRawJointRightPhysicalSiblingReceiverFor A
    receiver.1 (data.owner A strategy hwin) receiver.2.1 receiver.2.2.1
      (input.2, input.1)
  (data.1, ⟨receiverNext.2, ownerNext.2⟩, data.2.2)

/-- Left-oriented mirror. -/
noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.step
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
  let receiver := data.receiver A strategy hwin
  let ownerNext := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    receiver.1 false (data.owner A strategy hwin) input.2
  let receiverNext := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A
    receiver.1 (data.owner A strategy hwin) receiver.2.1 receiver.2.2.1 input
  (data.1, ⟨receiverNext.2, ownerNext.2⟩, data.2.2)

/-- Matched-prefix reachability is inductive through a strict-right round. -/
theorem ProfiledRawJointRecurrentRightBoundaryInvariant.step
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
      (data.step A strategy hwin input) := by
  rcases data with ⟨state, ⟨⟨move, row, receiverState, lastTarget⟩,
    owner⟩, oldReceiver⟩
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
    ProfiledRawJointRecurrentRightBoundaryData.receiver,
    ProfiledRawJointRecurrentRightBoundaryData.owner] at hinvariant
  rcases hinvariant with
    ⟨currentCode, root, past, hreachable, hcurrentCode, hroot, hmove,
      howner, hreceiverState⟩
  subst owner
  subst receiverState
  refine ⟨currentCode, root, past ++ [(input.2, input.1)], hreachable,
    hcurrentCode, hroot, hmove, ?_, ?_⟩
  · dsimp only [ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      profiledRawJointRightPhysicalSiblingMemberNoRecvStep]
    rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · dsimp only [ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      stepProfiledRawJointRightPhysicalSiblingReceiverFor]
    rw [narrowedControl_append]
    simp [narrowedRecord, TransitionRationalTree.labeledTree]

/-- Matched-prefix reachability is inductive through a strict-left round. -/
theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.step
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
      (data.step A strategy hwin input) := by
  rcases data with ⟨state, ⟨⟨move, row, receiverState, lastTarget⟩,
    owner⟩, oldReceiver⟩
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant,
    ProfiledRawJointRecurrentLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentLeftBoundaryData.owner] at hinvariant
  rcases hinvariant with
    ⟨currentCode, root, past, hreachable, hcurrentCode, hroot, hmove,
      howner, hreceiverState⟩
  subst owner
  subst receiverState
  refine ⟨currentCode, root, past ++ [input], hreachable, hcurrentCode,
    hroot, hmove, ?_, ?_⟩
  · dsimp only [ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      profiledRawJointLeftPhysicalSiblingMemberNoRecvStep]
    rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · dsimp only [ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      stepProfiledRawJointLeftPhysicalSiblingReceiverFor]
    rw [narrowedControl_append]
    simp [narrowedRecord, TransitionRationalTree.labeledTree]

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.target
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  let receiver := data.receiver A strategy hwin
  (((receiver.1.memberController A false).labelOf
      (data.owner A strategy hwin)).2 receiver.2.2.1
        (input.2, input.1) |>.target receiver.2.1)

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.successor
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (input : In₁ × In₂) : BankControl A strategy hwin :=
  profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
    data.1
    (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
      hwin data.1 (data.target A strategy hwin input))

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.target
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  let receiver := data.receiver A strategy hwin
  (((receiver.1.memberController A false).labelOf
      (data.owner A strategy hwin)).2 receiver.2.2.1 input |>.target
        receiver.2.1)

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.successor
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (input : In₁ × In₂) : BankControl A strategy hwin :=
  profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
    data.1
    (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
      hwin data.1 (data.target A strategy hwin input))

/-- A no-receive advances the original finite boundary state and preserves
both dormant bank coordinates. -/
noncomputable def profiledRawJointRecurrentTrackedBoundaryNoRecvOne
    (control :
      ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin ×
      Out₁ :=
  let next := profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin
    control.1 input
  ((next.1, control.2), next.2)

noncomputable def profiledRawJointRecurrentTrackedBoundaryNoRecvTwo
    (control :
      ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin ×
      Out₂ :=
  let next := profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin
    control.1 input
  ((next.1, control.2), next.2)

/-- Decode one of the six tracked shapes and create the two endpoint-local
forks.  The open receiver copies the bank coordinate visible in the
delivered finite control; the closed candidates retain the newly resolved
successor at both endpoints. -/
noncomputable def profiledRawJointRecurrentTrackedBoundaryReceive?
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (input : In₁ × In₂) :
    Option
      ((FiniteDelayedFork
          (ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy
            hwin) × Out₁) ×
        (FiniteDelayedFork
          (ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy
            hwin) × Out₂)) :=
  match profiledRawJointRecurrentTrackedRightBoundaryData? A strategy hwin one
      two with
  | some data =>
      let base := data.receive A strategy hwin input
      let successor := data.successor A strategy hwin input
      let oneFork :=
        (⟨(base.1.1.openControl, data.1, two.2.2),
          (base.1.1.closedControl, data.1, successor)⟩ :
          FiniteDelayedFork
            (ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy
              hwin))
      let twoFork :=
        (⟨(base.2.1.openControl, data.1, successor),
          (base.2.1.closedControl, data.1, successor)⟩ :
          FiniteDelayedFork
            (ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy
              hwin))
      some ((oneFork, base.1.2), (twoFork, base.2.2))
  | none =>
      match profiledRawJointRecurrentTrackedLeftBoundaryData? A strategy hwin
          one two with
      | some data =>
          let base := data.receive A strategy hwin input
          let successor := data.successor A strategy hwin input
          let oneFork :=
            (⟨(base.1.1.openControl, successor, data.1),
              (base.1.1.closedControl, successor, data.1)⟩ :
              FiniteDelayedFork
                (ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy
                  hwin))
          let twoFork :=
            (⟨(base.2.1.openControl, one.2.1, data.1),
              (base.2.1.closedControl, successor, data.1)⟩ :
              FiniteDelayedFork
                (ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy
                  hwin))
          some ((oneFork, base.1.2), (twoFork, base.2.2))
      | none => none

noncomputable def profiledRawJointRecurrentTrackedBoundaryOpenRecvOne
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin ×
      Out₁ :=
  match profiledRawJointRecurrentTrackedBoundaryReceive? A strategy hwin one
      two (inputOne, inputTwo) with
  | some result => (result.1.1.openControl, result.1.2)
  | none =>
      profiledRawJointRecurrentTrackedBoundaryNoRecvOne A strategy hwin one
        inputOne

noncomputable def profiledRawJointRecurrentTrackedBoundaryOpenRecvTwo
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (inputOne : In₁) :
    ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin ×
      Out₂ :=
  match profiledRawJointRecurrentTrackedBoundaryReceive? A strategy hwin one
      two (inputOne, inputTwo) with
  | some result => (result.2.1.openControl, result.2.2)
  | none =>
      profiledRawJointRecurrentTrackedBoundaryNoRecvTwo A strategy hwin two
        inputTwo

noncomputable def profiledRawJointRecurrentTrackedBoundaryClose
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin ×
      ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin :=
  match profiledRawJointRecurrentTrackedBoundaryReceive? A strategy hwin one
      two (inputOne, inputTwo) with
  | some result =>
      (result.1.1.closedControl, result.2.1.closedControl)
  | none =>
      ((profiledRawJointRecurrentTrackedBoundaryNoRecvOne A strategy hwin one
        inputOne).1,
       (profiledRawJointRecurrentTrackedBoundaryNoRecvTwo A strategy hwin two
        inputTwo).1)

/-! ## Blind laws survive bank-coordinate completion -/

def ProfiledRawJointRecurrentTrackedBoundaryOneBlind
    (left right :
      ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin left.1 right.1

def ProfiledRawJointRecurrentTrackedBoundaryTwoBlind
    (left right :
      ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin left.1 right.1

theorem profiledRawJointRecurrentTrackedBoundaryOneBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (input : In₁)
    (hblind : ProfiledRawJointRecurrentTrackedBoundaryOneBlind A strategy hwin
      left right) :
    (profiledRawJointRecurrentTrackedBoundaryNoRecvOne A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentTrackedBoundaryNoRecvOne A strategy hwin
          right input).2 ∧
      ProfiledRawJointRecurrentTrackedBoundaryOneBlind A strategy hwin
        (profiledRawJointRecurrentTrackedBoundaryNoRecvOne A strategy hwin
          left input).1
        (profiledRawJointRecurrentTrackedBoundaryNoRecvOne A strategy hwin
          right input).1 := by
  exact profiledRawJointRecurrentBoundaryOneBlind_noRecv A strategy hwin
    left.1 right.1 input hblind

theorem profiledRawJointRecurrentTrackedBoundaryTwoBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (input : In₂)
    (hblind : ProfiledRawJointRecurrentTrackedBoundaryTwoBlind A strategy hwin
      left right) :
    (profiledRawJointRecurrentTrackedBoundaryNoRecvTwo A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentTrackedBoundaryNoRecvTwo A strategy hwin
          right input).2 ∧
      ProfiledRawJointRecurrentTrackedBoundaryTwoBlind A strategy hwin
        (profiledRawJointRecurrentTrackedBoundaryNoRecvTwo A strategy hwin
          left input).1
        (profiledRawJointRecurrentTrackedBoundaryNoRecvTwo A strategy hwin
          right input).1 := by
  exact profiledRawJointRecurrentBoundaryTwoBlind_noRecv A strategy hwin
    left.1 right.1 input hblind

noncomputable def profiledRawJointRecurrentTrackedBoundaryBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentTrackedBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentTrackedBoundaryNoRecvTwo A strategy hwin)
      (ProfiledRawJointRecurrentTrackedBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentTrackedBoundaryTwoBlind A strategy hwin) where
  one := profiledRawJointRecurrentTrackedBoundaryOneBlind_noRecv A strategy
    hwin
  two := profiledRawJointRecurrentTrackedBoundaryTwoBlind_noRecv A strategy
    hwin

/-! ## Non-vacuous tracked selection and receive closure -/

theorem profiledRawJointRecurrentTrackedBoundaryReceive?_of_right
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hdata : profiledRawJointRecurrentTrackedRightBoundaryData? A strategy hwin
      one two = some data)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentTrackedBoundaryReceive? A strategy hwin one two
        input =
      let base := data.receive A strategy hwin input
      let successor := data.successor A strategy hwin input
      let oneFork :=
        (⟨(base.1.1.openControl, data.1, two.2.2),
          (base.1.1.closedControl, data.1, successor)⟩ :
          FiniteDelayedFork
            (ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy
              hwin))
      let twoFork :=
        (⟨(base.2.1.openControl, data.1, successor),
          (base.2.1.closedControl, data.1, successor)⟩ :
          FiniteDelayedFork
            (ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy
              hwin))
      some ((oneFork, base.1.2), (twoFork, base.2.2)) := by
  simp [profiledRawJointRecurrentTrackedBoundaryReceive?, hdata]

theorem profiledRawJointRecurrentTrackedBoundaryReceive?_of_left
    (one : ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin)
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hright : profiledRawJointRecurrentTrackedRightBoundaryData? A strategy
      hwin one two = none)
    (hdata : profiledRawJointRecurrentTrackedLeftBoundaryData? A strategy hwin
      one two = some data)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentTrackedBoundaryReceive? A strategy hwin one two
        input =
      let base := data.receive A strategy hwin input
      let successor := data.successor A strategy hwin input
      let oneFork :=
        (⟨(base.1.1.openControl, successor, data.1),
          (base.1.1.closedControl, successor, data.1)⟩ :
          FiniteDelayedFork
            (ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy
              hwin))
      let twoFork :=
        (⟨(base.2.1.openControl, one.2.1, data.1),
          (base.2.1.closedControl, successor, data.1)⟩ :
          FiniteDelayedFork
            (ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy
              hwin))
      some ((oneFork, base.1.2), (twoFork, base.2.2)) := by
  simp [profiledRawJointRecurrentTrackedBoundaryReceive?, hright, hdata]

inductive ProfiledRawJointRecurrentTrackedBoundarySelected :
    ProfiledRawJointRecurrentTrackedBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentTrackedBoundaryTwoControl A strategy hwin →
        Prop
  | right {one two}
      (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
      (hdata : profiledRawJointRecurrentTrackedRightBoundaryData? A strategy
        hwin one two = some data)
      (invariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
        hwin data) :
      ProfiledRawJointRecurrentTrackedBoundarySelected one two
  | left {one two}
      (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
      (hright : profiledRawJointRecurrentTrackedRightBoundaryData? A strategy
        hwin one two = none)
      (hdata : profiledRawJointRecurrentTrackedLeftBoundaryData? A strategy
        hwin one two = some data)
      (invariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
        hwin data) :
      ProfiledRawJointRecurrentTrackedBoundarySelected one two

/-- Adding the two bank coordinates preserves the exact blind receive law.
The non-vacuous matched-prefix invariant still discharges target realization
and the live crossed slot. -/
theorem profiledRawJointRecurrentTrackedBoundaryBlindReceiveLaws :
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindReceiveLaws
      (profiledRawJointRecurrentTrackedBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentTrackedBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentTrackedBoundaryClose A strategy hwin)
      (ProfiledRawJointRecurrentTrackedBoundarySelected A strategy hwin)
      (ProfiledRawJointRecurrentTrackedBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentTrackedBoundaryTwoBlind A strategy hwin) where
  one := by
    intro one inputOne two inputTwo hselected
    cases hselected with
    | right data hdata invariant =>
        have ready :=
          profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentTrackedBoundaryReceive?_of_right A strategy
            hwin one two data hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentRightToLeftBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentTrackedBoundaryOpenRecvOne,
          profiledRawJointRecurrentTrackedBoundaryClose, hreceive,
          ProfiledRawJointRecurrentTrackedBoundaryOneBlind]
        exact hspec.2.2.1
    | left data hright hdata invariant =>
        have ready :=
          profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentTrackedBoundaryReceive?_of_left A strategy
            hwin one two data hright hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentLeftToRightBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentTrackedBoundaryOpenRecvOne,
          profiledRawJointRecurrentTrackedBoundaryClose, hreceive,
          ProfiledRawJointRecurrentTrackedBoundaryOneBlind]
        exact hspec.2.2.1
  two := by
    intro one inputOne two inputTwo hselected
    cases hselected with
    | right data hdata invariant =>
        have ready :=
          profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentTrackedBoundaryReceive?_of_right A strategy
            hwin one two data hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentRightToLeftBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentTrackedBoundaryOpenRecvTwo,
          profiledRawJointRecurrentTrackedBoundaryClose, hreceive,
          ProfiledRawJointRecurrentTrackedBoundaryTwoBlind]
        exact hspec.2.2.2
    | left data hright hdata invariant =>
        have ready :=
          profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentTrackedBoundaryReceive?_of_left A strategy
            hwin one two data hright hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentLeftToRightBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentTrackedBoundaryOpenRecvTwo,
          profiledRawJointRecurrentTrackedBoundaryClose, hreceive,
          ProfiledRawJointRecurrentTrackedBoundaryTwoBlind]
        exact hspec.2.2.2

end

end DetParityAutomaton

end DistributedSynthesis
