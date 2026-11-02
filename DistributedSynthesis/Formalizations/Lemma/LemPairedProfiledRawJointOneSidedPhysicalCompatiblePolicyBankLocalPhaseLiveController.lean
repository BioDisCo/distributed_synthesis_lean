/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveDecoder

/-!
# Corrected recurrent endpoint controls with phase-live deferred states

The earlier tracked controller kept the obsolete deferred state whose payload
contained only one dormant receiver.  This file replaces that summand by the
bank-linked phase-live state.  Each endpoint is therefore either in its
informed staged/installed bridge or in a member-independent sender state
carrying the complete banked old/new receiver fork.

The first goal is deliberately structural: decode all four right-oriented
and four left-oriented combinations only when both the active and dormant
dependent owner/receiver pairs match.  The immediate deferred/deferred
reversal equations at the end are the principal fail-fast test.
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

/-! ## Corrected endpoint state space -/

abbrev ProfiledRawJointRecurrentPhaseBoundaryOneBase :=
  ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin ⊕
    ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin

abbrev ProfiledRawJointRecurrentPhaseBoundaryTwoBase :=
  ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin ⊕
    ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin

/-- The outer coordinates retain the right and left bank states while a
bridge has only an unbanked dormant receiver.  Phase-live states additionally
retain the exact bank coordinate beside each receiver candidate. -/
abbrev ProfiledRawJointRecurrentPhaseBoundaryOneControl :=
  ProfiledRawJointRecurrentPhaseBoundaryOneBase A strategy hwin ×
    ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin

abbrev ProfiledRawJointRecurrentPhaseBoundaryTwoControl :=
  ProfiledRawJointRecurrentPhaseBoundaryTwoBase A strategy hwin ×
    ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) := by
  classical
  infer_instance

/-! ## Aligned construction helpers -/

/-- Assemble right-oriented phase-live data after checking both dependent
move equalities. -/
private noncomputable def profiledRawJointRecurrentMakeRightPhaseData?
    (state : BankControl A strategy hwin)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftState : BankControl A strategy hwin)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    Option
      (ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) := by
  classical
  rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
  rcases rightReceiver with
    ⟨rightReceiverMove, rightRow, rightReceiverState, rightTarget⟩
  by_cases hright : rightOwnerMove = rightReceiverMove
  · subst rightReceiverMove
    let data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
      (state,
        ⟨⟨rightOwnerMove, rightRow, rightReceiverState, rightTarget⟩,
          rightOwnerControl⟩,
        leftReceiver)
    match profiledRawJointRecurrentAlignDormantLeftOwner? A leftOwner
        leftReceiver with
    | none => exact none
    | some leftOwnerControl => exact some ⟨data, leftState, leftOwnerControl⟩
  · exact none

/-- Mirrored aligned constructor. -/
private noncomputable def profiledRawJointRecurrentMakeLeftPhaseData?
    (state : BankControl A strategy hwin)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightState : BankControl A strategy hwin)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    Option
      (ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) := by
  classical
  rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
  rcases leftReceiver with
    ⟨leftReceiverMove, leftRow, leftReceiverState, leftTarget⟩
  by_cases hleft : leftOwnerMove = leftReceiverMove
  · subst leftReceiverMove
    let data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
      (state,
        ⟨⟨leftOwnerMove, leftRow, leftReceiverState, leftTarget⟩,
          leftOwnerControl⟩,
        rightReceiver)
    match profiledRawJointRecurrentAlignDormantRightOwner? A rightOwner
        rightReceiver with
    | none => exact none
    | some rightOwnerControl =>
        exact some ⟨data, rightState, rightOwnerControl⟩
  · exact none

/-- Extract the initial left owner from a staged right-receiver packet. -/
private noncomputable def profiledRawJointRecurrentStagedLeftOwner?
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin) :
    Option (ProfiledRawJointLeftPhysicalSiblingExceptional A) :=
  match staged.2.2 with
  | none => none
  | some packet =>
      packet.successor.2.1.2.2.map fun move ↦
        ⟨move, (move.memberController A false).initial⟩

/-- Extract the mirrored initial right owner. -/
private noncomputable def profiledRawJointRecurrentStagedRightOwner?
    (staged :
      ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin) :
    Option (ProfiledRawJointRightPhysicalSiblingExceptional A) :=
  match staged.2.2 with
  | none => none
  | some packet =>
      packet.successor.2.1.2.1.map fun move ↦
        ⟨move, (move.memberController A false).initial⟩

/-! ## Eight-shape phase-live decoder -/

/-- Decode a right block.  The four cases are installed/staged,
installed/phase-live, phase-live/phase-live, and phase-live/staged. -/
noncomputable def profiledRawJointRecurrentPhaseRightBoundaryData?
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) :
    Option
      (ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) :=
  match one.1, two.1 with
  | .inl (.inr installed), .inl (.inl staged) =>
      match staged.2.2 with
      | none => none
      | some packet =>
          match packet.successor.2.1.2.2 with
          | none => none
          | some move =>
              let leftReceiver :=
                initialProfiledRawJointLeftPhysicalSiblingReceiver A move
                  .first
              profiledRawJointRecurrentMakeRightPhaseData? A strategy hwin
                installed.1 installed.2.1 staged.2.1 packet.successor
                  ⟨move, (move.memberController A false).initial⟩ leftReceiver
  | .inl (.inr installed), .inr pendingTwo =>
      let rightReceiver :=
        profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
          pendingTwo
      profiledRawJointRecurrentMakeRightPhaseData? A strategy hwin
        rightReceiver.1 installed.2.1 rightReceiver.2 one.2.2 pendingTwo.2.1.1
          installed.2.2
  | .inr pendingOne, .inr pendingTwo =>
      if pendingOne.1 && !pendingTwo.1 then
        let rightReceiver :=
          profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
            pendingTwo
        let leftReceiver :=
          profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
            pendingOne
        profiledRawJointRecurrentMakeRightPhaseData? A strategy hwin
          rightReceiver.1 pendingOne.2.1.1 rightReceiver.2 leftReceiver.1
            pendingTwo.2.1.1 leftReceiver.2
      else none
  | .inr pendingOne, .inl (.inl staged) =>
      if pendingOne.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.2.2 with
            | none => none
            | some move =>
                let leftReceiver :=
                  initialProfiledRawJointLeftPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentMakeRightPhaseData? A strategy hwin
                  staged.1 pendingOne.2.1.1 staged.2.1 packet.successor
                    ⟨move, (move.memberController A false).initial⟩
                      leftReceiver
      else none
  | _, _ => none

/-- Mirrored four-case decoder. -/
noncomputable def profiledRawJointRecurrentPhaseLeftBoundaryData?
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) :
    Option
      (ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) :=
  match one.1, two.1 with
  | .inl (.inl staged), .inl (.inr installed) =>
      match staged.2.2 with
      | none => none
      | some packet =>
          match packet.successor.2.1.2.1 with
          | none => none
          | some move =>
              let rightReceiver :=
                initialProfiledRawJointRightPhysicalSiblingReceiver A move
                  .first
              profiledRawJointRecurrentMakeLeftPhaseData? A strategy hwin
                installed.1 installed.2.1 staged.2.1 packet.successor
                  ⟨move, (move.memberController A false).initial⟩ rightReceiver
  | .inr pendingOne, .inl (.inr installed) =>
      let leftReceiver :=
        profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
          pendingOne
      profiledRawJointRecurrentMakeLeftPhaseData? A strategy hwin
        leftReceiver.1 installed.2.1 leftReceiver.2 two.2.1 pendingOne.2.1.1
          installed.2.2
  | .inr pendingOne, .inr pendingTwo =>
      if !pendingOne.1 && pendingTwo.1 then
        let leftReceiver :=
          profiledRawJointRecurrentRightToLeftPhaseLiveReceiver A strategy hwin
            pendingOne
        let rightReceiver :=
          profiledRawJointRecurrentLeftToRightPhaseLiveReceiver A strategy hwin
            pendingTwo
        profiledRawJointRecurrentMakeLeftPhaseData? A strategy hwin
          leftReceiver.1 pendingTwo.2.1.1 leftReceiver.2 rightReceiver.1
            pendingOne.2.1.1 rightReceiver.2
      else none
  | .inl (.inl staged), .inr pendingTwo =>
      if pendingTwo.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.2.1 with
            | none => none
            | some move =>
                let rightReceiver :=
                  initialProfiledRawJointRightPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentMakeLeftPhaseData? A strategy hwin
                  staged.1 pendingTwo.2.1.1 staged.2.1 packet.successor
                    ⟨move, (move.memberController A false).initial⟩
                      rightReceiver
      else none
  | _, _ => none

/-! ## Exact immediate-reversal equations -/

/-- Canonical left-oriented phase/installed decoding.  The true member selects
the closed left receiver, while the shared right sender supplies the matching
dormant owner. -/
@[simp] theorem
    profiledRawJointRecurrentPhaseLeftBoundaryData?_phaseInstalled
    (rightState leftState : BankControl A strategy hwin)
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
    (leftTarget : Option (ProfiledRawJointUnitTarget A))
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A :=
      ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
    let leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A :=
      ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin :=
      (true,
        (⟨rightMove, rightOwner⟩,
          ⟨oldLeft, (leftState, leftReceiver)⟩), ())
    profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl (.inr (leftState, ⟨leftMove, leftOwner⟩, rightReceiver)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩, rightReceiver),
          twoCoordinates.1, rightOwner⟩ := by
  simp [profiledRawJointRecurrentPhaseLeftBoundaryData?,
    profiledRawJointRecurrentMakeLeftPhaseData?,
    profiledRawJointRecurrentAlignDormantRightOwner?,
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver]

/-- Receiver-packaged form of the preceding equation. -/
@[simp] theorem
    profiledRawJointRecurrentPhaseLeftBoundaryData?_phaseInstalledReceiver
    (rightState leftState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin :=
      (true,
        (⟨rightReceiver.1, rightOwner⟩,
          ⟨oldLeft, (leftState, leftReceiver)⟩), ())
    profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightReceiver)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩, rightReceiver),
          twoCoordinates.1, rightOwner⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  exact
    profiledRawJointRecurrentPhaseLeftBoundaryData?_phaseInstalled A strategy
      hwin rightState leftState rightMove rightOwner rightRow
        rightReceiverState rightTarget leftMove leftOwner leftRow
          leftReceiverState leftTarget oldLeft oneCoordinates twoCoordinates

/-- Canonical right-oriented installed/phase decoding.  The false member
selects the open right receiver; the shared left sender supplies the dormant
left owner. -/
@[simp] theorem
    profiledRawJointRecurrentPhaseRightBoundaryData?_installedPhase
    (rightState leftState : BankControl A strategy hwin)
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
    (leftTarget : Option (ProfiledRawJointUnitTarget A))
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A :=
      ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
    let leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A :=
      ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin :=
      (false,
        (⟨leftMove, leftOwner⟩,
          ⟨(rightState, rightReceiver), newRight⟩), ())
    profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
        (.inl (.inr (rightState, ⟨rightMove, rightOwner⟩, leftReceiver)),
          oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftReceiver),
          oneCoordinates.2, leftOwner⟩ := by
  simp [profiledRawJointRecurrentPhaseRightBoundaryData?,
    profiledRawJointRecurrentMakeRightPhaseData?,
    profiledRawJointRecurrentAlignDormantLeftOwner?,
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver]

/-- Receiver-packaged mirrored equation. -/
@[simp] theorem
    profiledRawJointRecurrentPhaseRightBoundaryData?_installedPhaseReceiver
    (rightState leftState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin :=
      (false,
        (⟨leftReceiver.1, leftOwner⟩,
          ⟨(rightState, rightReceiver), newRight⟩), ())
    profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftReceiver)),
          oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftReceiver),
          oneCoordinates.2, leftOwner⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  exact
    profiledRawJointRecurrentPhaseRightBoundaryData?_installedPhase A strategy
      hwin rightState leftState rightMove rightOwner rightRow
        rightReceiverState rightTarget leftMove leftOwner leftRow
          leftReceiverState leftTarget newRight oneCoordinates twoCoordinates

/-- Closed-member version used by an exact left-to-right simultaneous
reversal. -/
@[simp] theorem
    profiledRawJointRecurrentPhaseRightBoundaryData?_installedPhaseClosed
    (rightState leftState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin :=
      (true,
        (⟨leftReceiver.1, leftOwner⟩,
          ⟨oldRight, (rightState, rightReceiver)⟩), ())
    profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftReceiver)),
          oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftReceiver),
          oneCoordinates.2, leftOwner⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  simp [profiledRawJointRecurrentPhaseRightBoundaryData?,
    profiledRawJointRecurrentMakeRightPhaseData?,
    profiledRawJointRecurrentAlignDormantLeftOwner?,
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver]

/-- The phase-live controls close the
right-oriented deferred/deferred shape. -/
@[simp] theorem
    profiledRawJointRecurrentPhaseRightBoundaryData?_deferredDeferred
    (rightState leftState : BankControl A strategy hwin)
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
    (leftTarget : Option (ProfiledRawJointUnitTarget A))
    (rightCoordinates leftCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A :=
      ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
    let leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A :=
      ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
    let onePending :
        ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin :=
      (true,
        (⟨rightMove, rightOwner⟩,
          ⟨(leftState, leftReceiver), (leftState, leftReceiver)⟩), ())
    let twoPending :
        ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin :=
      (false,
        (⟨leftMove, leftOwner⟩,
          ⟨(rightState, rightReceiver), (rightState, rightReceiver)⟩), ())
    profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
        (.inr onePending, rightCoordinates)
        (.inr twoPending, leftCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftReceiver),
          leftState, leftOwner⟩ := by
  simp [profiledRawJointRecurrentPhaseRightBoundaryData?,
    profiledRawJointRecurrentMakeRightPhaseData?,
    profiledRawJointRecurrentAlignDormantLeftOwner?,
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver,
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver]

/-- Mirrored immediate reversal with member pattern `(false,true)`. -/
@[simp] theorem
    profiledRawJointRecurrentPhaseLeftBoundaryData?_deferredDeferred
    (rightState leftState : BankControl A strategy hwin)
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
    (leftTarget : Option (ProfiledRawJointUnitTarget A))
    (rightCoordinates leftCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A :=
      ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
    let leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A :=
      ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
    let onePending :
        ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin :=
      (false,
        (⟨rightMove, rightOwner⟩,
          ⟨(leftState, leftReceiver), (leftState, leftReceiver)⟩), ())
    let twoPending :
        ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin :=
      (true,
        (⟨leftMove, leftOwner⟩,
          ⟨(rightState, rightReceiver), (rightState, rightReceiver)⟩), ())
    profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin
        (.inr onePending, rightCoordinates)
        (.inr twoPending, leftCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩, rightReceiver),
          rightState, rightOwner⟩ := by
  simp [profiledRawJointRecurrentPhaseLeftBoundaryData?,
    profiledRawJointRecurrentMakeLeftPhaseData?,
    profiledRawJointRecurrentAlignDormantRightOwner?,
    profiledRawJointRecurrentRightToLeftPhaseLiveReceiver,
    profiledRawJointRecurrentLeftToRightPhaseLiveReceiver]

/-! ## Total no-receive maps and blind laws -/

noncomputable def profiledRawJointRecurrentPhaseBoundaryNoRecvOne
    (control :
      ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin × Out₁ :=
  match control.1 with
  | .inl bridge =>
      let next := profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy
        hwin bridge input
      ((.inl next.1, control.2), next.2)
  | .inr pending =>
      let next :=
        profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin
          pending input
      ((.inr next.1, control.2), next.2)

noncomputable def profiledRawJointRecurrentPhaseBoundaryNoRecvTwo
    (control :
      ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin × Out₂ :=
  match control.1 with
  | .inl bridge =>
      let next := profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy
        hwin bridge input
      ((.inl next.1, control.2), next.2)
  | .inr pending =>
      let next :=
        profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin
          pending input
      ((.inr next.1, control.2), next.2)

inductive ProfiledRawJointRecurrentPhaseBoundaryOneBlind :
    ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin → Prop
  | bridge {left right leftCoordinates rightCoordinates}
      (hblind : ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
        left right) :
      ProfiledRawJointRecurrentPhaseBoundaryOneBlind
        (.inl left, leftCoordinates) (.inl right, rightCoordinates)
  | phase {left right leftCoordinates rightCoordinates}
      (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
        right) :
      ProfiledRawJointRecurrentPhaseBoundaryOneBlind
        (.inr left, leftCoordinates) (.inr right, rightCoordinates)

inductive ProfiledRawJointRecurrentPhaseBoundaryTwoBlind :
    ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin →
      ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin → Prop
  | bridge {left right leftCoordinates rightCoordinates}
      (hblind : ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
        left right) :
      ProfiledRawJointRecurrentPhaseBoundaryTwoBlind
        (.inl left, leftCoordinates) (.inl right, rightCoordinates)
  | phase {left right leftCoordinates rightCoordinates}
      (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
        right) :
      ProfiledRawJointRecurrentPhaseBoundaryTwoBlind
        (.inr left, leftCoordinates) (.inr right, rightCoordinates)

theorem profiledRawJointRecurrentPhaseBoundaryOneBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (input : In₁)
    (hblind : ProfiledRawJointRecurrentPhaseBoundaryOneBlind A strategy hwin
      left right) :
    (profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin right
          input).2 ∧
      ProfiledRawJointRecurrentPhaseBoundaryOneBlind A strategy hwin
        (profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin left
          input).1
        (profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin right
          input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentLeftToRightBridgeBlind_noRecv A strategy hwin
          _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | phase hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentRightToLeftPhaseLive_blind_noRecv A strategy
          hwin _ _ input hblind
      exact ⟨hout, .phase hnext⟩

theorem profiledRawJointRecurrentPhaseBoundaryTwoBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (input : In₂)
    (hblind : ProfiledRawJointRecurrentPhaseBoundaryTwoBlind A strategy hwin
      left right) :
    (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin right
          input).2 ∧
      ProfiledRawJointRecurrentPhaseBoundaryTwoBlind A strategy hwin
        (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin left
          input).1
        (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin right
          input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentRightToLeftBridgeBlind_noRecv A strategy hwin
          _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | phase hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentLeftToRightPhaseLive_blind_noRecv A strategy
          hwin _ _ input hblind
      exact ⟨hout, .phase hnext⟩

noncomputable def profiledRawJointRecurrentPhaseBoundaryBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin)
      (ProfiledRawJointRecurrentPhaseBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentPhaseBoundaryTwoBlind A strategy hwin) where
  one := profiledRawJointRecurrentPhaseBoundaryOneBlind_noRecv A strategy hwin
  two := profiledRawJointRecurrentPhaseBoundaryTwoBlind_noRecv A strategy hwin

/-! ## Corrected receive-created forks -/

/-- The informed process-two fork, stated directly in the corrected bridge
summand.  This is the old receiver-side construction without the obsolete
deferred alternative in its codomain. -/
noncomputable def profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin) ×
      Out₂ :=
  let next := profiledRawJointRecurrentRightReceiveFor A strategy hwin state
    receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  let openControl :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin :=
    .inl next.1
  match packet.successor.2.1.2.2 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1)⟩,
        next.2)

/-- Mirrored informed process-one fork. -/
noncomputable def profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin) ×
      Out₁ :=
  let next := profiledRawJointRecurrentLeftReceiveFor A strategy hwin state
    receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  let openControl :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin :=
    .inl next.1
  match packet.successor.2.1.2.1 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1)⟩,
        next.2)

/-- A right-oriented receive advances the dormant old left receiver in the
process-one phase-live fork and advances the active right receiver in the
process-two informed bridge. -/
noncomputable def ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.receive
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin) ×
      Out₁) ×
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) ×
      Out₂) :=
  let data := phaseData.1
  let phaseOne := data.phaseLiveReceive A strategy hwin phaseData.2.1
    phaseData.2.2 input
  let bridgeTwo :=
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin)
        (input.2, input.1)
  let successor := data.successor A strategy hwin input
  let oneFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin) :=
    ⟨(.inr phaseOne.1.openControl, data.1, phaseData.2.1),
      (.inr phaseOne.1.closedControl, data.1, successor)⟩
  let twoFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) :=
    ⟨(.inl bridgeTwo.1.openControl, data.1, successor),
      (.inl bridgeTwo.1.closedControl, data.1, successor)⟩
  ((oneFork, phaseOne.2), (twoFork, bridgeTwo.2))

/-- Left-oriented mirror. -/
noncomputable def ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.receive
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin) ×
      Out₁) ×
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) ×
      Out₂) :=
  let data := phaseData.1
  let bridgeOne :=
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin) input
  let phaseTwo := data.phaseLiveReceive A strategy hwin phaseData.2.1
    phaseData.2.2 input
  let successor := data.successor A strategy hwin input
  let oneFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin) :=
    ⟨(.inl bridgeOne.1.openControl, successor, data.1),
      (.inl bridgeOne.1.closedControl, successor, data.1)⟩
  let twoFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) :=
    ⟨(.inr phaseTwo.1.openControl, phaseData.2.1, data.1),
      (.inr phaseTwo.1.closedControl, successor, data.1)⟩
  ((oneFork, bridgeOne.2), (twoFork, phaseTwo.2))

/-- Total orientation dispatcher. -/
noncomputable def profiledRawJointRecurrentPhaseBoundaryReceive?
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (input : In₁ × In₂) :
    Option
      ((FiniteDelayedFork
          (ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin) ×
        Out₁) ×
      (FiniteDelayedFork
          (ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin) ×
        Out₂)) :=
  match profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin one
      two with
  | some data => some (data.receive A strategy hwin input)
  | none =>
      match profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin one
          two with
      | some data => some (data.receive A strategy hwin input)
      | none => none

noncomputable def profiledRawJointRecurrentPhaseBoundaryOpenRecvOne
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin × Out₁ :=
  match profiledRawJointRecurrentPhaseBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.1.1.openControl, result.1.2)
  | none =>
      profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin one
        inputOne

noncomputable def profiledRawJointRecurrentPhaseBoundaryOpenRecvTwo
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (inputOne : In₁) :
    ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin × Out₂ :=
  match profiledRawJointRecurrentPhaseBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.2.1.openControl, result.2.2)
  | none =>
      profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin two
        inputTwo

noncomputable def profiledRawJointRecurrentPhaseBoundaryClose
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin ×
      ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin :=
  match profiledRawJointRecurrentPhaseBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result =>
      (result.1.1.closedControl, result.2.1.closedControl)
  | none =>
      ((profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin one
        inputOne).1,
       (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin two
        inputTwo).1)

/-! ## Non-vacuous receive-created blind pairs -/

theorem profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
      (profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo A strategy hwin
        state receiver owner input).1.openControl
      (profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo A strategy hwin
        state receiver owner input).1.closedControl := by
  subst target
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin state target hrealizes root hroot
  simp only [profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo, target,
    packet, hmove]
  exact .staged state
    (profiledRawJointRecurrentRightReceiveFor A strategy hwin state receiver
      owner input).1.2.1 packet move hmove

theorem profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne_blind
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
      (profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne A strategy hwin
        state receiver owner input).1.openControl
      (profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne A strategy hwin
        state receiver owner input).1.closedControl := by
  subst target
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin state target hrealizes root hroot
  simp only [profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne, target,
    packet, hmove]
  exact .staged state
    (profiledRawJointRecurrentLeftReceiveFor A strategy hwin state receiver
      owner input).1.2.1 packet move hmove

theorem ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.receive_blind_one
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    let result := phaseData.receive A strategy hwin input
    ProfiledRawJointRecurrentPhaseBoundaryOneBlind A strategy hwin
      result.1.1.openControl result.1.1.closedControl := by
  dsimp only [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.receive]
  apply ProfiledRawJointRecurrentPhaseBoundaryOneBlind.phase
  exact phaseData.1.phaseLive_blind A strategy hwin phaseData.2.1
    phaseData.2.2 input

theorem ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.receive_blind_two
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin phaseData.1)
    (input : In₁ × In₂) :
    let result := phaseData.receive A strategy hwin input
    ProfiledRawJointRecurrentPhaseBoundaryTwoBlind A strategy hwin
      result.2.1.openControl result.2.1.closedControl := by
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy hwin
      phaseData.1 hinvariant) input
  dsimp only [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.receive]
  apply ProfiledRawJointRecurrentPhaseBoundaryTwoBlind.bridge
  exact
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo_blind A strategy
      hwin phaseData.1.1 (phaseData.1.receiver A strategy hwin)
        (phaseData.1.owner A strategy hwin) (input.2, input.1) _ rfl hrealizes
          root hroot

theorem ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.receive_blind_one
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin phaseData.1)
    (input : In₁ × In₂) :
    let result := phaseData.receive A strategy hwin input
    ProfiledRawJointRecurrentPhaseBoundaryOneBlind A strategy hwin
      result.1.1.openControl result.1.1.closedControl := by
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy hwin
      phaseData.1 hinvariant) input
  dsimp only [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.receive]
  apply ProfiledRawJointRecurrentPhaseBoundaryOneBlind.bridge
  exact
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne_blind A strategy
      hwin phaseData.1.1 (phaseData.1.receiver A strategy hwin)
        (phaseData.1.owner A strategy hwin) input _ rfl hrealizes root hroot

theorem ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.receive_blind_two
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    let result := phaseData.receive A strategy hwin input
    ProfiledRawJointRecurrentPhaseBoundaryTwoBlind A strategy hwin
      result.2.1.openControl result.2.1.closedControl := by
  dsimp only [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.receive]
  apply ProfiledRawJointRecurrentPhaseBoundaryTwoBlind.phase
  exact phaseData.1.phaseLive_blind A strategy hwin phaseData.2.1
    phaseData.2.2 input

theorem profiledRawJointRecurrentPhaseBoundaryReceive?_of_right
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hdata : profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
      one two = some phaseData)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentPhaseBoundaryReceive? A strategy hwin one two
        input =
      some (phaseData.receive A strategy hwin input) := by
  simp [profiledRawJointRecurrentPhaseBoundaryReceive?, hdata]

theorem profiledRawJointRecurrentPhaseBoundaryReceive?_of_left
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hright : profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
      one two = none)
    (hdata : profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin
      one two = some phaseData)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentPhaseBoundaryReceive? A strategy hwin one two
        input =
      some (phaseData.receive A strategy hwin input) := by
  simp [profiledRawJointRecurrentPhaseBoundaryReceive?, hright, hdata]

/-- The selected relation records successful decoding of both active and
dormant dependent pairs and the matched-prefix invariant for the active
physical table. -/
inductive ProfiledRawJointRecurrentPhaseBoundarySelected :
    ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin → Prop
  | right {one two}
      (phaseData :
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
      (hdata : profiledRawJointRecurrentPhaseRightBoundaryData? A strategy
        hwin one two = some phaseData)
      (invariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
        hwin phaseData.1) :
      ProfiledRawJointRecurrentPhaseBoundarySelected one two
  | left {one two}
      (phaseData :
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
      (hright : profiledRawJointRecurrentPhaseRightBoundaryData? A strategy
        hwin one two = none)
      (hdata : profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin
        one two = some phaseData)
      (invariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
        hwin phaseData.1) :
      ProfiledRawJointRecurrentPhaseBoundarySelected one two

/-- The corrected phase-live controller satisfies the exact receive-created
blind laws.  Unlike the tracked diagnostic controller, these laws retain the
advanced old receiver and fresh successor receiver in the resulting state. -/
theorem profiledRawJointRecurrentPhaseBoundaryBlindReceiveLaws :
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindReceiveLaws
      (profiledRawJointRecurrentPhaseBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentPhaseBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentPhaseBoundaryClose A strategy hwin)
      (ProfiledRawJointRecurrentPhaseBoundarySelected A strategy hwin)
      (ProfiledRawJointRecurrentPhaseBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentPhaseBoundaryTwoBlind A strategy hwin) where
  one := by
    intro one inputOne two inputTwo hselected
    cases hselected with
    | right phaseData hdata invariant =>
        have hreceive :=
          profiledRawJointRecurrentPhaseBoundaryReceive?_of_right A strategy
            hwin one two phaseData hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentPhaseBoundaryOpenRecvOne,
          profiledRawJointRecurrentPhaseBoundaryClose, hreceive]
        exact phaseData.receive_blind_one A strategy hwin (inputOne, inputTwo)
    | left phaseData hright hdata invariant =>
        have hreceive :=
          profiledRawJointRecurrentPhaseBoundaryReceive?_of_left A strategy
            hwin one two phaseData hright hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentPhaseBoundaryOpenRecvOne,
          profiledRawJointRecurrentPhaseBoundaryClose, hreceive]
        exact phaseData.receive_blind_one A strategy hwin invariant
          (inputOne, inputTwo)
  two := by
    intro one inputOne two inputTwo hselected
    cases hselected with
    | right phaseData hdata invariant =>
        have hreceive :=
          profiledRawJointRecurrentPhaseBoundaryReceive?_of_right A strategy
            hwin one two phaseData hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentPhaseBoundaryOpenRecvTwo,
          profiledRawJointRecurrentPhaseBoundaryClose, hreceive]
        exact phaseData.receive_blind_two A strategy hwin invariant
          (inputOne, inputTwo)
    | left phaseData hright hdata invariant =>
        have hreceive :=
          profiledRawJointRecurrentPhaseBoundaryReceive?_of_left A strategy
            hwin one two phaseData hright hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentPhaseBoundaryOpenRecvTwo,
          profiledRawJointRecurrentPhaseBoundaryClose, hreceive]
        exact phaseData.receive_blind_two A strategy hwin (inputOne, inputTwo)

end

end DetParityAutomaton

end DistributedSynthesis
