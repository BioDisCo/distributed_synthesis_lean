/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveClosure
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibrePhase

/-!
# Fibre-aware phase decoder

The old phase decoder pairs a delayed owner with a receiver state retained in
the opposite endpoint.  After a strict reversal those states can be one local
step apart.  A valid owner-fibre carrier instead supplies a monitor state that
is prefix-aligned with its current owner.

This file replaces both dormant pending summands by their fibre-backed
versions.  The decoder retains the bank coordinate and row selected by the
old receiver fork, but whenever an owner comes from a fibre carrier it
replaces the corresponding monitor by that carrier's virtual monitor.  Thus
the move, owner, and monitor are definitionally aligned; no equality between
an old state and its successor is asserted.
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

local instance : DecidableEq (BankControl A strategy hwin) :=
  Classical.decEq _

/-! ## Endpoint controls and erasure -/

abbrev ProfiledRawJointRecurrentOwnerFibreBoundaryOneBase :=
  ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin ⊕
    ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin

abbrev ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBase :=
  ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin ⊕
    ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin

abbrev ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneBase A strategy hwin ×
    ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin

abbrev ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBase A strategy hwin ×
    ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy
        hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy
        hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryOneErase
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :
    ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin :=
  match control.1 with
  | .inl bridge => (.inl bridge, control.2)
  | .inr pending =>
      (.inr
        (profiledRawJointRecurrentRightToLeftOwnerFibreErase A strategy hwin
          pending), control.2)

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryTwoErase
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin :=
  match control.1 with
  | .inl bridge => (.inl bridge, control.2)
  | .inr pending =>
      (.inr
        (profiledRawJointRecurrentLeftToRightOwnerFibreErase A strategy hwin
          pending), control.2)

/-! ## Receiver templates and selected receiver forks -/

/-- Keep a right receiver's semantic row, but replace its monitor by the
state carried coherently beside the current right owner.  `lastTarget` is
proof-irrelevant to the boundary invariant and is reset. -/
noncomputable def ProfiledRawJointRightOwnerFibreControl.receiverAt
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (template : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  ⟨control.1, template.2.1, control.2.2, none⟩

/-- Mirrored fibre receiver. -/
noncomputable def ProfiledRawJointLeftOwnerFibreControl.receiverAt
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (template : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  ⟨control.1, template.2.1, control.2.2, none⟩

noncomputable def profiledRawJointRecurrentRightToLeftOwnerFibreReceiver
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin) :
    ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

noncomputable def profiledRawJointRecurrentLeftToRightOwnerFibreReceiver
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin) :
    ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

/-! ## Aligned constructors -/

private noncomputable def profiledRawJointRecurrentOwnerFibreMakeRight?
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
    rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
    by_cases hleft : leftOwnerMove = leftReceiver.1
    · subst leftOwnerMove
      exact some ⟨data, leftState, leftOwnerControl⟩
    · exact none
  · exact none

private noncomputable def profiledRawJointRecurrentOwnerFibreMakeLeft?
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
    rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
    by_cases hright : rightOwnerMove = rightReceiver.1
    · subst rightOwnerMove
      exact some ⟨data, rightState, rightOwnerControl⟩
    · exact none
  · exact none

/-! The following two projection lemmas expose the only bank-state fact used
by later trace arguments.  The alignment checks may change dependent owner
types, but a successful constructor does not change either bank state. -/

theorem profiledRawJointRecurrentOwnerFibreMakeRight?_states
    (state : BankControl A strategy hwin)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftState : BankControl A strategy hwin)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hmake :
      profiledRawJointRecurrentOwnerFibreMakeRight? A strategy hwin state
        rightOwner rightReceiver leftState leftOwner leftReceiver =
          some data) :
    data.1.1 = state ∧ data.2.1 = leftState := by
  classical
  rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
  rcases rightReceiver with
    ⟨rightReceiverMove, rightRow, rightReceiverState, rightTarget⟩
  unfold profiledRawJointRecurrentOwnerFibreMakeRight? at hmake
  simp only [Sigma.casesOn, Prod.casesOn] at hmake
  split at hmake
  · subst rightReceiverMove
    rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
    split at hmake
    · rename_i hleft
      change leftOwnerMove = leftReceiver.1 at hleft
      subst leftOwnerMove
      have heq := Option.some.inj hmake
      rw [← heq]
      exact ⟨rfl, rfl⟩
    · simp at hmake
  · simp at hmake

theorem profiledRawJointRecurrentOwnerFibreMakeLeft?_states
    (state : BankControl A strategy hwin)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightState : BankControl A strategy hwin)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hmake :
      profiledRawJointRecurrentOwnerFibreMakeLeft? A strategy hwin state
        leftOwner leftReceiver rightState rightOwner rightReceiver =
          some data) :
    data.1.1 = state ∧ data.2.1 = rightState := by
  classical
  rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
  rcases leftReceiver with
    ⟨leftReceiverMove, leftRow, leftReceiverState, leftTarget⟩
  unfold profiledRawJointRecurrentOwnerFibreMakeLeft? at hmake
  simp only [Sigma.casesOn, Prod.casesOn] at hmake
  split at hmake
  · subst leftReceiverMove
    rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
    split at hmake
    · rename_i hright
      change rightOwnerMove = rightReceiver.1 at hright
      subst rightOwnerMove
      have heq := Option.some.inj hmake
      rw [← heq]
      exact ⟨rfl, rfl⟩
    · simp at hmake
  · simp at hmake

theorem profiledRawJointRecurrentOwnerFibreMakeRight?_indices
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy)
    (state : BankControl A strategy hwin)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftState : BankControl A strategy hwin)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hstate : state.1 = key)
    (hleft : leftState.1 = key)
    (hmake :
      profiledRawJointRecurrentOwnerFibreMakeRight? A strategy hwin state
        rightOwner rightReceiver leftState leftOwner leftReceiver =
          some data) :
    data.1.1.1 = key ∧ data.2.1.1 = key := by
  obtain ⟨hdataState, hdataLeft⟩ :=
    profiledRawJointRecurrentOwnerFibreMakeRight?_states A strategy hwin state
      rightOwner rightReceiver leftState leftOwner leftReceiver data hmake
  exact ⟨(congrArg (fun control : BankControl A strategy hwin ↦ control.1)
      hdataState).trans hstate,
    (congrArg (fun control : BankControl A strategy hwin ↦ control.1)
      hdataLeft).trans hleft⟩

theorem profiledRawJointRecurrentOwnerFibreMakeLeft?_indices
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy)
    (state : BankControl A strategy hwin)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightState : BankControl A strategy hwin)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hstate : state.1 = key)
    (hright : rightState.1 = key)
    (hmake :
      profiledRawJointRecurrentOwnerFibreMakeLeft? A strategy hwin state
        leftOwner leftReceiver rightState rightOwner rightReceiver =
          some data) :
    data.1.1.1 = key ∧ data.2.1.1 = key := by
  obtain ⟨hdataState, hdataRight⟩ :=
    profiledRawJointRecurrentOwnerFibreMakeLeft?_states A strategy hwin state
      leftOwner leftReceiver rightState rightOwner rightReceiver data hmake
  exact ⟨(congrArg (fun control : BankControl A strategy hwin ↦ control.1)
      hdataState).trans hstate,
    (congrArg (fun control : BankControl A strategy hwin ↦ control.1)
      hdataRight).trans hright⟩

/-! ## Fibre-aware eight-shape decoder -/

noncomputable def profiledRawJointRecurrentOwnerFibreRightBoundaryData?
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Option
      (ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) :=
  match one.1, two.1 with
  | .inl (.inr installed), .inl (.inl staged) =>
      if installed.1 = staged.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.2.2 with
            | none => none
            | some move =>
                let leftReceiver :=
                  initialProfiledRawJointLeftPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentOwnerFibreMakeRight? A strategy hwin
                  installed.1 installed.2.1 staged.2.1 packet.successor
                    ⟨move, (move.memberController A false).initial⟩ leftReceiver
      else none
  | .inl (.inr installed), .inr pendingTwo =>
      let rightReceiver :=
        profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy hwin
          pendingTwo
      let leftFibre := pendingTwo.2.1.1
      let leftReceiver := leftFibre.receiverAt A installed.2.2
      if installed.1 = rightReceiver.1 then
        profiledRawJointRecurrentOwnerFibreMakeRight? A strategy hwin
          installed.1 installed.2.1 rightReceiver.2 one.2.2
            (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
            leftReceiver
      else none
  | .inr pendingOne, .inr pendingTwo =>
      if pendingOne.1 || !pendingTwo.1 then
        let rightTemplate :=
          (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy
            hwin pendingTwo).2
        let leftTemplate :=
          (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy
            hwin pendingOne).2
        let rightFibre := pendingOne.2.1.1
        let leftFibre := pendingTwo.2.1.1
        profiledRawJointRecurrentOwnerFibreMakeRight? A strategy hwin
          (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy
            hwin pendingTwo).1
          (profiledRawJointRightOwnerFibreExceptional A rightFibre)
          (rightFibre.receiverAt A rightTemplate)
          (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy
            hwin pendingOne).1
          (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
          (leftFibre.receiverAt A leftTemplate)
      else none
  | .inr pendingOne, .inl (.inl staged) =>
      match staged.2.2 with
      | none => none
      | some packet =>
          match packet.successor.2.1.2.2 with
          | none => none
          | some move =>
              let rightFibre := pendingOne.2.1.1
              let leftReceiver :=
                initialProfiledRawJointLeftPhysicalSiblingReceiver A move
                  .first
              profiledRawJointRecurrentOwnerFibreMakeRight? A strategy hwin
                staged.1
                  (profiledRawJointRightOwnerFibreExceptional A rightFibre)
                  (rightFibre.receiverAt A staged.2.1)
                  packet.successor
                  ⟨move, (move.memberController A false).initial⟩ leftReceiver
  | _, _ => none

noncomputable def profiledRawJointRecurrentOwnerFibreLeftBoundaryData?
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Option
      (ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) :=
  match one.1, two.1 with
  | .inl (.inl staged), .inl (.inr installed) =>
      if installed.1 = staged.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.2.1 with
            | none => none
            | some move =>
                let rightReceiver :=
                  initialProfiledRawJointRightPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentOwnerFibreMakeLeft? A strategy hwin
                  installed.1 installed.2.1 staged.2.1 packet.successor
                    ⟨move, (move.memberController A false).initial⟩
                    rightReceiver
      else none
  | .inr pendingOne, .inl (.inr installed) =>
      let leftReceiver :=
        profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy hwin
          pendingOne
      let rightFibre := pendingOne.2.1.1
      let rightReceiver := rightFibre.receiverAt A installed.2.2
      if installed.1 = leftReceiver.1 then
        profiledRawJointRecurrentOwnerFibreMakeLeft? A strategy hwin
          installed.1 installed.2.1 leftReceiver.2 two.2.1
            (profiledRawJointRightOwnerFibreExceptional A rightFibre)
            rightReceiver
      else none
  | .inr pendingOne, .inr pendingTwo =>
      if !pendingOne.1 && pendingTwo.1 then
        let leftTemplate :=
          (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy
            hwin pendingOne).2
        let rightTemplate :=
          (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy
            hwin pendingTwo).2
        let rightFibre := pendingOne.2.1.1
        let leftFibre := pendingTwo.2.1.1
        profiledRawJointRecurrentOwnerFibreMakeLeft? A strategy hwin
          (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy
            hwin pendingOne).1
          (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
          (leftFibre.receiverAt A leftTemplate)
          (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy
            hwin pendingTwo).1
          (profiledRawJointRightOwnerFibreExceptional A rightFibre)
          (rightFibre.receiverAt A rightTemplate)
      else none
  | .inl (.inl staged), .inr pendingTwo =>
      if pendingTwo.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.2.1 with
            | none => none
            | some move =>
                let leftFibre := pendingTwo.2.1.1
                let rightReceiver :=
                  initialProfiledRawJointRightPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentOwnerFibreMakeLeft? A strategy hwin
                  staged.1
                    (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
                    (leftFibre.receiverAt A staged.2.1)
                    packet.successor
                    ⟨move, (move.memberController A false).initial⟩
                    rightReceiver
      else none
  | _, _ => none

/-! ## Strict-reversal fail-fast equations -/

/-- Canonical installed/staged decoding.  The installed owner is aligned with
the staged receiver, and the staged packet supplies the fresh dormant left
move. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : packet.successor.2.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inl (.inl (rightState, rightReceiver, some packet)),
          twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          packet.successor, (leftMove.memberController A false).initial⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeRight?, hleftMove,
    initialProfiledRawJointLeftPhysicalSiblingReceiver]

/-- Mirrored staged/installed decoding. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : packet.successor.2.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some packet)), oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          packet.successor, (rightMove.memberController A false).initial⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeLeft?, hrightMove,
    initialProfiledRawJointRightPhysicalSiblingReceiver]

/-! ## Inversion of the two bridge/bridge branches -/

/-- Success of the installed/staged branch recovers all equalities checked by
the decoder. -/
theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged_inv
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl (.inr installed), oneCoordinates)
          (.inl (.inl staged), twoCoordinates) = some phaseData) :
    ∃ (rightState : BankControl A strategy hwin)
      (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
      (rightOwner : (rightReceiver.1.memberController A false).Control)
      (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
      (packet :
        ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin)
      (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A),
      installed =
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate) ∧
        staged = (rightState, rightReceiver, some packet) ∧
        packet.successor.2.1.2.2 = some leftMove ∧
        phaseData =
          ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
              initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
                .first),
            packet.successor,
            (leftMove.memberController A false).initial⟩ := by
  rcases installed with ⟨rightState, rightExceptional, leftTemplate⟩
  rcases rightExceptional with ⟨rightMove, rightOwner⟩
  rcases staged with ⟨stagedState, rightReceiver, packet⟩
  rcases rightReceiver with
    ⟨receiverMove, rightRow, rightReceiverState, rightTarget⟩
  cases packet with
  | none =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
  | some packet =>
      cases hleftMove : packet.successor.2.1.2.2 with
      | none =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
            hleftMove] at hdecode
      | some leftMove =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
            profiledRawJointRecurrentOwnerFibreMakeRight?, hleftMove] at hdecode
          rcases hdecode with
            ⟨hstate, ⟨hreceiverMove, hdecode⟩⟩
          subst stagedState
          subst receiverMove
          simp [initialProfiledRawJointLeftPhysicalSiblingReceiver] at hdecode
          subst phaseData
          exact ⟨rightState,
            ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩,
            rightOwner, leftTemplate, packet, leftMove, rfl, rfl,
            hleftMove, rfl⟩

/-- Mirrored inversion of the staged/installed branch. -/
theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled_inv
    (staged :
      ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl staged), oneCoordinates)
          (.inl (.inr installed), twoCoordinates) = some phaseData) :
    ∃ (leftState : BankControl A strategy hwin)
      (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
      (leftOwner : (leftReceiver.1.memberController A false).Control)
      (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
      (packet :
        ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin)
      (rightMove : ProfiledRawJointRightPhysicalSiblingMove A),
      staged = (leftState, leftReceiver, some packet) ∧
        installed =
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate) ∧
        packet.successor.2.1.2.1 = some rightMove ∧
        phaseData =
          ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
              initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
                .first),
            packet.successor,
            (rightMove.memberController A false).initial⟩ := by
  rcases staged with ⟨stagedState, leftReceiver, packet⟩
  rcases leftReceiver with
    ⟨receiverMove, leftRow, leftReceiverState, leftTarget⟩
  rcases installed with ⟨leftState, leftExceptional, rightTemplate⟩
  rcases leftExceptional with ⟨leftMove, leftOwner⟩
  cases packet with
  | none =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode
  | some packet =>
      cases hrightMove : packet.successor.2.1.2.1 with
      | none =>
          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
            hrightMove] at hdecode
      | some rightMove =>
          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
            profiledRawJointRecurrentOwnerFibreMakeLeft?, hrightMove] at hdecode
          rcases hdecode with
            ⟨hstate, ⟨hreceiverMove, hdecode⟩⟩
          subst stagedState
          subst receiverMove
          simp [initialProfiledRawJointRightPhysicalSiblingReceiver] at hdecode
          subst phaseData
          exact ⟨leftState,
            ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩,
            leftOwner, rightTemplate, packet, rightMove, rfl, rfl,
            hrightMove, rfl⟩

/-- Success of installed/fibre decoding identifies the installed state and
owner with the receiver member selected by the pending fibre. -/
theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl (.inr installed), oneCoordinates)
          (.inr pendingTwo, twoCoordinates) = some phaseData) :
    let rightReceiver :=
      profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy hwin
        pendingTwo
    let leftFibre := pendingTwo.2.1.1
    ∃ (rightOwner : (rightReceiver.2.1.memberController A false).Control)
      (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A),
      installed =
          (rightReceiver.1,
            ⟨rightReceiver.2.1, rightOwner⟩, leftTemplate) ∧
        phaseData =
          ⟨(rightReceiver.1, ⟨rightReceiver.2, rightOwner⟩,
              leftFibre.receiverAt A leftTemplate),
            oneCoordinates.2, leftFibre.2.1⟩ := by
  rcases installed with ⟨installedState, rightExceptional, leftTemplate⟩
  rcases rightExceptional with ⟨rightMove, rightOwner⟩
  rcases pendingTwo with
    ⟨member, ⟨⟨leftFibre, receiverFork⟩, empty⟩⟩
  rcases empty with ⟨⟩
  rcases receiverFork with ⟨openReceiver, closedReceiver⟩
  cases member <;>
    rcases openReceiver with ⟨openState, openReceiver⟩ <;>
    rcases closedReceiver with ⟨closedState, closedReceiver⟩
  · rcases openReceiver with
      ⟨receiverMove, rightRow, rightReceiverState, rightTarget⟩
    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
      profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
      profiledRawJointRecurrentOwnerFibreMakeRight?] at hdecode
    rcases hdecode with
      ⟨hstate, ⟨hmove, hdecode⟩⟩
    subst installedState
    subst receiverMove
    simp [profiledRawJointLeftOwnerFibreExceptional,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hdecode
    subst phaseData
    exact ⟨rightOwner, leftTemplate, rfl, rfl⟩
  · rcases closedReceiver with
      ⟨receiverMove, rightRow, rightReceiverState, rightTarget⟩
    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
      profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
      profiledRawJointRecurrentOwnerFibreMakeRight?] at hdecode
    rcases hdecode with
      ⟨hstate, ⟨hmove, hdecode⟩⟩
    subst installedState
    subst receiverMove
    simp [profiledRawJointLeftOwnerFibreExceptional,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hdecode
    subst phaseData
    exact ⟨rightOwner, leftTemplate, rfl, rfl⟩

/-- Mirrored inversion of fibre/installed decoding. -/
theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr pendingOne, oneCoordinates)
          (.inl (.inr installed), twoCoordinates) = some phaseData) :
    let leftReceiver :=
      profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy hwin
        pendingOne
    let rightFibre := pendingOne.2.1.1
    ∃ (leftOwner : (leftReceiver.2.1.memberController A false).Control)
      (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A),
      installed =
          (leftReceiver.1,
            ⟨leftReceiver.2.1, leftOwner⟩, rightTemplate) ∧
        phaseData =
          ⟨(leftReceiver.1, ⟨leftReceiver.2, leftOwner⟩,
              rightFibre.receiverAt A rightTemplate),
            twoCoordinates.1, rightFibre.2.1⟩ := by
  rcases pendingOne with
    ⟨member, ⟨⟨rightFibre, receiverFork⟩, empty⟩⟩
  rcases empty with ⟨⟩
  rcases receiverFork with ⟨openReceiver, closedReceiver⟩
  rcases installed with ⟨installedState, leftExceptional, rightTemplate⟩
  rcases leftExceptional with ⟨leftMove, leftOwner⟩
  cases member <;>
    rcases openReceiver with ⟨openState, openReceiver⟩ <;>
    rcases closedReceiver with ⟨closedState, closedReceiver⟩
  · rcases openReceiver with
      ⟨receiverMove, leftRow, leftReceiverState, leftTarget⟩
    simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
      profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
      profiledRawJointRecurrentOwnerFibreMakeLeft?] at hdecode
    rcases hdecode with
      ⟨hstate, ⟨hmove, hdecode⟩⟩
    subst installedState
    subst receiverMove
    simp [profiledRawJointRightOwnerFibreExceptional,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] at hdecode
    subst phaseData
    exact ⟨leftOwner, rightTemplate, rfl, rfl⟩
  · rcases closedReceiver with
      ⟨receiverMove, leftRow, leftReceiverState, leftTarget⟩
    simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
      profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
      profiledRawJointRecurrentOwnerFibreMakeLeft?] at hdecode
    rcases hdecode with
      ⟨hstate, ⟨hmove, hdecode⟩⟩
    subst installedState
    subst receiverMove
    simp [profiledRawJointRightOwnerFibreExceptional,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] at hdecode
    subst phaseData
    exact ⟨leftOwner, rightTemplate, rfl, rfl⟩

/-- A pending first endpoint and an installed second endpoint have the
left-oriented fibre/installed shape, so the right decoder rejects them before
inspecting any payload. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_reject_fibreInstalled
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl (.inr installed), twoCoordinates) = none := by
  rfl

/-- The mirror tag-disjointness fact: installed/fibre is right-oriented and
is rejected by the left decoder before any payload is inspected. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_reject_installedFibre
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        (.inl (.inr installed), oneCoordinates)
        (.inr pendingTwo, twoCoordinates) = none := by
  rfl

/-- In an installed/fibre right boundary, the active right receiver is the
selected open receiver.  The dormant left row is retained from the installed
template, but its monitor and owner both come from the delivered left fibre. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (false,
        (leftFibre, ⟨(rightState, rightReceiver), newRight⟩), ())
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            leftFibre.receiverAt A leftTemplate),
          oneCoordinates.2, leftFibre.2.1⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeRight?,
    profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
    ProfiledRawJointLeftOwnerFibreControl.receiverAt,
    profiledRawJointLeftOwnerFibreExceptional]

/-- The preceding decoded value satisfies the complete dual invariant once
the active right table is aligned and the delivered left fibre is valid at
the retained left bank coordinate. -/
theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_installedFibre
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (leftState : BankControl A strategy hwin)
    (hactive :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate))
    (hfibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : leftState.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (hmove : leftState.2.1.2.2 = some leftFibre.1) :
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
      ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
          leftFibre.receiverAt A leftTemplate),
        leftState, leftFibre.2.1⟩ := by
  constructor
  · exact
      ProfiledRawJointRecurrentRightBoundaryInvariant.replaceOldReceiver A
        strategy hwin _ hactive (leftFibre.receiverAt A leftTemplate)
  · simpa [
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointLeftOwnerFibreControl.boundaryData,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] using
        hfibre.boundaryInvariant A strategy hwin leftFibre leftState hleftState
          currentCode hcurrentCode root hroot hmove leftTemplate.2.1
            rightReceiver

/-- The closed-member form of installed/fibre decoding.  Here the current
right receiver is the closed member of the stored receiver fork. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibreClosed
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true,
        (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ())
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            leftFibre.receiverAt A leftTemplate),
          oneCoordinates.2, leftFibre.2.1⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeRight?,
    profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
    ProfiledRawJointLeftOwnerFibreControl.receiverAt,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Mirrored phase/fibre strict-reversal equation. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true,
        (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ())
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            rightFibre.receiverAt A rightTemplate),
          twoCoordinates.1, rightFibre.2.1⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeLeft?,
    profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.receiverAt,
    profiledRawJointRightOwnerFibreExceptional]

/-- Mirrored dual-invariant reconstruction. -/
theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreInstalled
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (rightState : BankControl A strategy hwin)
    (hactive :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate))
    (hfibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : rightState.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (hmove : rightState.2.1.2.1 = some rightFibre.1) :
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
      ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
          rightFibre.receiverAt A rightTemplate),
        rightState, rightFibre.2.1⟩ := by
  constructor
  · exact
      ProfiledRawJointRecurrentLeftBoundaryInvariant.replaceOldReceiver A
        strategy hwin _ hactive (rightFibre.receiverAt A rightTemplate)
  · simpa [
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRightOwnerFibreControl.boundaryData,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using
        hfibre.boundaryInvariant A strategy hwin rightFibre rightState
          hrightState currentCode hcurrentCode root hroot hmove
            rightTemplate.2.1 leftReceiver

/-- The open-member version of the fibre/installed decoder seam.  This is
the form produced when a right-oriented fibre/staged state takes a
strict-left step. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_openFibreInstalled
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false,
        (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ())
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            rightFibre.receiverAt A rightTemplate),
          twoCoordinates.1, rightFibre.2.1⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeLeft?,
    profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.receiverAt,
    profiledRawJointRightOwnerFibreExceptional]

/-! ## Deferred/deferred fibre alignment -/

/-- The right-oriented deferred/deferred case uses one coherent fibre for
each orientation.  The selected receiver forks contribute only their bank
coordinates and rows. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
            leftFibre.receiverAt A leftTemplate),
          leftState, leftFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeRight?,
    profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.receiverAt,
    ProfiledRawJointLeftOwnerFibreControl.receiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Validity of the two delivered fibres reconstructs both halves of the
dual invariant in the right deferred/deferred case. -/
theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
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
    (hleftRoot : profiledRawJointOneSidedCurrentSlots A .left leftCode () =
      some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1) :
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
      ⟨(rightState,
          ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
          leftFibre.receiverAt A leftTemplate),
        leftState, leftFibre.2.1⟩ := by
  constructor
  · simpa [ProfiledRawJointRightOwnerFibreControl.boundaryData,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using
        hrightFibre.boundaryInvariant A strategy hwin rightFibre rightState
          hrightState rightCode hrightCode rightRoot hrightRoot hrightMove
            rightTemplate.2.1 (leftFibre.receiverAt A leftTemplate)
  · simpa [
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointLeftOwnerFibreControl.boundaryData,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] using
        hleftFibre.boundaryInvariant A strategy hwin leftFibre leftState
          hleftState leftCode hleftCode leftRoot hleftRoot hleftMove
            leftTemplate.2.1 (rightFibre.receiverAt A rightTemplate)

/-- After two alternating strict rounds both newly selected members are open.
The right-priority decoder assigns `(false,false)` to the right orientation;
the two fibre certificates still give exactly the same dual invariant. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
            leftFibre.receiverAt A leftTemplate),
          leftState, leftFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeRight?,
    profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.receiverAt,
    ProfiledRawJointLeftOwnerFibreControl.receiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-! ## Closed/closed two-fibre alignment -/

/-- When both delivered fibres select their closed receiver, the right
orientation has priority.  As in the other two-fibre equations, the receiver
forks supply the bank coordinates and rows, whereas the two fibre controls
supply the aligned monitors and owners. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_closedClosed
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true, (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ())
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
            leftFibre.receiverAt A leftTemplate),
          leftState, leftFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeRight?,
    profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.receiverAt,
    ProfiledRawJointLeftOwnerFibreControl.receiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-! ## Fibre/staged alignment -/

/-- A right fibre paired with an informed staged receiver decodes without
consulting the obsolete receiver fork carried beside the fibre.  The active
right monitor comes from the fibre, while the fresh left boundary comes from
the staged packet successor. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : packet.successor.2.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false, (rightFibre, ⟨oldLeft, newLeft⟩), ())
    let staged :
        ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin :=
      (rightState, rightReceiver, some packet)
    profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl (.inl staged), twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.receiverAt A rightReceiver, rightFibre.2.1⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          packet.successor,
          (leftMove.memberController A false).initial⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases rightFibre with
    ⟨rightFibreMove, rightOwner, rightMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeRight?,
    ProfiledRawJointRightOwnerFibreControl.receiverAt, hleftMove,
    initialProfiledRawJointLeftPhysicalSiblingReceiver,
    profiledRawJointRightOwnerFibreExceptional]

/-- Mirrored deferred/deferred equation. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true, (leftFibre, ⟨newRight, (rightState, rightTemplate)⟩), ())
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(leftState,
            ⟨leftFibre.receiverAt A leftTemplate, leftFibre.2.1⟩,
            rightFibre.receiverAt A rightTemplate),
          rightState, rightFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeLeft?,
    profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.receiverAt,
    ProfiledRawJointLeftOwnerFibreControl.receiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Mirrored staged/fibre decoder seam.  The active left monitor comes from
the fibre and the staged packet supplies the fresh right boundary. -/
@[simp] theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedFibre
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight newRight :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : packet.successor.2.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    let staged :
        ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin :=
      (leftState, leftReceiver, some packet)
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true, (leftFibre, ⟨oldRight, newRight⟩), ())
    profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        (.inl (.inl staged), oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(leftState,
            ⟨leftFibre.receiverAt A leftReceiver, leftFibre.2.1⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          packet.successor,
          (rightMove.memberController A false).initial⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases leftFibre with
    ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentOwnerFibreMakeLeft?,
    ProfiledRawJointLeftOwnerFibreControl.receiverAt, hrightMove,
    initialProfiledRawJointRightPhysicalSiblingReceiver,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Mirrored two-fibre dual invariant. -/
theorem
    profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreFibre
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
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
    (hleftRoot : profiledRawJointOneSidedCurrentSlots A .left leftCode () =
      some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1) :
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
      ⟨(leftState,
          ⟨leftFibre.receiverAt A leftTemplate, leftFibre.2.1⟩,
          rightFibre.receiverAt A rightTemplate),
        rightState, rightFibre.2.1⟩ := by
  constructor
  · simpa [ProfiledRawJointLeftOwnerFibreControl.boundaryData,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt] using
        hleftFibre.boundaryInvariant A strategy hwin leftFibre leftState
          hleftState leftCode hleftCode leftRoot hleftRoot hleftMove
            leftTemplate.2.1 (rightFibre.receiverAt A rightTemplate)
  · simpa [
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRightOwnerFibreControl.boundaryData,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using
        hrightFibre.boundaryInvariant A strategy hwin rightFibre rightState
          hrightState rightCode hrightCode rightRoot hrightRoot hrightMove
            rightTemplate.2.1 (leftFibre.receiverAt A leftTemplate)

end

end DetParityAutomaton

end DistributedSynthesis
