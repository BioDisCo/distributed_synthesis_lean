/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreDecoder

/-!
# Transition maps for the fibre-aware phase carrier

This file installs the fibre-backed pending states in the actual finite
endpoint controls.  Boundary receives initialize a coherent fibre from the
advanced active owner; owner-only rounds advance that fibre locally.  The
informed bridge and the two bank-coordinate registers are unchanged.
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

/-! ## Fibre packet seams from aligned boundary data -/

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy
          hwin) ×
      Out₁ :=
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin data.1 (data.target A strategy hwin input)
  profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork A strategy
    hwin
      ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
      oldState data.2.2 oldOwner packet input

theorem ProfiledRawJointRecurrentRightBoundaryInvariant.ownerFibreReceive_valid
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let fork :=
      (data.ownerFibreReceive A strategy hwin oldState oldOwner input).1
    ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        fork.openControl ∧
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        fork.closedControl := by
  dsimp only [ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive]
  apply
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork_valid A
      strategy hwin
  exact hinvariant.ownerReachable A strategy hwin data

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy
          hwin) ×
      Out₂ :=
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin data.1 (data.target A strategy hwin input)
  profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork A strategy
    hwin
      ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
      oldState data.2.2 oldOwner packet (input.2, input.1)

theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.ownerFibreReceive_valid
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let fork :=
      (data.ownerFibreReceive A strategy hwin oldState oldOwner input).1
    ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        fork.openControl ∧
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        fork.closedControl := by
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive]
  apply
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork_valid A
      strategy hwin
  exact hinvariant.ownerReachable A strategy hwin data

/-! ## One-round phase transitions -/

noncomputable def
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy
          hwin) × Out₁) ×
      (FiniteDelayedFork
        (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy
          hwin) × Out₂) :=
  let data := phaseData.1
  let phaseOne := data.ownerFibreReceive A strategy hwin phaseData.2.1
    phaseData.2.2 input
  let bridgeTwo :=
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin)
        (input.2, input.1)
  let successor := data.successor A strategy hwin input
  let oneFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :=
    ⟨(.inr phaseOne.1.openControl, data.1, phaseData.2.1),
      (.inr phaseOne.1.closedControl, data.1, successor)⟩
  let twoFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :=
    ⟨(.inl bridgeTwo.1.openControl, data.1, successor),
      (.inl bridgeTwo.1.closedControl, data.1, successor)⟩
  ((oneFork, phaseOne.2), (twoFork, bridgeTwo.2))

noncomputable def
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (FiniteDelayedFork
        (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy
          hwin) × Out₁) ×
      (FiniteDelayedFork
        (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy
          hwin) × Out₂) :=
  let data := phaseData.1
  let bridgeOne :=
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin) input
  let phaseTwo := data.ownerFibreReceive A strategy hwin phaseData.2.1
    phaseData.2.2 input
  let successor := data.successor A strategy hwin input
  let oneFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :=
    ⟨(.inl bridgeOne.1.openControl, successor, data.1),
      (.inl bridgeOne.1.closedControl, successor, data.1)⟩
  let twoFork : FiniteDelayedFork
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :=
    ⟨(.inr phaseTwo.1.openControl, phaseData.2.1, data.1),
      (.inr phaseTwo.1.closedControl, successor, data.1)⟩
  ((oneFork, bridgeOne.2), (twoFork, phaseTwo.2))

/-! ## Total local transitions -/

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin ×
      Out₁ :=
  match control.1 with
  | .inl bridge =>
      let next := profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy
        hwin bridge input
      ((.inl next.1, control.2), next.2)
  | .inr pending =>
      let next := profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A
        strategy hwin pending input
      ((.inr next.1, control.2), next.2)

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin ×
      Out₂ :=
  match control.1 with
  | .inl bridge =>
      let next := profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy
        hwin bridge input
      ((.inl next.1, control.2), next.2)
  | .inr pending =>
      let next := profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A
        strategy hwin pending input
      ((.inr next.1, control.2), next.2)

theorem profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne_erase
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (input : In₁) :
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        control input).2 =
      (profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOneErase A strategy hwin
          control) input).2 ∧
    profiledRawJointRecurrentOwnerFibreBoundaryOneErase A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          control input).1 =
      (profiledRawJointRecurrentPhaseBoundaryNoRecvOne A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOneErase A strategy hwin
          control) input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge => constructor <;> rfl
  | inr pending =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
        profiledRawJointRecurrentOwnerFibreBoundaryOneErase,
        profiledRawJointRecurrentPhaseBoundaryNoRecvOne] using
          profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv_erase A strategy
            hwin pending input

theorem profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo_erase
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (input : In₂) :
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        control input).2 =
      (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryTwoErase A strategy hwin
          control) input).2 ∧
    profiledRawJointRecurrentOwnerFibreBoundaryTwoErase A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          control input).1 =
      (profiledRawJointRecurrentPhaseBoundaryNoRecvTwo A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryTwoErase A strategy hwin
          control) input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge => constructor <;> rfl
  | inr pending =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
        profiledRawJointRecurrentOwnerFibreBoundaryTwoErase,
        profiledRawJointRecurrentPhaseBoundaryNoRecvTwo] using
          profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv_erase A strategy
            hwin pending input

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryReceive?
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (input : In₁ × In₂) :
    Option
      ((FiniteDelayedFork
          (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy
            hwin) × Out₁) ×
        (FiniteDelayedFork
          (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy
            hwin) × Out₂)) :=
  match profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
      one two with
  | some data => some (data.ownerFibreReceive A strategy hwin input)
  | none =>
      match profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy
          hwin one two with
      | some data => some (data.ownerFibreReceive A strategy hwin input)
      | none => none

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin ×
      Out₁ :=
  match profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
      one two (inputOne, inputTwo) with
  | some result => (result.1.1.openControl, result.1.2)
  | none =>
      profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin one
        inputOne

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin ×
      Out₂ :=
  match profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
      one two (inputOne, inputTwo) with
  | some result => (result.2.1.openControl, result.2.2)
  | none =>
      profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin two
        inputTwo

noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryClose
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin ×
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
  match profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
      one two (inputOne, inputTwo) with
  | some result =>
      (result.1.1.closedControl, result.2.1.closedControl)
  | none =>
      ((profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one inputOne).1,
       (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two inputTwo).1)

/-! ## Semantic selected relation -/

inductive ProfiledRawJointRecurrentOwnerFibreBoundarySelected :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin →
        Prop
  | right {one two}
      (phaseData :
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
      (hdata :
        profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          one two = some phaseData)
      (invariant :
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy
          hwin phaseData) :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected one two
  | left {one two}
      (phaseData :
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
      (hright :
        profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          one two = none)
      (hdata :
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          one two = some phaseData)
      (invariant :
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy
          hwin phaseData) :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected one two

end

end DetParityAutomaton

end DistributedSynthesis
