/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicySelectionLocalBoundary
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreController

/-!
# Owner-fibre runtime kernel for a replaceable policy selection

The owner-fibre control types and all propagation steps are independent of
which rational policy was selected.  The selection is consulted only when an
informed boundary resolves a new target packet.  This file parameterizes that
single injection seam and rebuilds the top-level receive and round functions.

In addition to the next controls, `round` retains both emitted outputs.  It is
therefore the exact finite closed-loop transition needed by the subsequent
parity safety game.  No semantic source, reachability proof, graph oracle, or
other endpoint's input is stored in an endpoint control.
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

private abbrev OneControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin

private abbrev TwoControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin

private abbrev PolicySelection :=
  ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy hwin

namespace ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

variable (selection : PolicySelection A strategy hwin)

/-! ## The only policy-dependent injection seam -/

/-- Resolve a right boundary with `selection`, then initialize the existing
right-to-left owner-fibre fork from that packet. -/
noncomputable def rightBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy
          hwin) ×
      Out₁ :=
  let packet := selection.resolvePacket A strategy hwin data.1
    (data.target A strategy hwin input)
  profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork A strategy
    hwin ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
      oldState data.2.2 oldOwner packet input

/-- Left-orientation mirror of `rightBoundaryOwnerFibreReceive`. -/
noncomputable def leftBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy
          hwin) ×
      Out₂ :=
  let packet := selection.resolvePacket A strategy hwin data.1
    (data.target A strategy hwin input)
  profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork A strategy
    hwin ⟨(data.receiver A strategy hwin).1, data.owner A strategy hwin⟩
      oldState data.2.2 oldOwner packet (input.2, input.1)

/-- Lift the selected-policy right packet seam to both endpoint controls. -/
noncomputable def rightPhaseOwnerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (FiniteDelayedFork (OneControl A strategy hwin) × Out₁) ×
      (FiniteDelayedFork (TwoControl A strategy hwin) × Out₂) :=
  let data := phaseData.1
  let phaseOne := selection.rightBoundaryOwnerFibreReceive A strategy hwin
    data phaseData.2.1 phaseData.2.2 input
  let bridgeTwo :=
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin)
        (input.2, input.1)
  let successor := data.successor A strategy hwin input
  let oneFork : FiniteDelayedFork (OneControl A strategy hwin) :=
    ⟨(.inr phaseOne.1.openControl, data.1, phaseData.2.1),
      (.inr phaseOne.1.closedControl, data.1, successor)⟩
  let twoFork : FiniteDelayedFork (TwoControl A strategy hwin) :=
    ⟨(.inl bridgeTwo.1.openControl, data.1, successor),
      (.inl bridgeTwo.1.closedControl, data.1, successor)⟩
  ((oneFork, phaseOne.2), (twoFork, bridgeTwo.2))

/-- Lift the selected-policy left packet seam to both endpoint controls. -/
noncomputable def leftPhaseOwnerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (FiniteDelayedFork (OneControl A strategy hwin) × Out₁) ×
      (FiniteDelayedFork (TwoControl A strategy hwin) × Out₂) :=
  let data := phaseData.1
  let bridgeOne :=
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin) input
  let phaseTwo := selection.leftBoundaryOwnerFibreReceive A strategy hwin data
    phaseData.2.1 phaseData.2.2 input
  let successor := data.successor A strategy hwin input
  let oneFork : FiniteDelayedFork (OneControl A strategy hwin) :=
    ⟨(.inl bridgeOne.1.openControl, successor, data.1),
      (.inl bridgeOne.1.closedControl, successor, data.1)⟩
  let twoFork : FiniteDelayedFork (TwoControl A strategy hwin) :=
    ⟨(.inr phaseTwo.1.openControl, phaseData.2.1, data.1),
      (.inr phaseTwo.1.closedControl, successor, data.1)⟩
  ((oneFork, bridgeOne.2), (twoFork, phaseTwo.2))

/-! ## Selection-relative top-level receives -/

/-- Decode an aligned boundary and resolve it with `selection`. -/
noncomputable def ownerFibreBoundaryReceive?
    (one : OneControl A strategy hwin)
    (two : TwoControl A strategy hwin)
    (input : In₁ × In₂) :
    Option
      ((FiniteDelayedFork (OneControl A strategy hwin) × Out₁) ×
        (FiniteDelayedFork (TwoControl A strategy hwin) × Out₂)) :=
  match profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
      one two with
  | some data => some (selection.rightPhaseOwnerFibreReceive A strategy hwin
      data input)
  | none =>
      match profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy
          hwin one two with
      | some data => some (selection.leftPhaseOwnerFibreReceive A strategy hwin
          data input)
      | none => none

/-- Process-one receive transition. -/
noncomputable def ownerFibreBoundaryOpenRecvOne
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂) :
    OneControl A strategy hwin × Out₁ :=
  match selection.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.1.1.openControl, result.1.2)
  | none =>
      profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin one
        inputOne

/-- Process-two receive transition. -/
noncomputable def ownerFibreBoundaryOpenRecvTwo
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (one : OneControl A strategy hwin) (inputOne : In₁) :
    TwoControl A strategy hwin × Out₂ :=
  match selection.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.2.1.openControl, result.2.2)
  | none =>
      profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin two
        inputTwo

/-- Simultaneous receive, retaining the outputs that the legacy projection
discarded. -/
noncomputable def ownerFibreBoundaryCloseRound
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂) :
    (OneControl A strategy hwin × TwoControl A strategy hwin) ×
      (Out₁ × Out₂) :=
  match selection.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result =>
      ((result.1.1.closedControl, result.2.1.closedControl),
        (result.1.2, result.2.2))
  | none =>
      let nextOne :=
        profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne
      let nextTwo :=
        profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))

/-! ## Exact finite closed-loop round -/

/-- One physical round of the selection-relative owner-fibre kernel,
including both endpoint outputs. -/
noncomputable def ownerFibreRound
    (controls : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) (graph : Graph) :
    (OneControl A strategy hwin × TwoControl A strategy hwin) ×
      (Out₁ × Out₂) :=
  match graph with
  | .right =>
      let nextOne :=
        profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          controls.1 input.1
      let nextTwo := selection.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        controls.2 input.2 controls.1 input.1
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))
  | .left =>
      let nextOne := selection.ownerFibreBoundaryOpenRecvOne A strategy hwin
        controls.1 input.1 controls.2 input.2
      let nextTwo :=
        profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          controls.2 input.2
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))
  | .both =>
      selection.ownerFibreBoundaryCloseRound A strategy hwin controls.1
        input.1 controls.2 input.2

/-- The round record seen by the objective automaton. -/
noncomputable def ownerFibreRoundRecord
    (controls : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) (graph : Graph) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let result := selection.ownerFibreRound A strategy hwin controls input graph
  { inputOne := input.1
    inputTwo := input.2
    graph := graph
    outputOne := result.2.1
    outputTwo := result.2.2 }

/-! ## Regression bridge -/

@[simp] theorem default_rightBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).rightBoundaryOwnerFibreReceive A strategy hwin data
        oldState oldOwner input =
      data.ownerFibreReceive A strategy hwin oldState oldOwner input :=
  rfl

@[simp] theorem default_leftBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).leftBoundaryOwnerFibreReceive A strategy hwin data
        oldState oldOwner input =
      data.ownerFibreReceive A strategy hwin oldState oldOwner input :=
  rfl

@[simp] theorem default_rightPhaseOwnerFibreReceive
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).rightPhaseOwnerFibreReceive A strategy hwin data input =
      data.ownerFibreReceive A strategy hwin input := by
  simp only [rightPhaseOwnerFibreReceive,
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
    default_rightBoundaryOwnerFibreReceive]

@[simp] theorem default_leftPhaseOwnerFibreReceive
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).leftPhaseOwnerFibreReceive A strategy hwin data input =
      data.ownerFibreReceive A strategy hwin input := by
  simp only [leftPhaseOwnerFibreReceive,
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
    default_leftBoundaryOwnerFibreReceive]

@[simp] theorem default_ownerFibreBoundaryReceive?
    (one : OneControl A strategy hwin)
    (two : TwoControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).ownerFibreBoundaryReceive? A strategy hwin one two input =
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one
        two input := by
  simp only [ownerFibreBoundaryReceive?,
    profiledRawJointRecurrentOwnerFibreBoundaryReceive?,
    default_rightPhaseOwnerFibreReceive, default_leftPhaseOwnerFibreReceive]
  rfl

@[simp] theorem default_ownerFibreBoundaryOpenRecvOne
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).ownerFibreBoundaryOpenRecvOne A strategy hwin one
        inputOne two inputTwo =
      profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one inputOne two inputTwo := by
  rw [ownerFibreBoundaryOpenRecvOne,
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
    default_ownerFibreBoundaryReceive?]
  rfl

@[simp] theorem default_ownerFibreBoundaryOpenRecvTwo
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (one : OneControl A strategy hwin) (inputOne : In₁) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).ownerFibreBoundaryOpenRecvTwo A strategy hwin two
        inputTwo one inputOne =
      profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two inputTwo one inputOne := by
  rw [ownerFibreBoundaryOpenRecvTwo,
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
    default_ownerFibreBoundaryReceive?]
  rfl

/-- The control projection of the default selected close is the legacy close. -/
@[simp] theorem default_ownerFibreBoundaryCloseRound_controls
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂) :
    ((profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).ownerFibreBoundaryCloseRound A strategy hwin one
        inputOne two inputTwo).1 =
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        inputOne two inputTwo := by
  rw [ownerFibreBoundaryCloseRound,
    profiledRawJointRecurrentOwnerFibreBoundaryClose,
    default_ownerFibreBoundaryReceive?]
  split <;> rename_i hreceive
  · rw [hreceive]
  · rw [hreceive]

end ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
