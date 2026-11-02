/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalEndpointDecoder

/-!
# Finite-memory owner-fibre kernel for a replaceable policy selection

This file closes the executable seam between an augmented finite-memory policy
selection and the two endpoint controls.  The selected policy is consulted
only when an informed boundary resolves its target packet.  Every later blind
step uses the finite endpoint-local maps already carried by the controls.

The top-level round returns both next endpoint controls and both literal
outputs.  The associated round record is therefore suitable for a direct
product with the objective parity automaton.  The option-valued decoder keeps
the transition total on malformed control pairs; the final theorem in the
decoder section proves that the explicit decoding invariant rules out this
fallback.
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

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

private abbrev OneControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
    (Memory := Memory) A strategy

private abbrev TwoControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
    (Memory := Memory) A strategy

private abbrev PolicySelection
    (initialMemory : RootKey A strategy → Memory) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
    (Memory := Memory) A strategy hwin initialMemory

/-! ## Literal targets exposed by decoded boundaries -/

/-- Target printed by the informed right receiver on the current input. -/
noncomputable def ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  let receiver := data.receiver (Memory := Memory) A strategy
  (((receiver.1.memberController A false).labelOf
      (data.owner (Memory := Memory) A strategy)).2 receiver.2.2.1
        (input.2, input.1) |>.target receiver.2.1)

/-- Target printed by the informed left receiver on the current input. -/
noncomputable def ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  let receiver := data.receiver (Memory := Memory) A strategy
  (((receiver.1.memberController A false).labelOf
      (data.owner (Memory := Memory) A strategy)).2 receiver.2.2.1 input
        |>.target receiver.2.1)

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection : PolicySelection (Memory := Memory) A strategy hwin
    initialMemory)

/-! ## The selected-policy packet seam -/

/-- Resolve a right boundary and initialize its process-one owner-fibre fork. -/
noncomputable def rightBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := Memory) A strategy)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy) ×
      Out₁ :=
  let packet := selection.resolvePacket A strategy hwin initialMemory data.1
    (data.target (Memory := Memory) A strategy input)
  profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
    (Memory := Memory) A strategy
      ⟨(data.receiver (Memory := Memory) A strategy).1,
        data.owner (Memory := Memory) A strategy⟩
      oldState data.2.2 oldOwner packet input

/-- Mirrored packet seam at a left boundary. -/
noncomputable def leftBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := Memory) A strategy)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy) ×
      Out₂ :=
  let packet := selection.resolvePacket A strategy hwin initialMemory data.1
    (data.target (Memory := Memory) A strategy input)
  profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
    (Memory := Memory) A strategy
      ⟨(data.receiver (Memory := Memory) A strategy).1,
        data.owner (Memory := Memory) A strategy⟩
      oldState data.2.2 oldOwner packet (input.2, input.1)

/-! ## Two-endpoint informed receives -/

/-- Lift a decoded right boundary to the two augmented endpoint controls. -/
noncomputable def rightPhaseOwnerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
      (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂) :=
  let data := phaseData.1
  let phaseOne := selection.rightBoundaryOwnerFibreReceive A strategy hwin
    initialMemory data phaseData.2.1 phaseData.2.2 input
  let bridgeTwo := selection.rightToLeftBridgeForkTwo A strategy hwin
    initialMemory data.1 (data.receiver (Memory := Memory) A strategy)
      (data.owner (Memory := Memory) A strategy) (input.2, input.1)
  let packet := selection.resolvePacket A strategy hwin initialMemory data.1
    (data.target (Memory := Memory) A strategy input)
  let successor := packet.successor
  let oneFork :
      FiniteDelayedFork (OneControl (Memory := Memory) A strategy) :=
    ⟨(.inr phaseOne.1.openControl, data.1, phaseData.2.1),
      (.inr phaseOne.1.closedControl, data.1, successor)⟩
  let twoFork :
      FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) :=
    ⟨(.inl bridgeTwo.1.openControl, data.1, successor),
      (.inl bridgeTwo.1.closedControl, data.1, successor)⟩
  ((oneFork, phaseOne.2), (twoFork, bridgeTwo.2))

/-- Lift a decoded left boundary to the two augmented endpoint controls. -/
noncomputable def leftPhaseOwnerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
      (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂) :=
  let data := phaseData.1
  let bridgeOne := selection.leftToRightBridgeForkOne A strategy hwin
    initialMemory data.1 (data.receiver (Memory := Memory) A strategy)
      (data.owner (Memory := Memory) A strategy) input
  let phaseTwo := selection.leftBoundaryOwnerFibreReceive A strategy hwin
    initialMemory data phaseData.2.1 phaseData.2.2 input
  let packet := selection.resolvePacket A strategy hwin initialMemory data.1
    (data.target (Memory := Memory) A strategy input)
  let successor := packet.successor
  let oneFork :
      FiniteDelayedFork (OneControl (Memory := Memory) A strategy) :=
    ⟨(.inl bridgeOne.1.openControl, successor, data.1),
      (.inl bridgeOne.1.closedControl, successor, data.1)⟩
  let twoFork :
      FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) :=
    ⟨(.inr phaseTwo.1.openControl, phaseData.2.1, data.1),
      (.inr phaseTwo.1.closedControl, successor, data.1)⟩
  ((oneFork, bridgeOne.2), (twoFork, phaseTwo.2))

/-! ## Decoder and total local transitions -/

/-- Decode the active orientation and execute its selected informed receive. -/
noncomputable def ownerFibreBoundaryReceive?
    (one : OneControl (Memory := Memory) A strategy)
    (two : TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    Option
      ((FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
        (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) ×
          Out₂)) :=
  match
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy one two with
  | some data =>
      some (selection.rightPhaseOwnerFibreReceive A strategy hwin
        initialMemory data input)
  | none =>
      match
          profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
            (Memory := Memory) A strategy one two with
      | some data =>
          some (selection.leftPhaseOwnerFibreReceive A strategy hwin
            initialMemory data input)
      | none => none

/-- A decodable control pair cannot take the malformed-state fallback. -/
theorem exists_ownerFibreBoundaryReceive_of_decodes
    (one : OneControl (Memory := Memory) A strategy)
    (two : TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (hdecodes :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
        (Memory := Memory) A strategy one two) :
    ∃ result,
      selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory
        one two input = some result := by
  rcases hdecodes with ⟨rightData, hright⟩ | ⟨leftData, hleft⟩
  · refine
      ⟨selection.rightPhaseOwnerFibreReceive A strategy hwin initialMemory
        rightData input, ?_⟩
    simp [ownerFibreBoundaryReceive?, hright]
  · cases hright :
        profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := Memory) A strategy one two with
    | none =>
        refine
          ⟨selection.leftPhaseOwnerFibreReceive A strategy hwin initialMemory
            leftData input, ?_⟩
        simp [ownerFibreBoundaryReceive?, hright, hleft]
    | some rightData =>
        refine
          ⟨selection.rightPhaseOwnerFibreReceive A strategy hwin
            initialMemory rightData input, ?_⟩
        simp [ownerFibreBoundaryReceive?, hright]

/-- Process-one transition on a receive edge. -/
noncomputable def ownerFibreBoundaryOpenRecvOne
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂) :
    OneControl (Memory := Memory) A strategy × Out₁ :=
  match selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory
      one two (inputOne, inputTwo) with
  | some result => (result.1.1.openControl, result.1.2)
  | none =>
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := Memory) A strategy one inputOne

/-- Process-two transition on a receive edge. -/
noncomputable def ownerFibreBoundaryOpenRecvTwo
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁) :
    TwoControl (Memory := Memory) A strategy × Out₂ :=
  match selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory
      one two (inputOne, inputTwo) with
  | some result => (result.2.1.openControl, result.2.2)
  | none =>
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := Memory) A strategy two inputTwo

/-- Simultaneous receive, retaining both literal outputs. -/
noncomputable def ownerFibreBoundaryCloseRound
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂) :
    (OneControl (Memory := Memory) A strategy ×
        TwoControl (Memory := Memory) A strategy) ×
      (Out₁ × Out₂) :=
  match selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory
      one two (inputOne, inputTwo) with
  | some result =>
      ((result.1.1.closedControl, result.2.1.closedControl),
        (result.1.2, result.2.2))
  | none =>
      let nextOne :=
        profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := Memory) A strategy one inputOne
      let nextTwo :=
        profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := Memory) A strategy two inputTwo
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))

@[simp] theorem ownerFibreBoundaryOpenRecvOne_of_some
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (result :
      (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
        (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂))
    (hreceive :
      selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory
        one two (inputOne, inputTwo) = some result) :
    selection.ownerFibreBoundaryOpenRecvOne A strategy hwin initialMemory one
        inputOne two inputTwo =
      (result.1.1.openControl, result.1.2) := by
  simp [ownerFibreBoundaryOpenRecvOne, hreceive]

@[simp] theorem ownerFibreBoundaryOpenRecvTwo_of_some
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (result :
      (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
        (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂))
    (hreceive :
      selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory
        one two (inputOne, inputTwo) = some result) :
    selection.ownerFibreBoundaryOpenRecvTwo A strategy hwin initialMemory two
        inputTwo one inputOne =
      (result.2.1.openControl, result.2.2) := by
  simp [ownerFibreBoundaryOpenRecvTwo, hreceive]

@[simp] theorem ownerFibreBoundaryCloseRound_of_some
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (result :
      (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
        (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂))
    (hreceive :
      selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory
        one two (inputOne, inputTwo) = some result) :
    selection.ownerFibreBoundaryCloseRound A strategy hwin initialMemory one
        inputOne two inputTwo =
      ((result.1.1.closedControl, result.2.1.closedControl),
        (result.1.2, result.2.2)) := by
  simp [ownerFibreBoundaryCloseRound, hreceive]

/-! ## Exact finite closed-loop round -/

/-- One physical round, with no output projection or semantic oracle. -/
noncomputable def ownerFibreRound
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    (OneControl (Memory := Memory) A strategy ×
        TwoControl (Memory := Memory) A strategy) ×
      (Out₁ × Out₂) :=
  match graph with
  | .right =>
      let nextOne :=
        profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := Memory) A strategy controls.1 input.1
      let nextTwo := selection.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        initialMemory controls.2 input.2 controls.1 input.1
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))
  | .left =>
      let nextOne := selection.ownerFibreBoundaryOpenRecvOne A strategy hwin
        initialMemory controls.1 input.1 controls.2 input.2
      let nextTwo :=
        profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := Memory) A strategy controls.2 input.2
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))
  | .both =>
      selection.ownerFibreBoundaryCloseRound A strategy hwin initialMemory
        controls.1 input.1 controls.2 input.2

/-- Literal round record consumed by the objective automaton. -/
noncomputable def ownerFibreRoundRecord
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let result := selection.ownerFibreRound A strategy hwin initialMemory
    controls input graph
  { inputOne := input.1
    inputTwo := input.2
    graph := graph
    outputOne := result.2.1
    outputTwo := result.2.2 }

@[simp] theorem ownerFibreRoundRecord_inputOne
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    (selection.ownerFibreRoundRecord A strategy hwin initialMemory controls
      input graph).inputOne = input.1 :=
  rfl

@[simp] theorem ownerFibreRoundRecord_inputTwo
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    (selection.ownerFibreRoundRecord A strategy hwin initialMemory controls
      input graph).inputTwo = input.2 :=
  rfl

@[simp] theorem ownerFibreRoundRecord_graph
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    (selection.ownerFibreRoundRecord A strategy hwin initialMemory controls
      input graph).graph = graph :=
  rfl

@[simp] theorem ownerFibreRoundRecord_outputOne
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    (selection.ownerFibreRoundRecord A strategy hwin initialMemory controls
      input graph).outputOne =
        (selection.ownerFibreRound A strategy hwin initialMemory controls input
          graph).2.1 :=
  rfl

@[simp] theorem ownerFibreRoundRecord_outputTwo
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    (selection.ownerFibreRoundRecord A strategy hwin initialMemory controls
      input graph).outputTwo =
        (selection.ownerFibreRound A strategy hwin initialMemory controls input
          graph).2.2 :=
  rfl

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
