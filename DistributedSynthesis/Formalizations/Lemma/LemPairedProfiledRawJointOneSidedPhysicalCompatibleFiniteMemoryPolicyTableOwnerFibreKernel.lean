/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableBankLocalInformedBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreKernel

/-!
# Owner-fibre kernel executed directly from a finite policy table

This is the selection-free executable form of the augmented owner-fibre
kernel.  Its only policy parameter is a genuinely finite successor-table
family.  It does not require local validity, forward parity, reachability, or
owner safety in order to take a total step; those are obligations for the
enriched verifier.

If the table is later certified, the final agreement theorems identify every
raw receive, round, and emitted record with the previously verified
selection-relative kernel.
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

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (tables :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) A strategy)

/-- Resolve a right boundary and initialize its process-one owner-fibre
fork. -/
def rightBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := Memory) A strategy)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy) ×
      Out₁ :=
  let packet := tables.resolvePacket A strategy hwin data.1
    (data.target (Memory := Memory) A strategy input)
  profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
    (Memory := Memory) A strategy
      ⟨(data.receiver (Memory := Memory) A strategy).1,
        data.owner (Memory := Memory) A strategy⟩
      oldState data.2.2 oldOwner packet input

/-- Left-orientation mirror of the raw table packet seam. -/
def leftBoundaryOwnerFibreReceive
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := Memory) A strategy)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy) ×
      Out₂ :=
  let packet := tables.resolvePacket A strategy hwin data.1
    (data.target (Memory := Memory) A strategy input)
  profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
    (Memory := Memory) A strategy
      ⟨(data.receiver (Memory := Memory) A strategy).1,
        data.owner (Memory := Memory) A strategy⟩
      oldState data.2.2 oldOwner packet (input.2, input.1)

/-- Execute a decoded right boundary in both endpoint coordinates. -/
def rightPhaseOwnerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
      (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂) :=
  let data := phaseData.1
  let phaseOne := tables.rightBoundaryOwnerFibreReceive A strategy hwin data
    phaseData.2.1 phaseData.2.2 input
  let bridgeTwo := tables.rightToLeftBridgeForkTwo A strategy hwin data.1
    (data.receiver (Memory := Memory) A strategy)
    (data.owner (Memory := Memory) A strategy) (input.2, input.1)
  let packet := tables.resolvePacket A strategy hwin data.1
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

/-- Execute a decoded left boundary in both endpoint coordinates. -/
def leftPhaseOwnerFibreReceive
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
      (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂) :=
  let data := phaseData.1
  let bridgeOne := tables.leftToRightBridgeForkOne A strategy hwin data.1
    (data.receiver (Memory := Memory) A strategy)
    (data.owner (Memory := Memory) A strategy) input
  let phaseTwo := tables.leftBoundaryOwnerFibreReceive A strategy hwin data
    phaseData.2.1 phaseData.2.2 input
  let packet := tables.resolvePacket A strategy hwin data.1
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

/-- Decode the active orientation and execute its raw-table informed
receive. -/
def ownerFibreBoundaryReceive?
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
      some (tables.rightPhaseOwnerFibreReceive A strategy hwin data input)
  | none =>
      match
          profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
            (Memory := Memory) A strategy one two with
      | some data =>
          some (tables.leftPhaseOwnerFibreReceive A strategy hwin data input)
      | none => none

/-- Process-one transition on a receive edge. -/
def ownerFibreBoundaryOpenRecvOne
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂) :
    OneControl (Memory := Memory) A strategy × Out₁ :=
  match tables.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.1.1.openControl, result.1.2)
  | none =>
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := Memory) A strategy one inputOne

/-- Process-two transition on a receive edge. -/
def ownerFibreBoundaryOpenRecvTwo
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁) :
    TwoControl (Memory := Memory) A strategy × Out₂ :=
  match tables.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.2.1.openControl, result.2.2)
  | none =>
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := Memory) A strategy two inputTwo

/-- Simultaneous receive, retaining both literal outputs. -/
def ownerFibreBoundaryCloseRound
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂) :
    (OneControl (Memory := Memory) A strategy ×
        TwoControl (Memory := Memory) A strategy) ×
      (Out₁ × Out₂) :=
  match tables.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
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

/-- One total physical round of the raw finite-table kernel. -/
def ownerFibreRound
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
      let nextTwo := tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        controls.2 input.2 controls.1 input.1
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))
  | .left =>
      let nextOne := tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        controls.1 input.1 controls.2 input.2
      let nextTwo :=
        profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := Memory) A strategy controls.2 input.2
      ((nextOne.1, nextTwo.1), (nextOne.2, nextTwo.2))
  | .both =>
      tables.ownerFibreBoundaryCloseRound A strategy hwin controls.1 input.1
        controls.2 input.2

/-- Literal objective record emitted by the raw finite-table kernel. -/
def ownerFibreRoundRecord
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let result := tables.ownerFibreRound A strategy hwin controls input graph
  { inputOne := input.1
    inputTwo := input.2
    graph := graph
    outputOne := result.2.1
    outputTwo := result.2.2 }

/-! ## Exact agreement after certification -/

/-- Certifying a table does not alter the decoded receive result. -/
theorem ownerFibreBoundaryReceive_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (one : OneControl (Memory := Memory) A strategy)
    (two : TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    tables.ownerFibreBoundaryReceive? A strategy hwin one two input =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreBoundaryReceive?
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        one two input := by
  rfl

/-- Certifying a table does not alter a complete physical round. -/
theorem ownerFibreRound_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    tables.ownerFibreRound A strategy hwin controls input graph =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRound
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        controls input graph := by
  rfl

/-- Certifying a table does not alter the literal objective record. -/
theorem ownerFibreRoundRecord_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph) :
    tables.ownerFibreRoundRecord A strategy hwin controls input graph =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRoundRecord
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        controls input graph := by
  rfl

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

end

end DetParityAutomaton

end DistributedSynthesis
