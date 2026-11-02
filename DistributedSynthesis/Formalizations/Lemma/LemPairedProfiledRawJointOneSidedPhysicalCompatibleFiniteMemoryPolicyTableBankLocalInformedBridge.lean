/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalInformedBridge

/-!
# Informed reversal bridges executed from finite policy tables

Only an informed receive consults the policy resolver.  The delayed bridge
controls themselves already contain all data needed by later blind steps.
This file replaces the certified-selection resolver at those two informed
seams by the raw finite-table resolver and proves exact agreement after the
table is certified.
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

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (tables :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) A strategy)

/-- Advance the installed right receiver and stage the packet resolved by the
raw finite transition table. -/
def rightReceiveFor
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
        (Memory := Memory) A strategy × Out₂ :=
  let next := stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  match next.2.2.2.2 with
  | none => ((state, next.2, none), next.1)
  | some target =>
      ((state, next.2,
        some (tables.resolvePacket A strategy hwin state target)), next.1)

/-- Process-two reversal fork produced at an informed right receive. -/
def rightToLeftBridgeForkTwo
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
          (Memory := Memory) A strategy) × Out₂ :=
  let next := tables.rightReceiveFor A strategy hwin state receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet := tables.resolvePacket A strategy hwin state target
  let openControl :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy :=
    .inl next.1
  match packet.successor.2.1.1.2.2 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1)⟩,
        next.2)

/-- Advance the installed left receiver and stage the packet resolved by the
raw finite transition table. -/
def leftReceiveFor
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
        (Memory := Memory) A strategy × Out₁ :=
  let next := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  match next.2.2.2.2 with
  | none => ((state, next.2, none), next.1)
  | some target =>
      ((state, next.2,
        some (tables.resolvePacket A strategy hwin state target)), next.1)

/-- Process-one reversal fork produced at an informed left receive. -/
def leftToRightBridgeForkOne
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
          (Memory := Memory) A strategy) × Out₁ :=
  let next := tables.leftReceiveFor A strategy hwin state receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet := tables.resolvePacket A strategy hwin state target
  let openControl :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy :=
    .inl next.1
  match packet.successor.2.1.1.2.1 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1)⟩,
        next.2)

/-- Certification does not alter an informed right receive. -/
theorem rightReceiveFor_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    tables.rightReceiveFor A strategy hwin state receiver owner input =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.rightReceiveFor
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state receiver owner input := by
  rfl

/-- Certification does not alter the right-to-left fork. -/
theorem rightToLeftBridgeForkTwo_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    tables.rightToLeftBridgeForkTwo A strategy hwin state receiver owner input =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.rightToLeftBridgeForkTwo
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state receiver owner input := by
  rfl

/-- Certification does not alter an informed left receive. -/
theorem leftReceiveFor_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    tables.leftReceiveFor A strategy hwin state receiver owner input =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.leftReceiveFor
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state receiver owner input := by
  rfl

/-- Certification does not alter the left-to-right fork. -/
theorem leftToRightBridgeForkOne_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    tables.leftToRightBridgeForkOne A strategy hwin state receiver owner input =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.leftToRightBridgeForkOne
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state receiver owner input := by
  rfl

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

end

end DetParityAutomaton

end DistributedSynthesis
