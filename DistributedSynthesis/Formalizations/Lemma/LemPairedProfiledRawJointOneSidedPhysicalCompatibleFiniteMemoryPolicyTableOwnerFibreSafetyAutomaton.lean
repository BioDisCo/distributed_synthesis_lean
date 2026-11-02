/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableOwnerFibreKernel
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreSafetyAutomaton

/-!
# Guarded owner-fibre safety for an uncertified finite policy table

This module runs the existing rejecting-sink decoder monitor directly over a
raw finite policy table.  Consequently it is meaningful inside the
transition relation of the future choice automaton, before either forward
parity or owner safety has been proved.  Certification changes none of its
states, priorities, or transitions.
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

private abbrev Direction :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
    (In₁ := In₁) (In₂ := In₂)

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev SafetyState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
    (Memory := Memory) A strategy

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (tables :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) A strategy)

/-- Exact live product step driven by a raw finite transition table. -/
def ownerFibreSafetyLiveStep
    (state : LiveState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    LiveState (Memory := Memory) A strategy :=
  let result := tables.ownerFibreRound A strategy hwin state.1 direction.1
    direction.2
  (result.1,
    A.step state.2
      (tables.ownerFibreRoundRecord A strategy hwin state.1 direction.1
        direction.2))

/-- Literal live state after a finite environment history. -/
def ownerFibreSafetyLiveStateAt
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂))) :
    LiveState (Memory := Memory) A strategy :=
  node.foldl (tables.ownerFibreSafetyLiveStep A strategy hwin) initial

/-- Guard the raw live step by the structural decoder. -/
def ownerFibreSafetyStep
    (state : SafetyState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    SafetyState (Memory := Memory) A strategy := by
  classical
  exact
    match state with
    | none => none
    | some live =>
        if ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := Memory) A strategy live.1.1 live.1.2 then
          some (tables.ownerFibreSafetyLiveStep A strategy hwin live direction)
        else none

/-- Monitored raw-table state after a finite environment history. -/
def ownerFibreSafetyStateAt
    (initial : SafetyState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂))) :
    SafetyState (Memory := Memory) A strategy :=
  node.foldl (tables.ownerFibreSafetyStep A strategy hwin) initial

/-- Exact guarded owner-fibre obligation for one possibly failing raw-table
entry state. -/
def OwnerFibreSafe
    (initial : SafetyState (Memory := Memory) A strategy) : Prop :=
  ∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
    NatSeqMinEvenParity
      (fun n ↦
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority
          (Memory := Memory) A strategy
          (tables.ownerFibreSafetyStateAt A strategy hwin initial
            (branchNode branch n)))

omit [Fintype Memory] in
@[simp] theorem ownerFibreSafetyStep_none
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    tables.ownerFibreSafetyStep A strategy hwin none direction = none :=
  rfl

/-- Certification leaves the guarded table step unchanged. -/
theorem ownerFibreSafetyStep_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : SafetyState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    tables.ownerFibreSafetyStep A strategy hwin state direction =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyStep
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state direction := by
  rfl

/-- Certification leaves every finite monitored prefix unchanged. -/
theorem ownerFibreSafetyStateAt_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (initial : SafetyState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂))) :
    tables.ownerFibreSafetyStateAt A strategy hwin initial node =
      node.foldl
        (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyStep
          A strategy hwin initialMemory
          (tables.toPolicySelection A strategy hwin initialMemory hvalid
            haccepts))
        initial := by
  rfl

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

end

end DetParityAutomaton

end DistributedSynthesis
