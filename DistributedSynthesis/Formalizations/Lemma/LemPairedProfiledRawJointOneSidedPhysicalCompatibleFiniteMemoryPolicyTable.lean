/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityFiniteMemoryStationaryPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBank

/-!
# Finite transition tables for the augmented physical-compatible policy bank

The selected-policy bank is convenient after legality and forward parity have
been proved, but it cannot be the existential label of the enriched automaton:
its policy type already contains those proofs.  This file gives the bank its
finite executable presentation first.  A table family chooses one augmented
successor for every finite public child-code request at every augmented state
of every root key.

The raw lambda move is intentionally not stored: that type can be infinite.
Instead, `ValidAt` requires a node-local raw move which realizes the complete
finite public successor map.  `Accepts` is a separate proposition.  Once both
hold, the table family induces the existing certified policy selection, and
its root and successor operations are literally the table operations.
Conversely, every certified selection yields such a table family.
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

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := ActualDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev PolicyDPA
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointOneSidedCodeParityDPA A initialCode)

private abbrev PolicyValid :=
  sourceFreeBeliefParentLinkedValid
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy hwin)

private noncomputable abbrev PolicyNext :
    LinkedCode A →
      LinkedMove A (In₁ := In₁) (In₂ := In₂) →
        LinkedCode A → LinkedCode A :=
  sourceFreeBeliefFiniteCodeNext
    (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))

/-- Finite executable successor table at one realizable root key. -/
abbrev
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
    (key : RootKey A strategy) :=
  SourceFreeBeliefCodeParityFiniteMemoryTransitionTable
    (PolicyDPA A key.1.1) Memory (LinkedCode A)

noncomputable instance
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableFintype
    (key : RootKey A strategy) :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key) := by
  infer_instance

/-- One finite executable table for every realizable root key. -/
abbrev
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection :=
  ∀ key : RootKey A strategy,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
      (Memory := Memory) A strategy key

noncomputable instance
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelectionFintype :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (tables :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) A strategy)

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

/-- Extend one fixed-key table to a total table family.  Other roots receive
the identity table and are operationally irrelevant to a kernel confined to
`key`.  This avoids storing a Cartesian product of choices for unrelated root
keys in the fixed-key enriched automaton. -/
def singletonAt
    (key : RootKey A strategy)
    (table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) A strategy := by
  classical
  intro other
  by_cases h : other = key
  · subst other
    exact table
  · exact ⟨fun state _childCode ↦ state⟩

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem singletonAt_apply_key
    (key : RootKey A strategy)
    (table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key) :
    (singletonAt (Memory := Memory) A strategy key table) key = table := by
  simp [singletonAt]

/-- Initial table control at one root key. -/
def root (key : RootKey A strategy) :
    BankControl (Memory := Memory) A strategy :=
  ⟨key, ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)⟩

/-- Execute one table transition.  The root key is unchanged, the public
coordinates are forced, and only the memory update is read from the table. -/
def successor
    (state : BankControl (Memory := Memory) A strategy)
    (childCode : LinkedCode A) :
    BankControl (Memory := Memory) A strategy :=
  ⟨state.1,
    (tables state.1).successor state.2 childCode⟩

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem root_index (key : RootKey A strategy) :
    (root A strategy initialMemory key).1 = key :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem successor_index
    (state : BankControl (Memory := Memory) A strategy)
    (childCode : LinkedCode A) :
    (tables.successor A strategy state childCode).1 = state.1 :=
  rfl

/-- All table moves are locally physical-compatible on table-reachable
augmented states. -/
def ValidAt : Prop :=
  ∀ key : RootKey A strategy,
    (tables key).ValidAt
      (PolicyDPA A key.1.1) key.1 (initialMemory key)
      (PolicyValid A strategy hwin)
      (PolicyNext A (In₁ := In₁) (In₂ := In₂))

/-- Every branch of every root table satisfies the forward objective. -/
def Accepts : Prop :=
  ∀ key : RootKey A strategy,
    (tables key).Accepts
      (PolicyDPA A key.1.1) key.1 (initialMemory key)

/-- Add the local-validity and universal-parity proofs to an executable table
family. -/
def toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
      (Memory := Memory) A strategy hwin initialMemory :=
  fun key ↦
    (tables key).toFiniteMemoryPolicy
      (PolicyDPA A key.1.1) key.1 (initialMemory key)
      (PolicyValid A strategy hwin)
      (PolicyNext A (In₁ := In₁) (In₂ := In₂))
      (hvalid key) (haccepts key)

/-- Certification does not alter the table root. -/
@[simp] theorem toPolicySelection_root
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (key : RootKey A strategy) :
    (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts).root
        A strategy hwin initialMemory key =
      root A strategy initialMemory key :=
  rfl

/-- Certification does not alter any executable table successor. -/
@[simp] theorem toPolicySelection_successor
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (childCode : LinkedCode A) :
    (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts).successor
        A strategy hwin initialMemory state childCode =
      tables.successor A strategy state childCode :=
  rfl

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

/-- Exact data/proof separation for model-specific policy selections. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection_iff
    (initialMemory : RootKey A strategy → Memory) :
    (∃ tables :
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
          (Memory := Memory) A strategy,
      tables.ValidAt A strategy hwin initialMemory ∧
        tables.Accepts A strategy initialMemory) ↔
      Nonempty
        (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
          (Memory := Memory) A strategy hwin initialMemory) := by
  constructor
  · rintro ⟨tables, hvalid, haccepts⟩
    exact ⟨tables.toPolicySelection A strategy hwin initialMemory hvalid
      haccepts⟩
  · rintro ⟨selection⟩
    let tables :
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
          (Memory := Memory) A strategy :=
      fun key ↦
        (selection key).transitionTable
          (PolicyDPA A key.1.1) key.1 (initialMemory key)
          (PolicyValid A strategy hwin)
          (PolicyNext A (In₁ := In₁) (In₂ := In₂))
    refine ⟨tables, ?_, ?_⟩
    · intro key
      exact
        (selection key).transitionTable_validAt
          (PolicyDPA A key.1.1) key.1 (initialMemory key)
          (PolicyValid A strategy hwin)
          (PolicyNext A (In₁ := In₁) (In₂ := In₂))
    · intro key
      exact
        (selection key).transitionTable_accepts
          (PolicyDPA A key.1.1) key.1 (initialMemory key)
          (PolicyValid A strategy hwin)
          (PolicyNext A (In₁ := In₁) (In₂ := In₂))

end

end DetParityAutomaton

end DistributedSynthesis
