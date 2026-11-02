/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalBoundary

/-!
# Resolving augmented bank packets directly from finite transition tables

The enriched automaton must run the bank while its chosen transition table is
still being checked.  It therefore cannot call a resolver parameterized by a
certified policy.  This file defines the same resolver directly from the
finite table family.

The final agreement theorems are exact equalities.  After local validity and
forward parity certify a table family, target realization, deterministic
choice, and the complete packet (including its memory successor) coincide
with the existing selected-policy bank.
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

/-- A requested bare target is realized by one literal semantic child whose
public augmented successor is the one stored in the finite table.  The raw
move is only an existential witness and is not part of the table data. -/
def ChildRealizes
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A) : Prop :=
  ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        source.code A = state.2.1.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source state.2.1.1.2 ∧
          (∀ direction,
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
                source state.2.1.1.2 direction =
              move.2 direction) ∧
          childCode = sourceFreeBeliefParentLinkedNext
            (profiledRawJointOneSidedNext A) state.2.1.1 move actual ∧
          childCode.1 = target ∧
          (tables.successor A strategy state childCode).2.1 =
            (childCode,
              (PolicyDPA A state.1.1.1).step state.2.1.2 childCode)

omit [Fintype Memory] in
/-- Total deterministic resolver obtained from the finite realization
predicate.  The fallback is used only when no realizing child exists. -/
def resolveTarget
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : LinkedCode A := by
  classical
  exact if h : ∃ childCode,
      tables.ChildRealizes A strategy hwin state target
        childCode then
    Classical.choose h
  else
    state.2.1.1

omit [Fintype Memory] in
theorem resolveTarget_realizes
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hexists : ∃ childCode,
      tables.ChildRealizes A strategy hwin state target
        childCode) :
    tables.ChildRealizes A strategy hwin state target
      (tables.resolveTarget A strategy hwin state target) := by
  classical
  simp only [resolveTarget]
  split
  next h => exact Classical.choose_spec h
  next h => exact (h hexists).elim

/-- Resolve a target to the complete finite-memory packet used by the
endpoint kernels. -/
def resolvePacket
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
      (Memory := Memory) A strategy :=
  let childCode :=
    tables.resolveTarget A strategy hwin state target
  ⟨target, childCode, tables.successor A strategy state childCode⟩

section
omit [Fintype Memory]

@[simp] theorem resolvePacket_target
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (tables.resolvePacket A strategy hwin state target).target =
      target :=
  rfl

@[simp] theorem resolvePacket_childCode
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (tables.resolvePacket A strategy hwin state
      target).childCode =
        tables.resolveTarget A strategy hwin state target :=
  rfl

@[simp] theorem resolvePacket_successor
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (tables.resolvePacket A strategy hwin state
      target).successor =
        tables.successor A strategy state
          (tables.resolveTarget A strategy hwin state target) :=
  rfl

end

/-- Certification leaves the literal child-realization predicate unchanged. -/
theorem childRealizes_toPolicySelection_iff
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A) :
    tables.ChildRealizes A strategy hwin state target childCode ↔
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ChildRealizes
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state target childCode := by
  rfl

/-- Certification leaves the deterministic target choice unchanged. -/
theorem resolveTarget_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    tables.resolveTarget A strategy hwin state target =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.resolveTarget
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state target := by
  rfl

/-- Certification leaves the entire resolved packet unchanged, including the
additional memory coordinate of its successor. -/
theorem resolvePacket_toPolicySelection
    (hvalid : tables.ValidAt A strategy hwin initialMemory)
    (haccepts : tables.Accepts A strategy initialMemory)
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    tables.resolvePacket A strategy hwin state target =
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.resolvePacket
        A strategy hwin initialMemory
        (tables.toPolicySelection A strategy hwin initialMemory hvalid haccepts)
        state target := by
  rfl

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

end

end DetParityAutomaton

end DistributedSynthesis
