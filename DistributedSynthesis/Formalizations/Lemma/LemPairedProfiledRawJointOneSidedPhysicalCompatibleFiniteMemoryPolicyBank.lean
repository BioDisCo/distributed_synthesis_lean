/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankSelection

/-!
# A recurrent bank with explicit finite policy memory

This file lifts the root/successor/resolver core of the recurrent bank to the
finite-memory policy interface.  The root key remains exactly the old public
pair `(incidence code, installed physical table)`.  Only the policy control
stored below that key gains a finite memory coordinate.

The target resolver still chooses a literal parent-linked semantic child.  Its
public code and forward-parity state are forced by the semantic move; its
additional memory is advanced by the selected augmented policy.
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

/-- One augmented physical-compatible policy for every realizable root. -/
abbrev
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
    (initialMemory : RootKey A strategy → Memory) :=
  ∀ key : RootKey A strategy,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
      (Memory := Memory) A strategy hwin (initialMemory key) key.1.1 key.1.2

/-- Runtime state of an augmented bank. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl :=
  Σ key : RootKey A strategy,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
      (Memory := Memory) A key.1.1

noncomputable instance
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControlFintype :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
      (Memory := Memory) A strategy hwin initialMemory)

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

/-- Agreement of two augmented selections at one root key. -/
def AgreeAt
    (other :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
        (Memory := Memory) A strategy hwin initialMemory)
    (key : RootKey A strategy) : Prop :=
  selection key = other key

/-- Enter the augmented policy selected at one root. -/
noncomputable def root (key : RootKey A strategy) :
    BankControl (Memory := Memory) A strategy :=
  ⟨key, (selection key).run []⟩

/-- Advance the selected augmented policy without changing the root key. -/
noncomputable def successor
    (state : BankControl (Memory := Memory) A strategy)
    (childCode : LinkedCode A) :
    BankControl (Memory := Memory) A strategy :=
  ⟨state.1, (selection state.1).successor state.2 childCode⟩

@[simp] theorem root_index (key : RootKey A strategy) :
    (selection.root A strategy hwin initialMemory key).1 = key :=
  rfl

@[simp] theorem successor_index
    (state : BankControl (Memory := Memory) A strategy)
    (childCode : LinkedCode A) :
    (selection.successor A strategy hwin initialMemory state childCode).1 =
      state.1 :=
  rfl

/-- The augmented root exposes exactly the old public root data. -/
theorem root_data (key : RootKey A strategy) :
    (selection.root A strategy hwin initialMemory key).2.1.1 = key.1 := by
  exact congrArg (fun state ↦ state.1.1) (selection key).accepts.1.1

/-- Reachability relative to the selected augmented policy. -/
abbrev Reachable
    (state : BankControl (Memory := Memory) A strategy) : Prop :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryReachable
    (Memory := Memory) A strategy hwin (initialMemory state.1)
      state.1.1.1 state.1.1.2 (selection state.1) state.2

theorem root_reachable (key : RootKey A strategy) :
    selection.Reachable A strategy hwin initialMemory
      (selection.root A strategy hwin initialMemory key) :=
  ⟨[], rfl⟩

theorem successor_reachable
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable : selection.Reachable A strategy hwin initialMemory state)
    (childCode : LinkedCode A) :
    selection.Reachable A strategy hwin initialMemory
      (selection.successor A strategy hwin initialMemory state childCode) :=
  SourceFreeBeliefCodeParityFiniteMemoryPolicy.successor_reachable
    (PolicyDPA A state.1.1.1)
    state.1.1
    (initialMemory state.1)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A)))
    (selection state.1) state.2 hreachable childCode

/-- Reachability of an augmented bank state depends only on the finite-memory
policy selected at its stored root key. -/
theorem reachable_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
        (Memory := Memory) A strategy hwin initialMemory)
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.1 = key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.Reachable A strategy hwin initialMemory state ↔
      other.Reachable A strategy hwin initialMemory state := by
  subst key
  unfold AgreeAt at hagrees
  change
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryReachable
        (Memory := Memory) A strategy hwin (initialMemory state.1)
          state.1.1.1 state.1.1.2 (selection state.1) state.2 ↔
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryReachable
        (Memory := Memory) A strategy hwin (initialMemory state.1)
          state.1.1.1 state.1.1.2 (other state.1) state.2
  rw [hagrees]

/-- Literal realization of a bare target by one child of the selected
augmented policy. -/
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
          ((selection state.1).successor state.2 childCode).1 =
            (childCode,
              (PolicyDPA A state.1.1.1).step state.2.1.2 childCode)

/-- Realization depends only on the policy selected at the stored key. -/
theorem childRealizes_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
        (Memory := Memory) A strategy hwin initialMemory)
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.1 = key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ChildRealizes A strategy hwin initialMemory state target
        childCode ↔
      other.ChildRealizes A strategy hwin initialMemory state target
        childCode := by
  subst key
  unfold AgreeAt at hagrees
  unfold ChildRealizes
  rw [hagrees]

/-- A realizing augmented child is still the literal semantic child carrying
the table installed by the same step. -/
theorem ChildRealizes.exists_child
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes : selection.ChildRealizes A strategy hwin initialMemory state
      target childCode) :
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        (source.step A actual).code A = target ∧
          childCode.2 =
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
              source state.2.1.1.2 actual ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            (source.step A actual) childCode.2 := by
  rcases hrealizes with
    ⟨move, source, actual, hcode, hmove, _hcompatible, hchildren,
      hchildCode, hbare, _hsuccessor⟩
  have hstepCode : (source.step A actual).code A = childCode.1 := by
    rw [ProfiledRawJointOneSidedSemanticState.step_code]
    rw [hcode, hmove, hchildCode]
    rfl
  have hannotation :
      childCode.2 =
        profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
          source state.2.1.1.2 actual := by
    rw [hchildCode]
    exact (hchildren actual).symm
  refine ⟨source, actual, hstepCode.trans hbare, hannotation, ?_⟩
  rw [hannotation]
  exact
    profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
      hwin source state.2.1.1.2 actual

/-- Total finite resolver for augmented policies. -/
noncomputable def resolveTarget
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : LinkedCode A := by
  classical
  exact if h : ∃ childCode,
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode then
    Classical.choose h
  else
    state.2.1.1

theorem resolveTarget_realizes
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hexists : ∃ childCode,
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode) :
    selection.ChildRealizes A strategy hwin initialMemory state target
      (selection.resolveTarget A strategy hwin initialMemory state target) := by
  classical
  simp only [resolveTarget]
  split
  next h => exact Classical.choose_spec h
  next h => exact (h hexists).elim

theorem resolveTarget_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
        (Memory := Memory) A strategy hwin initialMemory)
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.1 = key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.resolveTarget A strategy hwin initialMemory state target =
      other.resolveTarget A strategy hwin initialMemory state target := by
  subst key
  unfold AgreeAt at hagrees
  unfold resolveTarget ChildRealizes
  rw [hagrees]

/-- The augmented successor, including its memory update, is extensional in
the policy selected at the state's fixed root key. -/
theorem successor_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
        (Memory := Memory) A strategy hwin initialMemory)
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.1 = key)
    (childCode : LinkedCode A)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.successor A strategy hwin initialMemory state childCode =
      other.successor A strategy hwin initialMemory state childCode := by
  subst key
  unfold AgreeAt at hagrees
  unfold successor
  rw [hagrees]

/-- The deterministic augmented resolver retains the key and reachability. -/
theorem resolveTarget_spec
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable : selection.Reachable A strategy hwin initialMemory state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hexists : ∃ childCode,
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode) :
    let childCode :=
      selection.resolveTarget A strategy hwin initialMemory state target
    childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode ∧
      (selection.successor A strategy hwin initialMemory state childCode).1 =
        state.1 ∧
      selection.Reachable A strategy hwin initialMemory
        (selection.successor A strategy hwin initialMemory state childCode) := by
  dsimp only
  have hrealizes := selection.resolveTarget_realizes A strategy hwin
    initialMemory state target hexists
  have hrealizes' := hrealizes
  rcases hrealizes' with
    ⟨_move, _source, _actual, _hcode, _hmove, _hcompatible,
      _hchildren, _hchildCode, htarget, _hsuccessor⟩
  refine ⟨htarget, hrealizes, rfl, ?_⟩
  exact selection.successor_reachable A strategy hwin initialMemory state
    hreachable _

/-! ## Installed-table target closure -/

/-- Every target allowed by the installed right table is realized inside the
same selected finite-memory policy and under the same public root key. -/
theorem exists_rightTargetSuccessor
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable : selection.Reachable A strategy hwin initialMemory state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.2.1.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        selection.ChildRealizes A strategy hwin initialMemory state target
          childCode ∧
        (selection.successor A strategy hwin initialMemory state childCode).1 =
          state.1 ∧
        selection.Reachable A strategy hwin initialMemory
          (selection.successor A strategy hwin initialMemory state
            childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryRightTargetSuccessor
        (Memory := Memory) A strategy hwin (initialMemory state.1)
          state.1.1.1 state.1.1.2 (selection state.1) state.2 hreachable
          currentCode hcurrentCode root hroot phaseMove hphaseMove target
          htarget with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, _hside,
      _hactualTarget, _hchildAnnotation, hchildBare, hsuccessor⟩
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1.1 move actual
  have hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode := by
    exact ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, rfl,
      hchildBare, hsuccessor⟩
  refine ⟨childCode, hchildBare, hrealizes, rfl, ?_⟩
  exact selection.successor_reachable A strategy hwin initialMemory state
    hreachable childCode

/-- Deterministic right-target closure for the augmented bank. -/
theorem resolveRightTarget_spec
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable : selection.Reachable A strategy hwin initialMemory state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.2.1.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    let childCode :=
      selection.resolveTarget A strategy hwin initialMemory state target
    childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode ∧
      (selection.successor A strategy hwin initialMemory state childCode).1 =
        state.1 ∧
      selection.Reachable A strategy hwin initialMemory
        (selection.successor A strategy hwin initialMemory state
          childCode) := by
  obtain ⟨childCode, _hbare, hrealizes, _hindex, _hnext⟩ :=
    selection.exists_rightTargetSuccessor A strategy hwin initialMemory state
      hreachable currentCode hcurrentCode root hroot phaseMove hphaseMove
      target htarget
  exact selection.resolveTarget_spec A strategy hwin initialMemory state
    hreachable target ⟨childCode, hrealizes⟩

/-- Left-orientation mirror of installed-table target closure. -/
theorem exists_leftTargetSuccessor
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable : selection.Reachable A strategy hwin initialMemory state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.2.1.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        selection.ChildRealizes A strategy hwin initialMemory state target
          childCode ∧
        (selection.successor A strategy hwin initialMemory state childCode).1 =
          state.1 ∧
        selection.Reachable A strategy hwin initialMemory
          (selection.successor A strategy hwin initialMemory state
            childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryLeftTargetSuccessor
        (Memory := Memory) A strategy hwin (initialMemory state.1)
          state.1.1.1 state.1.1.2 (selection state.1) state.2 hreachable
          currentCode hcurrentCode root hroot phaseMove hphaseMove target
          htarget with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, _hside,
      _hactualTarget, _hchildAnnotation, hchildBare, hsuccessor⟩
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1.1 move actual
  have hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode := by
    exact ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, rfl,
      hchildBare, hsuccessor⟩
  refine ⟨childCode, hchildBare, hrealizes, rfl, ?_⟩
  exact selection.successor_reachable A strategy hwin initialMemory state
    hreachable childCode

/-- Deterministic left-target closure for the augmented bank. -/
theorem resolveLeftTarget_spec
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable : selection.Reachable A strategy hwin initialMemory state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.2.1.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    let childCode :=
      selection.resolveTarget A strategy hwin initialMemory state target
    childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin initialMemory state target
        childCode ∧
      (selection.successor A strategy hwin initialMemory state childCode).1 =
        state.1 ∧
      selection.Reachable A strategy hwin initialMemory
        (selection.successor A strategy hwin initialMemory state
          childCode) := by
  obtain ⟨childCode, _hbare, hrealizes, _hindex, _hnext⟩ :=
    selection.exists_leftTargetSuccessor A strategy hwin initialMemory state
      hreachable currentCode hcurrentCode root hroot phaseMove hphaseMove
      target htarget
  exact selection.resolveTarget_spec A strategy hwin initialMemory state
    hreachable target ⟨childCode, hrealizes⟩

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

/-- An old policy selection embeds pointwise into the augmented bank with
unit memory. -/
noncomputable def
    ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection.withUnitMemory
    (selection :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
      (Memory := Unit) A strategy hwin (fun _ ↦ ()) :=
  fun key ↦
    (selection key).withUnitMemory A strategy hwin key.1.1 key.1.2

end

end DetParityAutomaton

end DistributedSynthesis
