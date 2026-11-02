/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicy
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityFiniteMemoryPolicy

/-!
# Finite-memory recurrent physical-compatible policies

This is the model-specific specialization of the explicit finite-memory
policy interface.  Its public state is unchanged: the current incidence code,
installed physical annotation, and forward code-parity state.  A separate
finite coordinate may carry the belief state required by the output-aware
owner-fibre regularization.

Reachable-state inversion still exposes one exact semantic source, one linked
move, the installed-table compatibility proof, and the literal public child
state for every actual raw direction.  Only the added memory component of a
child remains under control of the augmented transition table.
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

private abbrev OneSidedState :=
  ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

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

/-- A recurrent physical-compatible policy with one explicit finite memory
coordinate. -/
noncomputable abbrev
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
    (initialMemory : Memory)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A) :=
  SourceFreeBeliefCodeParityFiniteMemoryPolicy
    (PolicyDPA A initialCode)
    (initialCode, initialAnnotation)
    initialMemory
    (PolicyValid A strategy hwin)
    (PolicyNext A (In₁ := In₁) (In₂ := In₂))

/-- Complete augmented state of a recurrent physical-compatible policy. -/
noncomputable abbrev
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  SourceFreeBeliefCodeParityFiniteMemoryState
    (PolicyDPA A initialCode) Memory

noncomputable instance
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyStateFintype
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
        (Memory := Memory) A initialCode) := by
  infer_instance

/-- Reachability in one selected augmented recurrent policy. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryReachable
    (initialMemory : Memory)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
        (Memory := Memory) A initialCode) : Prop :=
  SourceFreeBeliefCodeParityFiniteMemoryPolicy.Reachable
    (PolicyDPA A initialCode)
    (initialCode, initialAnnotation)
    initialMemory
    (PolicyValid A strategy hwin)
    (PolicyNext A (In₁ := In₁) (In₂ := In₂))
    policy state

/-- Every old recurrent policy is the unit-memory specialization of the
augmented interface. -/
noncomputable def
    ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy.withUnitMemory
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy : ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A
      strategy hwin initialCode initialAnnotation) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
      (Memory := Unit) A strategy hwin () initialCode initialAnnotation :=
  SourceFreeBeliefCodeParityRationalPolicy.withUnitMemory
    (PolicyDPA A initialCode)
    (initialCode, initialAnnotation)
    (PolicyValid A strategy hwin)
    (PolicyNext A (In₁ := In₁) (In₂ := In₂))
    policy

/-- Reachable augmented states retain the exact semantic-source inversion of
the old policy.  The public component of every actual child is fixed; only its
additional finite-memory coordinate is new. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemorySemanticSource
    (initialMemory : Memory)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
        (Memory := Memory) A initialCode)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryReachable
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation policy state) :
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ∃ source : OneSidedState A strategy,
        source.code A = state.1.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source state.1.1.2 ∧
          (∀ actual,
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
                source state.1.1.2 actual =
              move.2 actual) ∧
          ∀ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointOneSidedNext A) state.1.1 move actual
            (policy.successor state childCode).1 =
              (childCode, (PolicyDPA A initialCode).step state.1.2 childCode) := by
  obtain ⟨move, hmove⟩ :=
    SourceFreeBeliefCodeParityFiniteMemoryPolicy.exists_move
      (PolicyDPA A initialCode)
      (initialCode, initialAnnotation)
      initialMemory
      (PolicyValid A strategy hwin)
      (PolicyNext A (In₁ := In₁) (In₂ := In₂))
      policy state hreachable
  rcases hmove.1.2 with
    ⟨source, hcode, hsourceMove, hcompatible, hchildren⟩
  refine ⟨move, source, hcode, hsourceMove, hcompatible, hchildren, ?_⟩
  intro actual
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hsuccessor := hmove.2 childCode
  have hchild :
      PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1 move childCode =
        childCode := by
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))
      state.1.1 move actual
  rw [hchild] at hsuccessor
  simpa only [sourceFreeBeliefCodeParityControllerNext] using hsuccessor

/-! ## Installed-table target closure with finite memory -/

/-- Every target allowed by the installed right table is a literal public
successor of the same finite-memory policy.  The theorem deliberately leaves
the successor's memory coordinate unconstrained. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryRightTargetSuccessor
    (initialMemory : Memory)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
        (Memory := Memory) A initialCode)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryReachable
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ∃ source : OneSidedState A strategy,
        ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
          source.code A = state.1.1.1 ∧
            source.move A = move.1 ∧
            ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
              source state.1.1.2 ∧
            (∀ direction,
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                  hwin source state.1.1.2 direction =
                move.2 direction) ∧
            actual.side = .right ∧
            (source.step A actual).code A = target ∧
            move.2 actual =
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                hwin source state.1.1.2 actual ∧
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointOneSidedNext A) state.1.1 move actual
            childCode.1 = target ∧
              (policy.successor state childCode).1 =
                (childCode, (PolicyDPA A initialCode).step state.1.2
                  childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemorySemanticSource
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation policy state hreachable with
    ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩
  have hsourceCode : source.code A = currentCode :=
    hcode.trans hcurrentCode
  have hsourceRoot :
      profiledRawJointOneSidedCurrentSlots A .right (source.code A) () =
        some root := by
    rw [hsourceCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    source.exists_right_member_of_currentSlot A () root hsourceRoot
  obtain ⟨actual, hactualSide, hactualTarget⟩ :=
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_rightTargetChild
      A strategy source state.1.1.2 hcompatible semanticMember hmember
        phaseMove hphaseMove target htarget
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1.1 move.1 actual = target
    rw [← hcode, ← hmove, ← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
    hactualSide, hactualTarget, (hchildren actual).symm, hchildBare, ?_⟩
  exact hsuccessor actual

/-- Left-orientation mirror of finite-memory installed-table closure. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryLeftTargetSuccessor
    (initialMemory : Memory)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
        (Memory := Memory) A initialCode)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryReachable
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ∃ source : OneSidedState A strategy,
        ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
          source.code A = state.1.1.1 ∧
            source.move A = move.1 ∧
            ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
              source state.1.1.2 ∧
            (∀ direction,
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                  hwin source state.1.1.2 direction =
                move.2 direction) ∧
            actual.side = .left ∧
            (source.step A actual).code A = target ∧
            move.2 actual =
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                hwin source state.1.1.2 actual ∧
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointOneSidedNext A) state.1.1 move actual
            childCode.1 = target ∧
              (policy.successor state childCode).1 =
                (childCode, (PolicyDPA A initialCode).step state.1.2
                  childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleFiniteMemorySemanticSource
        (Memory := Memory) A strategy hwin initialMemory initialCode
          initialAnnotation policy state hreachable with
    ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩
  have hsourceCode : source.code A = currentCode :=
    hcode.trans hcurrentCode
  have hsourceRoot :
      profiledRawJointOneSidedCurrentSlots A .left (source.code A) () =
        some root := by
    rw [hsourceCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    source.exists_left_member_of_currentSlot A () root hsourceRoot
  obtain ⟨actual, hactualSide, hactualTarget⟩ :=
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_leftTargetChild
      A strategy source state.1.1.2 hcompatible semanticMember hmember
        phaseMove hphaseMove target htarget
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1.1 move.1 actual = target
    rw [← hcode, ← hmove, ← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
    hactualSide, hactualTarget, (hchildren actual).symm, hchildBare, ?_⟩
  exact hsuccessor actual

end

end DetParityAutomaton

end DistributedSynthesis
