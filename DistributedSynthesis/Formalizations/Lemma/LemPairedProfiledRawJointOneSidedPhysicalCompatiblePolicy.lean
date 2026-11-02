/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedProvenancePolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCurrentCompatibility
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedSemanticMemberExtraction

/-!
# Recurrent one-sided policies with an installed physical table

A post-resolution handoff supplies more than a public incidence code: it
supplies the finite physical table selected at the same literal incoming
edge.  Starting an ordinary code-indexed policy at that point is unsound,
because its independently selected root move need not be compatible with the
installed table.

This file carries the current physical annotation through the exact
one-sided semantic tree before the single parity rationalization.  The root
annotation is arbitrary, subject to compatibility with the exact root
source.  At every reachable rational-policy state, one semantic source
simultaneously explains the public code, the policy move, the installed
current table, and the complete table of successor annotations.  Hence a
target emitted by an installed table advances to a state of the same
accepting policy; no representative or policy is selected at that target.

All runtime data below are finite.  Semantic sources and compatibility
proofs occur only in the construction and inversion theorems.
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

/-! ## Replace-only annotation and its invariant -/

/-- Install the two finite sibling tables selected by the exact one-sided
source and actual raw direction.  The preceding annotation is intentionally
discarded. -/
noncomputable def profiledRawJointOneSidedPhysicalAnnotationAdvance
    (source : OneSidedState A strategy)
    (_current : PhysicalAnnotation A)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂)) :
    PhysicalAnnotation A :=
  profiledRawJointHybridPhysicalAnnotationOf A strategy hwin source.family
    actual.direction

/-- A literal one-sided step installs an annotation compatible with its
literal child. -/
theorem profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible
    (source : OneSidedState A strategy)
    (current : PhysicalAnnotation A)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      (source.step A actual)
      (profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
        source current actual) := by
  cases hside : actual.side with
  | right =>
      simpa [ProfiledRawJointOneSidedSemanticState.step, hside,
        profiledRawJointOneSidedPhysicalAnnotationAdvance] using
        (profiledRawJointHybridPhysicalAnnotationOf_rightActual_compatible A
          strategy hwin source.family actual.direction)
  | left =>
      simpa [ProfiledRawJointOneSidedSemanticState.step, hside,
        profiledRawJointOneSidedPhysicalAnnotationAdvance] using
        (profiledRawJointHybridPhysicalAnnotationOf_leftActual_compatible A
          strategy hwin source.family actual.direction)

/-- The carried exact semantic tree preserves current-table compatibility
from any compatible root annotation. -/
theorem profiledRawJointOneSidedPhysicalCarriedTree_currentCompatible
    (initial : OneSidedState A strategy)
    (initialAnnotation : PhysicalAnnotation A)
    (hinitial : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy initial initialAnnotation)
    (node : TreeNode
      (ActualDirection (In₁ := In₁) (In₂ := In₂))) :
    let carried :=
      (profiledRawJointOneSidedSemanticTree A initial).carryFiniteAnnotation
        initialAnnotation
        (profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin)
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      (carried.stateAt node).1 (carried.stateAt node).2 := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  exact raw.carryFiniteAnnotation_invariant initialAnnotation
    (profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin)
    (ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy)
    hinitial
    (fun source current actual _ ↦
      profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
        hwin source current actual)
    node

/-! ## Source-linked finite legality -/

/-- One semantic source explains the current code, the policy move, the
already installed physical table, and the complete successor-annotation
assignment. -/
def ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (current : PhysicalAnnotation A)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (children : ActualDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) : Prop :=
  ∃ source : OneSidedState A strategy,
    source.code A = code ∧
      source.move A = move ∧
      ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy source
        current ∧
      ∀ actual,
        profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
            source current actual =
          children actual

/-- Every compatible literal source supplies a valid parent-linked move. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_of_semantic
    (source : OneSidedState A strategy)
    (current : PhysicalAnnotation A)
    (hcompatible : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy source current) :
    ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy hwin
      (source.code A) current (source.move A)
      (fun actual ↦
        profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
          source current actual) := by
  exact ⟨source, rfl, rfl, hcompatible, fun _ ↦ rfl⟩

/-! ## One recurrent rational policy -/

/-- A one-sided policy whose public code includes the current physical
annotation. -/
noncomputable abbrev
    ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A initialCode))
    (initialCode, initialAnnotation)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A)))

/-- Complete finite state of the recurrent physical-compatible policy. -/
noncomputable abbrev
    ProfiledRawJointOneSidedPhysicalCompatiblePolicyState
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A initialCode))
    (initialCode, initialAnnotation)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext
        (profiledRawJointOneSidedNext A)))).State

noncomputable instance
    profiledRawJointOneSidedPhysicalCompatiblePolicyStateFintype
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A) :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy hwin
        initialCode initialAnnotation) := by
  infer_instance

/-- Reachability inside the one selected recurrent policy. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatibleReachable
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy : ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A
      strategy hwin initialCode initialAnnotation)
    (state : ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy
      hwin initialCode initialAnnotation) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A initialCode))
    (initialCode, initialAnnotation)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A)))
    policy state

/-- The exact carried one-sided tree yields a finite recurrent policy rooted
at its supplied compatible physical annotation. -/
theorem nonempty_profiledRawJointOneSidedPhysicalCompatibleRationalPolicy
    (initial : OneSidedState A strategy)
    (initialAnnotation : PhysicalAnnotation A)
    (hinitial : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy initial initialAnnotation) :
    Nonempty
      (ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A strategy
        hwin (initial.code A) initialAnnotation) := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  let advance :=
    profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
  let carried := raw.carryFiniteAnnotation initialAnnotation advance
  let certificate :=
    profiledRawJointOneSidedSemanticTree_provenanceCodeParityCertificate A
      strategy hwin initial
  let carriedCertificate :=
    certificate.carryFiniteAnnotation
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedNext A) raw initialAnnotation advance
  exact carriedCertificate.nonempty_parentLinkedFiniteCodeDirectionRationalPolicy
    (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
    (initial.code A)
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedNext A)
    carried Prod.snd
    (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy hwin)
    (fun node ↦ by
      let state := carried.stateAt node
      exact
        profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_of_semantic
          A strategy hwin state.1 state.2
          (profiledRawJointOneSidedPhysicalCarriedTree_currentCompatible A
            strategy hwin initial initialAnnotation hinitial node))

/-! ## Reachable-state inversion and successor closure -/

/-- A reachable policy state exposes one source witnessing the current table
and one linked move whose complete child map is the policy transition. -/
theorem exists_profiledRawJointOneSidedPhysicalCompatibleSemanticSource
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy : ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A
      strategy hwin initialCode initialAnnotation)
    (state : ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy
      hwin initialCode initialAnnotation)
    (hreachable : ProfiledRawJointOneSidedPhysicalCompatibleReachable A
      strategy hwin initialCode initialAnnotation policy state) :
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ∃ source : OneSidedState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source state.1.2 ∧
          (∀ actual,
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
                source state.1.2 actual =
              move.2 actual) ∧
          ∀ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
            policy.successor state
                (sourceFreeBeliefParentLinkedNext
                  (profiledRawJointOneSidedNext A) state.1 move actual) =
              let childCode := sourceFreeBeliefParentLinkedNext
                (profiledRawJointOneSidedNext A) state.1 move actual
              (childCode,
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation := PhysicalAnnotation A)
                  (profiledRawJointOneSidedCodeParityDPA A initialCode)).step
                    state.2 childCode) := by
  rcases
      SourceFreeBeliefCodeParityRationalPolicy.exists_parentLinkedMove_finiteCodeDirection
        (profiledRawJointOneSidedCodeParityDPA A initialCode)
        initialCode initialAnnotation
        (ProfiledRawJointOneSidedProvenanceValid A strategy)
        (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
          hwin)
        (profiledRawJointOneSidedNext A) policy state hreachable with
    ⟨move, _hvalid, hlink, hsuccessor⟩
  rcases hlink with
    ⟨source, hcode, hmove, hcompatible, hchildren⟩
  exact ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩

/-- Every actual raw child of a reachable state is a reachable state of the
same selected policy. -/
theorem
    profiledRawJointOneSidedPhysicalCompatible_successor_reachable
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy : ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A
      strategy hwin initialCode initialAnnotation)
    (state : ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy
      hwin initialCode initialAnnotation)
    (hreachable : ProfiledRawJointOneSidedPhysicalCompatibleReachable A
      strategy hwin initialCode initialAnnotation policy state)
    (childCode : LinkedCode A) :
    ProfiledRawJointOneSidedPhysicalCompatibleReachable A strategy hwin
      initialCode initialAnnotation policy
        (policy.successor state childCode) := by
  rcases hreachable with ⟨node, hnode⟩
  refine ⟨node ++ [childCode], ?_⟩
  rw [← policy.successor_at node childCode, hnode]

/-! ## Targets of the installed table remain in the same policy -/

/-- Right orientation of recurrent closure.  The current code and current
physical annotation are read from one reachable policy state.  Consequently,
every target allowed by the installed right table is the bare code of an
actual right child selected by the linked move at that state, and the child
is obtained with the successor function of the same policy. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleRightTargetSuccessor
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy : ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A
      strategy hwin initialCode initialAnnotation)
    (state : ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy
      hwin initialCode initialAnnotation)
    (hreachable : ProfiledRawJointOneSidedPhysicalCompatibleReachable A
      strategy hwin initialCode initialAnnotation policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ∃ source : OneSidedState A strategy,
        ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source state.1.2 ∧
          (∀ direction,
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
                source state.1.2 direction =
              move.2 direction) ∧
          actual.side = .right ∧
            (source.step A actual).code A = target ∧
            move.2 actual =
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                hwin source state.1.2 actual ∧
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointOneSidedNext A) state.1 move actual
            childCode.1 = target ∧
              policy.successor state childCode =
                (childCode,
                  (sourceFreeBeliefParentLinkedCodeParityDPA
                    (Annotation := PhysicalAnnotation A)
                    (profiledRawJointOneSidedCodeParityDPA A initialCode)).step
                      state.2 childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleSemanticSource A
        strategy hwin initialCode initialAnnotation policy state hreachable with
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
      A strategy source state.1.2 hcompatible semanticMember hmember phaseMove
        hphaseMove target htarget
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1 move.1 actual = target
    rw [← hcode, ← hmove, ← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
    hactualSide, hactualTarget, (hchildren actual).symm, hchildBare, ?_⟩
  exact hsuccessor actual

/-- Left-orientation mirror of recurrent closure. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleLeftTargetSuccessor
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (initialAnnotation : PhysicalAnnotation A)
    (policy : ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A
      strategy hwin initialCode initialAnnotation)
    (state : ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy
      hwin initialCode initialAnnotation)
    (hreachable : ProfiledRawJointOneSidedPhysicalCompatibleReachable A
      strategy hwin initialCode initialAnnotation policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ∃ source : OneSidedState A strategy,
        ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source state.1.2 ∧
          (∀ direction,
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
                source state.1.2 direction =
              move.2 direction) ∧
          actual.side = .left ∧
            (source.step A actual).code A = target ∧
            move.2 actual =
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                hwin source state.1.2 actual ∧
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointOneSidedNext A) state.1 move actual
            childCode.1 = target ∧
              policy.successor state childCode =
                (childCode,
                  (sourceFreeBeliefParentLinkedCodeParityDPA
                    (Annotation := PhysicalAnnotation A)
                    (profiledRawJointOneSidedCodeParityDPA A initialCode)).step
                      state.2 childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleSemanticSource A
        strategy hwin initialCode initialAnnotation policy state hreachable with
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
      A strategy source state.1.2 hcompatible semanticMember hmember phaseMove
        hphaseMove target htarget
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1 move.1 actual = target
    rw [← hcode, ← hmove, ← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
    hactualSide, hactualTarget, (hchildren actual).symm, hchildBare, ?_⟩
  exact hsuccessor actual

end

end DetParityAutomaton

end DistributedSynthesis
