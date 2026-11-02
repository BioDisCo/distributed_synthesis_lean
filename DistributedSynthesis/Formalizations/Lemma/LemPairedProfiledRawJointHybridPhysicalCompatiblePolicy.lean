/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCurrentCompatibility
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedSemanticMemberExtraction

/-!
# One carried physical policy with current-source compatibility

The ordinary parent-linked rationalization remembers where a child's finite
annotation came from, but its local legality predicate does not say that the
annotation is compatible with the semantic representative selected at that
child.  For the replace-not-accumulate physical update this information
cannot be recovered afterwards.

This file retains the already proved semantic invariant *inside* the finite
legality relation before rationalization.  Consequently one reachable-policy
inversion supplies, simultaneously:

* the literal current semantic source;
* the policy's actual raw move;
* the policy state's literally installed current physical tables;
* compatibility of those same tables with that same source; and
* the complete child-table map selected by the policy move.

This is the anti-mosaic interface needed to consume an actual phase-live
table target.  No fresh semantic inversion or independently selected table
is used at the physical cut.
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

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

/-! ## The exact semantic invariant -/

/-- Every node of the literal carried tree has a current annotation compatible
with its literal semantic source.  The root is common, and every non-root
annotation was installed by the exact incoming semantic edge. -/
theorem profiledRawJointHybridPhysicalCarriedTree_currentCompatible
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (node : TreeNode (HybridDirection (In₁ := In₁) (In₂ := In₂))) :
    let carried :=
      (profiledRawJointHybridSemanticTree A initial).carryFiniteAnnotation
        (profiledRawJointHybridInitialPhysicalAnnotation A)
        (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
    ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      (carried.stateAt node).1 (carried.stateAt node).2 := by
  let raw := profiledRawJointHybridSemanticTree A initial
  exact raw.carryFiniteAnnotation_invariant
    (profiledRawJointHybridInitialPhysicalAnnotation A)
    (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
    (ProfiledRawJointHybridPhysicalCurrentCompatible A strategy)
    (by trivial)
    (fun source current direction _ ↦
      profiledRawJointHybridPhysicalAnnotationAdvance_compatible A strategy
        hwin source current direction)
    node

/-! ## Compatibility retained by parent-linked legality -/

/-- One representative explains the current code, the actual policy move,
the literally installed current tables, and the entire child-table map. -/
def ProfiledRawJointHybridPhysicalCompatibleParentLinkValid
    (code : ProfiledRawJointHybridCode A)
    (current : PhysicalAnnotation A)
    (move : ProfiledRawJointHybridMove A)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) : Prop :=
  ∃ source : HybridState A strategy,
    source.code A = code ∧
      source.move A = move ∧
      ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
        current ∧
      ∀ direction,
        profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
            source current direction =
          children direction

/-- The exact carried semantic node satisfies the strengthened parent link. -/
theorem
    profiledRawJointHybridPhysicalCompatibleParentLinkValid_of_semantic
    (source : HybridState A strategy)
    (current : PhysicalAnnotation A)
    (hcompatible : ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      source current) :
    ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy hwin
      (source.code A) current (source.move A)
      (fun direction ↦
        profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
          current direction) := by
  exact ⟨source, rfl, rfl, hcompatible, fun _ ↦ rfl⟩

/-! ## The strengthened finite policy -/

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridInitialPhysicalAnnotation A)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatiblePolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridInitialPhysicalAnnotation A)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A)))).State

abbrev ProfiledRawJointHybridPhysicalCompatibleReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A
      strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridInitialPhysicalAnnotation A)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
    policy state

/-- A winning strategy yields one finite rational policy in which current
table/source compatibility survives rationalization. -/
theorem nonempty_profiledRawJointHybridPhysicalCompatibleRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
        initial) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let initialAnnotation := profiledRawJointHybridInitialPhysicalAnnotation A
  let advance :=
    profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
  let carried := raw.carryFiniteAnnotation initialAnnotation advance
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let certificate :=
    profiledRawJointHybridSemanticTree_codeParityCertificate A strategy hwin
      initial
  let carriedCertificate :=
    certificate.carryFiniteAnnotation
      (profiledRawJointHybridCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridNext A)
      raw initialAnnotation advance
  exact carriedCertificate.nonempty_parentLinkedFiniteCodeDirectionRationalPolicy
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    carried Prod.snd
    (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy hwin)
    (fun node ↦ by
      let state := carried.stateAt node
      exact
        profiledRawJointHybridPhysicalCompatibleParentLinkValid_of_semantic A
          strategy hwin state.1 state.2
            (profiledRawJointHybridPhysicalCarriedTree_currentCompatible A
              strategy hwin initial node))

/-! ## Reachable inversion: current table and current source stay together -/

/-- At a reachable state, one semantic representative explains the public
code, the policy's raw move, the *current annotation already stored in that
state*, and the complete child-annotation table.  In particular the
compatibility fact is about `state.1.2` itself. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A
      strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := PhysicalAnnotation A),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2 ∧
          (∀ direction,
            profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
                source state.1.2 direction =
              move.2 direction) ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            policy.successor state
                (sourceFreeBeliefParentLinkedNext
                  (profiledRawJointHybridNext A) state.1 move direction) =
              let childCode := sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) state.1 move direction
              (childCode,
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation := PhysicalAnnotation A)
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode) := by
  rcases
      SourceFreeBeliefCodeParityRationalPolicy.exists_parentLinkedMove_finiteCodeDirection
        (profiledRawJointHybridCodeParityDPA A
          (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
            A)))
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridInitialPhysicalAnnotation A)
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
          hwin)
        (profiledRawJointHybridNext A)
        policy state hreachable with
    ⟨move, _hvalid, hlink, hsuccessor⟩
  rcases hlink with
    ⟨source, hcode, hmove, hcompatible, hchildren⟩
  exact ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩

/-! ## The actual installed table target is one policy child -/

/-- Right orientation of the decisive anti-mosaic seam.

`phaseMove` is not selected in this theorem: `hphaseMove` says literally that
it is the right table component of the current carried policy state.  Hence
an allowed target of the actual phase-live table is the bare code of a strict
right child selected through the raw move returned by the same reachable
policy inversion. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRightTargetSuccessor
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A
      strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1 = .oneSided currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointHybridCurrentSlots A .right state.1.1 () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := PhysicalAnnotation A),
      ∃ source : HybridState A strategy,
        ∃ actual : ProfiledRawJointActualDirection
            (I := Unit) (In₁ := In₁) (In₂ := In₂),
          source.code A = state.1.1 ∧
            source.move A = move.1 ∧
            actual.side = .right ∧
            (source.step A (.strict actual)).code A = .oneSided target ∧
            move.2 (.strict actual) =
              profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
                source state.1.2 (.strict actual) ∧
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointHybridNext A) state.1 move (.strict actual)
            childCode.1 = .oneSided target ∧
              policy.successor state childCode =
                (childCode,
                  (sourceFreeBeliefParentLinkedCodeParityDPA
                    (Annotation := PhysicalAnnotation A)
                    (profiledRawJointHybridCodeParityDPA A
                      (.common ((profiledRawJointCommonWorldFamily A initial
                        ).incidenceCode A)))).step state.2 childCode) := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleSemanticSource A strategy
        hwin initial policy state hreachable with
    ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩
  have hrootCurrent :
      profiledRawJointOneSidedCurrentSlots A .right currentCode () =
        some root := by
    rw [hcurrentCode] at hroot
    exact hroot
  have hsourceCode : source.code A = .oneSided currentCode :=
    hcode.trans hcurrentCode
  cases source with
  | common world => simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead => simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | oneSided semantic =>
      have hsemanticCode : semantic.code A = currentCode := by
        simpa [ProfiledRawJointHybridSemanticState.code] using hsourceCode
      have hsemanticRoot :
          profiledRawJointOneSidedCurrentSlots A .right (semantic.code A) () =
            some root := by
        rw [hsemanticCode]
        exact hrootCurrent
      obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
        semantic.exists_right_member_of_currentSlot A () root hsemanticRoot
      have honeCompatible :
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            semantic state.1.2 := by
        simpa [ProfiledRawJointHybridPhysicalCurrentCompatible] using
          hcompatible
      obtain ⟨actual, hactualSide, hactualTarget⟩ :=
        ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_rightTargetChild
          A strategy semantic state.1.2 honeCompatible semanticMember hmember
            phaseMove hphaseMove target htarget
      have hsemanticChild :
          ((ProfiledRawJointHybridSemanticState.oneSided semantic).step A
              (.strict actual)).code A = .oneSided target := by
        simpa [ProfiledRawJointHybridSemanticState.step,
          ProfiledRawJointHybridSemanticState.code] using
            congrArg ProfiledRawJointHybridCode.oneSided hactualTarget
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      have hchildBare : childCode.1 = .oneSided target := by
        change profiledRawJointHybridNext A state.1.1 move.1
            (.strict actual) = .oneSided target
        rw [← hcode, ← hmove,
          ← ProfiledRawJointHybridSemanticState.step_code]
        exact hsemanticChild
      refine ⟨move, .oneSided semantic, actual, hcode, hmove, hactualSide,
        hsemanticChild, (hchildren (.strict actual)).symm, hchildBare, ?_⟩
      exact hsuccessor (.strict actual)

/-- Left-orientation mirror.  The `phaseMove` consumed here is literally the
left table stored in `state.1.2`; every allowed target is a strict-left child
of the same selected policy move. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLeftTargetSuccessor
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A
      strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1 = .oneSided currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointHybridCurrentSlots A .left state.1.1 () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := PhysicalAnnotation A),
      ∃ source : HybridState A strategy,
        ∃ actual : ProfiledRawJointActualDirection
            (I := Unit) (In₁ := In₁) (In₂ := In₂),
          source.code A = state.1.1 ∧
            source.move A = move.1 ∧
            actual.side = .left ∧
            (source.step A (.strict actual)).code A = .oneSided target ∧
            move.2 (.strict actual) =
              profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
                source state.1.2 (.strict actual) ∧
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointHybridNext A) state.1 move (.strict actual)
            childCode.1 = .oneSided target ∧
              policy.successor state childCode =
                (childCode,
                  (sourceFreeBeliefParentLinkedCodeParityDPA
                    (Annotation := PhysicalAnnotation A)
                    (profiledRawJointHybridCodeParityDPA A
                      (.common ((profiledRawJointCommonWorldFamily A initial
                        ).incidenceCode A)))).step state.2 childCode) := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleSemanticSource A strategy
        hwin initial policy state hreachable with
    ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩
  have hrootCurrent :
      profiledRawJointOneSidedCurrentSlots A .left currentCode () =
        some root := by
    rw [hcurrentCode] at hroot
    exact hroot
  have hsourceCode : source.code A = .oneSided currentCode :=
    hcode.trans hcurrentCode
  cases source with
  | common world => simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead => simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | oneSided semantic =>
      have hsemanticCode : semantic.code A = currentCode := by
        simpa [ProfiledRawJointHybridSemanticState.code] using hsourceCode
      have hsemanticRoot :
          profiledRawJointOneSidedCurrentSlots A .left (semantic.code A) () =
            some root := by
        rw [hsemanticCode]
        exact hrootCurrent
      obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
        semantic.exists_left_member_of_currentSlot A () root hsemanticRoot
      have honeCompatible :
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            semantic state.1.2 := by
        simpa [ProfiledRawJointHybridPhysicalCurrentCompatible] using
          hcompatible
      obtain ⟨actual, hactualSide, hactualTarget⟩ :=
        ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_leftTargetChild
          A strategy semantic state.1.2 honeCompatible semanticMember hmember
            phaseMove hphaseMove target htarget
      have hsemanticChild :
          ((ProfiledRawJointHybridSemanticState.oneSided semantic).step A
              (.strict actual)).code A = .oneSided target := by
        simpa [ProfiledRawJointHybridSemanticState.step,
          ProfiledRawJointHybridSemanticState.code] using
            congrArg ProfiledRawJointHybridCode.oneSided hactualTarget
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      have hchildBare : childCode.1 = .oneSided target := by
        change profiledRawJointHybridNext A state.1.1 move.1
            (.strict actual) = .oneSided target
        rw [← hcode, ← hmove,
          ← ProfiledRawJointHybridSemanticState.step_code]
        exact hsemanticChild
      refine ⟨move, .oneSided semantic, actual, hcode, hmove, hactualSide,
        hsemanticChild, (hchildren (.strict actual)).symm, hchildBare, ?_⟩
      exact hsuccessor (.strict actual)

end

end DetParityAutomaton

end DistributedSynthesis
