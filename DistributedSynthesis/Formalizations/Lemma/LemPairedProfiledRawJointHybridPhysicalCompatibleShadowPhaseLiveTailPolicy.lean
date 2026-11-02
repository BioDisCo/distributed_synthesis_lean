/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePath

/-!
# Reachable inversion below a delayed root-pinned strict child

The delayed shadow handoff does not coerce its re-rooted accepting tail into
an ordinary common-root policy.  Nevertheless the tail uses exactly the same
parent-linked validity predicate and the same false-state successor table as
its selected root-pinned package.  Consequently every state reachable below
the tagged child still exposes one semantic source, its literal raw move, the
current physical annotation, and the complete linked-child table.

This is the policy-independent input needed by a tag-indexed recurrent
controller fibre.  The only changed datum is the initial state: it is the
actual guarded child, including the objective-DPA control already reached
there.  No root transition is erased and no policy is selected again.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := PhysicalAnnotation A)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointHybridMove A)
    (Annotation := PhysicalAnnotation A)

/-- Reachability is relative to the exact tagged child, not to the old common
root.  This distinction is what makes the tail projection sound. -/
def ProfiledRawJointHybridShadowPhaseLiveTag.TailReachable
    (tag : Tag A strategy hwin)
    (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
      tag) : Prop :=
  ∃ node,
    (tag.tailCodePolicy A strategy hwin).run node = state

/-- The exact child state is the root of its re-rooted ordinary tail. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTag.tailRoot_reachable
    (tag : Tag A strategy hwin) :
    tag.TailReachable A strategy hwin
      ((tag.tailCodePolicy A strategy hwin).run []) :=
  ⟨[], rfl⟩

/-- Reachable inversion for the re-rooted tagged tail.

The statement deliberately exposes the tail policy's own successor.  Its DPA
step is written with the original parent-linked DPA; `withInitial` changes
only the initial control and leaves every step unchanged. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.exists_tailSemanticSource
    (tag : Tag A strategy hwin)
    (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
      tag)
    (hreachable : tag.TailReachable A strategy hwin state) :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let bareDPA := profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A))
    let linkedDPA := sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A) bareDPA
    ∃ move : LinkedMove A,
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
            (tag.tailCodePolicy A strategy hwin).successor state
                (sourceFreeBeliefParentLinkedNext
                  (profiledRawJointHybridNext A) state.1 move direction) =
              let childCode := sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) state.1 move direction
              (childCode, linkedDPA.step state.2 childCode) := by
  dsimp only
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  let bareDPA := profiledRawJointHybridCodeParityDPA A
    (.common ((profiledRawJointCommonWorldFamily A installed.world
      ).incidenceCode A))
  let linkedDPA := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A) bareDPA
  let childCode := tag.childCode A strategy hwin
  let tailRoot := (package.policy.run [childCode]).2
  have hreachable' :
      SourceFreeBeliefCodeParityRationalPolicy.Reachable
        (linkedDPA.withInitial tailRoot.2)
        tailRoot.1
        (sourceFreeBeliefParentLinkedValid
          (ProfiledRawJointHybridProvenanceValid A strategy)
          (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
            hwin))
        (sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext
            (profiledRawJointHybridNext A)))
        (tag.tailCodePolicy A strategy hwin) state := by
    exact hreachable
  rcases
      SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
        (linkedDPA.withInitial tailRoot.2)
        tailRoot.1
        (sourceFreeBeliefParentLinkedValid
          (ProfiledRawJointHybridProvenanceValid A strategy)
          (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
            hwin))
        (sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext
            (profiledRawJointHybridNext A)))
        (tag.tailCodePolicy A strategy hwin) state hreachable' with
    ⟨move, hvalid, hsuccessor⟩
  let hlink := hvalid.2
  rcases hlink with
    ⟨source, hcode, hmove, hcompatible, hchildren⟩
  refine ⟨move, source, hcode, hmove, hcompatible, hchildren, ?_⟩
  intro direction
  simpa only [sourceFreeBeliefFiniteCodeNext_of_direction] using
    hsuccessor
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
        state.1 move direction)

/-! ## Literal table targets remain children of this one tail -/

/-- A checked right-table target at a reachable tagged-tail state is the
literal strict-right child of the same semantic source and the same tail
successor table. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.exists_tailRightTargetSuccessor
    (tag : Tag A strategy hwin)
    (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
      tag)
    (hreachable : tag.TailReachable A strategy hwin state)
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
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let bareDPA := profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A))
    let linkedDPA := sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A) bareDPA
    ∃ move : LinkedMove A,
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
              (tag.tailCodePolicy A strategy hwin).successor state childCode =
                (childCode, linkedDPA.step state.2 childCode) := by
  dsimp only
  have hsource :=
    tag.exists_tailSemanticSource A strategy hwin state hreachable
  dsimp only at hsource
  rcases hsource with
    ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩
  have hrootCurrent :
      profiledRawJointOneSidedCurrentSlots A .right currentCode () =
        some root := by
    rw [hcurrentCode] at hroot
    exact hroot
  have hsourceCode : source.code A = .oneSided currentCode :=
    hcode.trans hcurrentCode
  cases source with
  | common world =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
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

/-! ## A tag-relative finite target table -/

/-- One literal target of the physical sibling table stored in a tagged-tail
state.  This is the re-rooted counterpart of
`ProfiledRawJointHybridPhysicalCompatibleTableTargetAt`; it has no common-root
policy parameter. -/
inductive ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt
    (tag : Tag A strategy hwin)
    (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
      tag) : IndexedLineageSide → ProfiledRawJointThreadRoot A → Prop where
  | right
      (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
      (current_code : state.1.1 = .oneSided currentCode)
      (currentRoot : ProfiledRawJointThreadRoot A)
      (current_live :
        profiledRawJointHybridCurrentSlots A .right state.1.1 () =
          some currentRoot)
      (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
      (phaseMove_eq : state.1.2.1 = some phaseMove)
      (target : ProfiledRawJointIncidenceCode A (I := Unit))
      (target_allowed :
        profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1 target)
      (slot : ProfiledRawLeftSlot A)
      (target_live : target.family.left () = some slot) :
      ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt tag state .left
        (.inr slot)
  | left
      (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
      (current_code : state.1.1 = .oneSided currentCode)
      (currentRoot : ProfiledRawJointThreadRoot A)
      (current_live :
        profiledRawJointHybridCurrentSlots A .left state.1.1 () =
          some currentRoot)
      (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
      (phaseMove_eq : state.1.2.2 = some phaseMove)
      (target : ProfiledRawJointIncidenceCode A (I := Unit))
      (target_allowed :
        profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1 target)
      (slot : ProfiledRawRightSlot A)
      (target_live : target.family.right () = some slot) :
      ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt tag state .right
        (.inl slot)

/-- Exact one-edge successor selected by a tag-relative table target. -/
structure ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt
    (tag : Tag A strategy hwin)
    (state next : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy
      hwin tag)
    (side : IndexedLineageSide)
    (root : ProfiledRawJointThreadRoot A) where
  childCode : LinkedCode A
  successor : next =
    (tag.tailCodePolicy A strategy hwin).successor state childCode
  child_oneSided : ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
    next.1.1 = .oneSided code
  child_move :
    match side with
    | .right => ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
        next.1.2.1 = some move
    | .left => ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
        next.1.2.2 = some move
  child_live :
    profiledRawJointHybridCurrentSlots A side next.1.1 () = some root

/-- A tail transition is exactly an allowed target edge of the already
selected tag policy. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt.allowed
    {tag : Tag A strategy hwin}
    {state next : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy
      hwin tag}
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
        hwin tag state next side root) :
    tag.TailAllowedTarget A strategy hwin state next := by
  exact ⟨transition.childCode, transition.successor.symm⟩

/-- Exact tail edges preserve reachability relative to the same tagged
child. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt.reachable
    {tag : Tag A strategy hwin}
    {state next : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy
      hwin tag}
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
        hwin tag state next side root)
    (hstate : tag.TailReachable A strategy hwin state) :
    tag.TailReachable A strategy hwin next := by
  rcases hstate with ⟨node, hnode⟩
  refine ⟨node ++ [transition.childCode], ?_⟩
  calc
    (tag.tailCodePolicy A strategy hwin).run
          (node ++ [transition.childCode]) =
        (tag.tailCodePolicy A strategy hwin).successor
          ((tag.tailCodePolicy A strategy hwin).run node)
          transition.childCode :=
      ((tag.tailCodePolicy A strategy hwin).successor_at node
        transition.childCode).symm
    _ = (tag.tailCodePolicy A strategy hwin).successor state
          transition.childCode := by rw [hnode]
    _ = next := transition.successor.symm

/-- The tag-relative target table closes under one exact successor.  This is
the recursive target/key law needed by every per-tag controller fibre. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt.exists_transition
    {tag : Tag A strategy hwin}
    (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
      tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (targetAt :
      ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt A strategy hwin
        tag state side root) :
    ∃ next : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
        tag,
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
          hwin tag state next side root) := by
  cases targetAt with
  | right currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      have hright := tag.exists_tailRightTargetSuccessor A strategy hwin state
          hreachable currentCode hcode currentRoot hcurrent phaseMove hphase
            target hallowed
      dsimp only at hright
      rcases hright with
        ⟨move, source, actual, _hsourceCode, _hsourceMove, hside,
          hsemanticChild, hchildAnnotation, hchildBare, hsuccessor⟩
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      let next :=
        (tag.tailCodePolicy A strategy hwin).successor state childCode
      refine ⟨next, ⟨?_⟩⟩
      refine ⟨childCode, rfl, ?_, ?_, ?_⟩
      · refine ⟨target, ?_⟩
        dsimp only [next]
        rw [hsuccessor]
        exact hchildBare
      · obtain ⟨nextMove, hnextMove⟩ :=
          exists_profiledRawJointHybridPhysicalCompatible_leftMove_of_strictRight
            A strategy hwin source state.1.2 actual target slot hside
              hsemanticChild hlive
        change ∃ nextMove : ProfiledRawJointLeftPhysicalSiblingMove A,
          next.1.2.2 = some nextMove
        refine ⟨nextMove, ?_⟩
        dsimp only [next]
        rw [hsuccessor]
        dsimp only [childCode, sourceFreeBeliefParentLinkedNext]
        rw [hchildAnnotation]
        exact hnextMove
      · dsimp only [next, childCode]
        rw [hsuccessor]
        change profiledRawJointHybridCurrentSlots A .left childCode.1 () =
          some (.inr slot)
        rw [hchildBare]
        simpa [profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots,
          ProfiledRawJointIncidenceCode.family] using hlive
  | left currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      have hsource :=
        tag.exists_tailSemanticSource A strategy hwin state hreachable
      dsimp only at hsource
      rcases hsource with
        ⟨move, source, hsourceCode, hsourceMove, hcompatible, hchildren,
          hsuccessorAll⟩
      have hrootCurrent :
          profiledRawJointOneSidedCurrentSlots A .left currentCode () =
            some currentRoot := by
        rw [hcode] at hcurrent
        exact hcurrent
      have hsourceCode' : source.code A = .oneSided currentCode :=
        hsourceCode.trans hcode
      cases source with
      | common world =>
          simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode'
      | dead =>
          simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode'
      | oneSided semantic =>
        have hsemanticCode : semantic.code A = currentCode := by
          simpa [ProfiledRawJointHybridSemanticState.code] using hsourceCode'
        have hsemanticRoot :
            profiledRawJointOneSidedCurrentSlots A .left (semantic.code A) () =
              some currentRoot := by
          rw [hsemanticCode]
          exact hrootCurrent
        obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
          semantic.exists_left_member_of_currentSlot A () currentRoot
            hsemanticRoot
        have honeCompatible :
            ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
              semantic state.1.2 := by
          simpa [ProfiledRawJointHybridPhysicalCurrentCompatible] using
            hcompatible
        obtain ⟨actual, hside, hactualTarget⟩ :=
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_leftTargetChild
            A strategy semantic state.1.2 honeCompatible semanticMember hmember
              phaseMove hphase target hallowed
        have hsemanticChild :
            ((ProfiledRawJointHybridSemanticState.oneSided semantic).step A
                (.strict actual)).code A = .oneSided target := by
          simpa [ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointHybridSemanticState.code] using
              congrArg ProfiledRawJointHybridCode.oneSided hactualTarget
        have hchildAnnotation :
            move.2 (.strict actual) =
              profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
                (.oneSided semantic) state.1.2 (.strict actual) :=
          (hchildren (.strict actual)).symm
        let childCode := sourceFreeBeliefParentLinkedNext
          (profiledRawJointHybridNext A) state.1 move (.strict actual)
        have hchildBare : childCode.1 = .oneSided target := by
          change profiledRawJointHybridNext A state.1.1 move.1
              (.strict actual) = .oneSided target
          rw [← hsourceCode, ← hsourceMove,
            ← ProfiledRawJointHybridSemanticState.step_code]
          exact hsemanticChild
        have hsuccessor := hsuccessorAll (.strict actual)
        let next :=
          (tag.tailCodePolicy A strategy hwin).successor state childCode
        refine ⟨next, ⟨?_⟩⟩
        refine ⟨childCode, rfl, ?_, ?_, ?_⟩
        · refine ⟨target, ?_⟩
          dsimp only [next]
          rw [hsuccessor]
          exact hchildBare
        · obtain ⟨nextMove, hnextMove⟩ :=
            exists_profiledRawJointHybridPhysicalCompatible_rightMove_of_strictLeft
              A strategy hwin (.oneSided semantic) state.1.2 actual target slot hside
                hsemanticChild hlive
          change ∃ nextMove : ProfiledRawJointRightPhysicalSiblingMove A,
            next.1.2.1 = some nextMove
          refine ⟨nextMove, ?_⟩
          dsimp only [next]
          rw [hsuccessor]
          dsimp only [childCode, sourceFreeBeliefParentLinkedNext]
          rw [hchildAnnotation]
          exact hnextMove
        · dsimp only [next, childCode]
          rw [hsuccessor]
          change profiledRawJointHybridCurrentSlots A .right childCode.1 () =
            some (.inl slot)
          rw [hchildBare]
          simpa [profiledRawJointHybridCurrentSlots,
            profiledRawJointOneSidedCurrentSlots,
            ProfiledRawJointIncidenceCode.family] using hlive

/-- Left-table mirror of `exists_tailRightTargetSuccessor`. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.exists_tailLeftTargetSuccessor
    (tag : Tag A strategy hwin)
    (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
      tag)
    (hreachable : tag.TailReachable A strategy hwin state)
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
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let bareDPA := profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A))
    let linkedDPA := sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A) bareDPA
    ∃ move : LinkedMove A,
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
              (tag.tailCodePolicy A strategy hwin).successor state childCode =
                (childCode, linkedDPA.step state.2 childCode) := by
  dsimp only
  have hsource :=
    tag.exists_tailSemanticSource A strategy hwin state hreachable
  dsimp only at hsource
  rcases hsource with
    ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩
  have hrootCurrent :
      profiledRawJointOneSidedCurrentSlots A .left currentCode () =
        some root := by
    rw [hcurrentCode] at hroot
    exact hroot
  have hsourceCode : source.code A = .oneSided currentCode :=
    hcode.trans hcurrentCode
  cases source with
  | common world =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
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
