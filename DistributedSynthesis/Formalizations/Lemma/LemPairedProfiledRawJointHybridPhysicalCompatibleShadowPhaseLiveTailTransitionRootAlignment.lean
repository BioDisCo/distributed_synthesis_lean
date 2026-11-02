/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailPolicy

/-!
# Root alignment of exact transitions below a delayed tag

The tail target interface records both a live child root and a physical move
installed in that child.  The plain transition structure intentionally does
not relate these two fields.  At the point where a checked table target is
turned into a literal semantic successor, however, the carried-annotation
root theorem proves the stronger fact: the installed move's descriptor source
is exactly that live root.

This file retains that equation in a wrapper around the existing transition.
It does not change the tail policy or add information to an executable local
state.  The equation is proof-side data used to feed the next physical cut's
entry-state hypothesis.
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

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-! ## The carried strict-edge root also identifies the move source -/

/-- A strict-right child with a live left slot carries a left move whose
descriptor source is literally that slot. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_leftMoveSource_of_strictRight
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hside : actual.side = .right)
    (hchild : (source.step A (.strict actual)).code A = .oneSided target)
    (hlive : target.family.left () = some slot) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
          current (.strict actual)).2 = some move ∧
        move.1.source = slot := by
  cases hstep : source.step A (.strict actual) with
  | common world =>
      rw [hstep] at hchild
      simp [ProfiledRawJointHybridSemanticState.code] at hchild
  | dead =>
      rw [hstep] at hchild
      simp [ProfiledRawJointHybridSemanticState.code] at hchild
  | oneSided child =>
      have hcode : child.code A = target := by
        rw [hstep] at hchild
        simpa [ProfiledRawJointHybridSemanticState.code] using hchild
      have hroot :=
        profiledRawJointHybridPhysicalPhaseAdvance_rightRoot_eq A strategy hwin
          source current actual child target slot hside hstep hcode hlive
      cases hmove :
          (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
            source current (.strict actual)).2 with
      | none =>
          simp [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove]
            at hroot
      | some move =>
          refine ⟨move, rfl, ?_⟩
          simpa [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove]
            using hroot

/-- Strict-left mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_rightMoveSource_of_strictLeft
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hside : actual.side = .left)
    (hchild : (source.step A (.strict actual)).code A = .oneSided target)
    (hlive : target.family.right () = some slot) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
          current (.strict actual)).1 = some move ∧
        move.1.source = slot := by
  cases hstep : source.step A (.strict actual) with
  | common world =>
      rw [hstep] at hchild
      simp [ProfiledRawJointHybridSemanticState.code] at hchild
  | dead =>
      rw [hstep] at hchild
      simp [ProfiledRawJointHybridSemanticState.code] at hchild
  | oneSided child =>
      have hcode : child.code A = target := by
        rw [hstep] at hchild
        simpa [ProfiledRawJointHybridSemanticState.code] using hchild
      have hroot :=
        profiledRawJointHybridPhysicalPhaseAdvance_leftRoot_eq A strategy hwin
          source current actual child target slot hside hstep hcode hlive
      cases hmove :
          (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
            source current (.strict actual)).1 with
      | none =>
          simp [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove]
            at hroot
      | some move =>
          refine ⟨move, rfl, ?_⟩
          simpa [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove]
            using hroot

/-! ## A transition wrapper retaining the source/root equation -/

/-- An exact tail transition together with the equation identifying the
installed move's descriptor source with its live lineage root. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt
    (tag : Tag A strategy hwin)
    (state next : TailState A strategy hwin tag)
    (side : IndexedLineageSide)
    (root : ProfiledRawJointThreadRoot A) where
  transition :
    ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy hwin
      tag state next side root
  move_source :
    match side with
    | .right => ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
        next.1.2.1 = some move ∧ root = .inl move.1.source
    | .left => ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
        next.1.2.2 = some move ∧ root = .inr move.1.source

namespace
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt

/-- Forgetting root alignment recovers the existing allowed-tail edge. -/
theorem allowed
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (aligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
        strategy hwin tag state next side root) :
    tag.TailAllowedTarget A strategy hwin state next :=
  aligned.transition.allowed A strategy hwin

/-- Root-aligned exact edges preserve tagged-tail reachability. -/
theorem reachable
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (aligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
        strategy hwin tag state next side root)
    (hstate : tag.TailReachable A strategy hwin state) :
    tag.TailReachable A strategy hwin next :=
  aligned.transition.reachable A strategy hwin hstate

/-- In a right-live successor, the installed right table is based at the
same right slot named by the live root. -/
theorem right_move_source
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {slot : ProfiledRawRightSlot A}
    (aligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
        strategy hwin tag state next .right (.inl slot)) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      next.1.2.1 = some move ∧ move.1.source = slot := by
  rcases aligned.move_source with ⟨move, hmove, hroot⟩
  exact ⟨move, hmove, Sum.inl.inj hroot.symm⟩

/-- Left-live mirror. -/
theorem left_move_source
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {slot : ProfiledRawLeftSlot A}
    (aligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
        strategy hwin tag state next .left (.inr slot)) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      next.1.2.2 = some move ∧ move.1.source = slot := by
  rcases aligned.move_source with ⟨move, hmove, hroot⟩
  exact ⟨move, hmove, Sum.inr.inj hroot.symm⟩

end
  ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt

/-! ## Checked table targets emit root-aligned transitions -/

/-- Strengthened target-table closure.  This is the exact constructor boundary
at which the source/root equation is still available. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt.exists_rootAlignedTransition
    {tag : Tag A strategy hwin}
    (state : TailState A strategy hwin tag)
    (hreachable : tag.TailReachable A strategy hwin state)
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (targetAt :
      ProfiledRawJointHybridShadowPhaseLiveTailTableTargetAt A strategy hwin tag
        state side root) :
    ∃ next : TailState A strategy hwin tag,
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
          strategy hwin tag state next side root) := by
  cases targetAt with
  | right currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      have hright := tag.exists_tailRightTargetSuccessor A strategy hwin state
        hreachable currentCode hcode currentRoot hcurrent phaseMove hphase target
          hallowed
      dsimp only at hright
      rcases hright with
        ⟨move, source, actual, _hsourceCode, _hsourceMove, hside,
          hsemanticChild, hchildAnnotation, hchildBare, hsuccessor⟩
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      let next :=
        (tag.tailCodePolicy A strategy hwin).successor state childCode
      obtain ⟨nextMove, hnextMoveAt, hnextSource⟩ :=
        exists_profiledRawJointHybridPhysicalCompatible_leftMoveSource_of_strictRight
          A strategy hwin source state.1.2 actual target slot hside
            hsemanticChild hlive
      have hnextBare : next.1.1 = .oneSided target := by
        dsimp only [next]
        rw [hsuccessor]
        exact hchildBare
      have hnextMove : next.1.2.2 = some nextMove := by
        dsimp only [next]
        rw [hsuccessor]
        dsimp only [childCode, sourceFreeBeliefParentLinkedNext]
        rw [hchildAnnotation]
        exact hnextMoveAt
      have hnextLive :
          profiledRawJointHybridCurrentSlots A .left next.1.1 () =
            some (.inr slot) := by
        dsimp only [next, childCode]
        rw [hsuccessor]
        change profiledRawJointHybridCurrentSlots A .left childCode.1 () =
          some (.inr slot)
        rw [hchildBare]
        simpa [profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots,
          ProfiledRawJointIncidenceCode.family] using hlive
      let transition :
          ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
            hwin tag state next .left (.inr slot) :=
        { childCode := childCode
          successor := rfl
          child_oneSided := ⟨target, hnextBare⟩
          child_move := ⟨nextMove, hnextMove⟩
          child_live := hnextLive }
      refine ⟨next, ⟨transition, ?_⟩⟩
      exact ⟨nextMove, hnextMove, congrArg Sum.inr hnextSource.symm⟩
  | left currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      have hleft := tag.exists_tailLeftTargetSuccessor A strategy hwin state
        hreachable currentCode hcode currentRoot hcurrent phaseMove hphase target
          hallowed
      dsimp only at hleft
      rcases hleft with
        ⟨move, source, actual, _hsourceCode, _hsourceMove, hside,
          hsemanticChild, hchildAnnotation, hchildBare, hsuccessor⟩
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      let next :=
        (tag.tailCodePolicy A strategy hwin).successor state childCode
      obtain ⟨nextMove, hnextMoveAt, hnextSource⟩ :=
        exists_profiledRawJointHybridPhysicalCompatible_rightMoveSource_of_strictLeft
          A strategy hwin source state.1.2 actual target slot hside
            hsemanticChild hlive
      have hnextBare : next.1.1 = .oneSided target := by
        dsimp only [next]
        rw [hsuccessor]
        exact hchildBare
      have hnextMove : next.1.2.1 = some nextMove := by
        dsimp only [next]
        rw [hsuccessor]
        dsimp only [childCode, sourceFreeBeliefParentLinkedNext]
        rw [hchildAnnotation]
        exact hnextMoveAt
      have hnextLive :
          profiledRawJointHybridCurrentSlots A .right next.1.1 () =
            some (.inl slot) := by
        dsimp only [next, childCode]
        rw [hsuccessor]
        change profiledRawJointHybridCurrentSlots A .right childCode.1 () =
          some (.inl slot)
        rw [hchildBare]
        simpa [profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots,
          ProfiledRawJointIncidenceCode.family] using hlive
      let transition :
          ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
            hwin tag state next .right (.inl slot) :=
        { childCode := childCode
          successor := rfl
          child_oneSided := ⟨target, hnextBare⟩
          child_move := ⟨nextMove, hnextMove⟩
          child_live := hnextLive }
      refine ⟨next, ⟨transition, ?_⟩⟩
      exact ⟨nextMove, hnextMove, congrArg Sum.inl hnextSource.symm⟩

end

end DetParityAutomaton

end DistributedSynthesis
