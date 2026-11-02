/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalPhaseAnnotation

/-!
# Coherent carried-table target paths

This file is the reusable positive endpoint of the current-table repair.  A
physical block is admitted only when its live table is *literally* one
component of the current compatible-policy annotation.  The one-step target
theorems then select a child of that same outer policy.  Iterating these
transitions produces one `codeBranch`, not a mosaic of freshly rationalized
policies, and the selected physical roots form a literal live run of the
alternating-lineage monitor.

The existing default phase-live controller is deliberately not claimed to
instantiate this interface: its seam tables are built by a separate
decorated/root-pinned rationalization.  The remaining model construction is
to parameterize the activated block controller by the carried annotation so
that its target cuts supply `PhysicalCompatibleTableTargetAt` below.
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

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := PhysicalAnnotation A)

/-! ## The crossed child really carries its next physical table -/

/-- A strict-right semantic child with a live left lane has a concrete left
table in the annotation installed by that very edge. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_leftMove_of_strictRight
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
        current (.strict actual)).2 = some move := by
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
          simp [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove] at hroot
      | some move => exact ⟨move, rfl⟩

/-- Strict-left mirror: a live right lane comes with the right table installed
by the same semantic edge. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_rightMove_of_strictLeft
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
        current (.strict actual)).1 = some move := by
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
          simp [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove] at hroot
      | some move => exact ⟨move, rfl⟩

/-- Strengthened strict-right child-table theorem retaining the equation
between the installed left move's descriptor source and the live child slot.
This is the state-lineage datum forgotten by the older existence theorem. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_leftMoveSource_of_strictRight_base
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
  obtain ⟨move, hmove⟩ :=
    exists_profiledRawJointHybridPhysicalCompatible_leftMove_of_strictRight
      A strategy hwin source current actual target slot hside hchild hlive
  have hroot :=
    profiledRawJointHybridPhysicalAnnotationAdvance_strict_root_eq A strategy
      hwin source current actual
  have hlive' :
      profiledRawJointHybridCurrentSlots A actual.side.other
          ((source.step A (.strict actual)).code A) () =
        some (.inr slot) := by
    rw [hside, hchild]
    simpa [IndexedLineageSide.other, profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots,
      ProfiledRawJointIncidenceCode.family] using hlive
  rw [source.strictLiveRoot_eq_currentSlots A strategy actual, hlive'] at hroot
  refine ⟨move, hmove, ?_⟩
  simpa [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove] using hroot

/-- Strict-left/right-move mirror of the root-aligned base theorem. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_rightMoveSource_of_strictLeft_base
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
  obtain ⟨move, hmove⟩ :=
    exists_profiledRawJointHybridPhysicalCompatible_rightMove_of_strictLeft
      A strategy hwin source current actual target slot hside hchild hlive
  have hroot :=
    profiledRawJointHybridPhysicalAnnotationAdvance_strict_root_eq A strategy
      hwin source current actual
  have hlive' :
      profiledRawJointHybridCurrentSlots A actual.side.other
          ((source.step A (.strict actual)).code A) () =
        some (.inl slot) := by
    rw [hside, hchild]
    simpa [IndexedLineageSide.other, profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots,
      ProfiledRawJointIncidenceCode.family] using hlive
  rw [source.strictLiveRoot_eq_currentSlots A strategy actual, hlive'] at hroot
  refine ⟨move, hmove, ?_⟩
  simpa [profiledRawJointHybridStrictPhysicalCutRoot, hside, hmove] using hroot

/-! ## One literal current-table target -/

/-- Physical target data for one carried state.  The table equality fields
are the decisive ones: the move being executed is literally the relevant
component of `state.1.2`.  The final live-slot equation is the target root
reported by the physical cut. -/
inductive ProfiledRawJointHybridPhysicalCompatibleTableTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial) :
    IndexedLineageSide → ProfiledRawJointThreadRoot A → Prop where
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
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt state .left
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
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt state .right
        (.inl slot)

/-- Exact transition selected from one literal carried-table target. -/
structure ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state next : CompatibleState A strategy hwin initial)
    (side : IndexedLineageSide)
    (root : ProfiledRawJointThreadRoot A) where
  childCode : LinkedCode A
  successor : next = policy.successor state childCode
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

theorem
    ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt.right_move
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
        hwin policy state next .right root) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      next.1.2.1 = some move := by
  exact transition.child_move

theorem
    ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt.left_move
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
        hwin policy state next .left root) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      next.1.2.2 = some move := by
  exact transition.child_move

/-- A compatible-policy transition retaining the equation between its live
lineage root and the descriptor source of the physical move installed in the
child annotation. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state next : CompatibleState A strategy hwin initial)
    (side : IndexedLineageSide)
    (root : ProfiledRawJointThreadRoot A) where
  transition :
    ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy hwin
      policy state next side root
  move_source :
    match side with
    | .right => ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
        next.1.2.1 = some move ∧ root = .inl move.1.source
    | .left => ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
        next.1.2.2 = some move ∧ root = .inr move.1.source

namespace
    ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt

theorem right_move_source
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {slot : ProfiledRawRightSlot A}
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt A
        strategy hwin policy state next .right (.inl slot)) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      next.1.2.1 = some move ∧ move.1.source = slot := by
  rcases aligned.move_source with ⟨move, hmove, hroot⟩
  exact ⟨move, hmove, Sum.inl.inj hroot.symm⟩

theorem left_move_source
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state next : CompatibleState A strategy hwin initial}
    {slot : ProfiledRawLeftSlot A}
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt A
        strategy hwin policy state next .left (.inr slot)) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      next.1.2.2 = some move ∧ move.1.source = slot := by
  rcases aligned.move_source with ⟨move, hmove, hroot⟩
  exact ⟨move, hmove, Sum.inr.inj hroot.symm⟩

end
  ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt

/-- One actual carried table target extends the same compatible outer policy
by one exact linked child code. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleTableTargetAt.exists_transition
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (targetAt :
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state side root) :
    ∃ next : CompatibleState A strategy hwin initial,
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A
          strategy hwin policy state next side root) := by
  cases targetAt with
  | right currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      rcases
          exists_profiledRawJointHybridPhysicalCompatibleRightTargetSuccessor
            A strategy hwin initial policy state hreachable currentCode hcode
              currentRoot hcurrent phaseMove hphase target hallowed with
        ⟨move, source, actual, _hsourceCode, _hsourceMove, hside,
          hsemanticChild, hchildAnnotation, hchildBare, hsuccessor⟩
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      let next := policy.successor state childCode
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
      dsimp only [next, childCode]
      rw [hsuccessor]
      change profiledRawJointHybridCurrentSlots A .left childCode.1 () =
        some (.inr slot)
      rw [hchildBare]
      simpa [profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointIncidenceCode.family] using hlive
  | left currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      rcases
          exists_profiledRawJointHybridPhysicalCompatibleLeftTargetSuccessor
            A strategy hwin initial policy state hreachable currentCode hcode
              currentRoot hcurrent phaseMove hphase target hallowed with
        ⟨move, source, actual, _hsourceCode, _hsourceMove, hside,
          hsemanticChild, hchildAnnotation, hchildBare, hsuccessor⟩
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      let next := policy.successor state childCode
      refine ⟨next, ⟨?_⟩⟩
      refine ⟨childCode, rfl, ?_, ?_, ?_⟩
      · refine ⟨target, ?_⟩
        dsimp only [next]
        rw [hsuccessor]
        exact hchildBare
      · obtain ⟨nextMove, hnextMove⟩ :=
          exists_profiledRawJointHybridPhysicalCompatible_rightMove_of_strictLeft
            A strategy hwin source state.1.2 actual target slot hside
              hsemanticChild hlive
        change ∃ nextMove : ProfiledRawJointRightPhysicalSiblingMove A,
          next.1.2.1 = some nextMove
        refine ⟨nextMove, ?_⟩
        dsimp only [next]
        rw [hsuccessor]
        dsimp only [childCode, sourceFreeBeliefParentLinkedNext]
        rw [hchildAnnotation]
        exact hnextMove
      dsimp only [next, childCode]
      rw [hsuccessor]
      change profiledRawJointHybridCurrentSlots A .right childCode.1 () =
        some (.inl slot)
      rw [hchildBare]
      simpa [profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointIncidenceCode.family] using hlive

/-- Strengthened target closure retaining the physical move-source/root
equation before the compatible successor is stored in a finite table. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleTableTargetAt.exists_rootAlignedTransition
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (targetAt :
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state side root) :
    ∃ next : CompatibleState A strategy hwin initial,
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt
          A strategy hwin policy state next side root) := by
  cases targetAt with
  | right currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      rcases
          exists_profiledRawJointHybridPhysicalCompatibleRightTargetSuccessor
            A strategy hwin initial policy state hreachable currentCode hcode
              currentRoot hcurrent phaseMove hphase target hallowed with
        ⟨move, source, actual, _hsourceCode, _hsourceMove, hside,
          hsemanticChild, hchildAnnotation, hchildBare, hsuccessor⟩
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      let next := policy.successor state childCode
      obtain ⟨nextMove, hnextMoveAt, hnextSource⟩ :=
        exists_profiledRawJointHybridPhysicalCompatible_leftMoveSource_of_strictRight_base
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
          ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
            hwin policy state next .left (.inr slot) :=
        { childCode := childCode
          successor := rfl
          child_oneSided := ⟨target, hnextBare⟩
          child_move := ⟨nextMove, hnextMove⟩
          child_live := hnextLive }
      refine ⟨next, ⟨transition, ?_⟩⟩
      exact ⟨nextMove, hnextMove, congrArg Sum.inr hnextSource.symm⟩
  | left currentCode hcode currentRoot hcurrent phaseMove hphase target
      hallowed slot hlive =>
      rcases
          exists_profiledRawJointHybridPhysicalCompatibleLeftTargetSuccessor
            A strategy hwin initial policy state hreachable currentCode hcode
              currentRoot hcurrent phaseMove hphase target hallowed with
        ⟨move, source, actual, _hsourceCode, _hsourceMove, hside,
          hsemanticChild, hchildAnnotation, hchildBare, hsuccessor⟩
      let childCode := sourceFreeBeliefParentLinkedNext
        (profiledRawJointHybridNext A) state.1 move (.strict actual)
      let next := policy.successor state childCode
      obtain ⟨nextMove, hnextMoveAt, hnextSource⟩ :=
        exists_profiledRawJointHybridPhysicalCompatible_rightMoveSource_of_strictLeft_base
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
          ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
            hwin policy state next .right (.inl slot) :=
        { childCode := childCode
          successor := rfl
          child_oneSided := ⟨target, hnextBare⟩
          child_move := ⟨nextMove, hnextMove⟩
          child_live := hnextLive }
      refine ⟨next, ⟨transition, ?_⟩⟩
      exact ⟨nextMove, hnextMove, congrArg Sum.inl hnextSource.symm⟩

/-! ## Iteration and literal live lineage -/

/-- Side after `n` alternating monitor transitions. -/
def profiledRawJointHybridPhysicalCompatibleSideAfter
    (initialSide : IndexedLineageSide) : Nat → IndexedLineageSide
  | 0 => initialSide
  | n + 1 =>
      (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide n).other

@[simp] theorem profiledRawJointHybridPhysicalCompatibleSideAfter_zero
    (initialSide : IndexedLineageSide) :
    profiledRawJointHybridPhysicalCompatibleSideAfter initialSide 0 =
      initialSide :=
  rfl

@[simp] theorem profiledRawJointHybridPhysicalCompatibleSideAfter_succ
    (initialSide : IndexedLineageSide) (n : Nat) :
    profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 1) =
      (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide n).other :=
  rfl

/-- A coherent infinite path made exclusively of carried-table transitions.
The controller-side refactor owes precisely such a path at its physical block
cuts. -/
structure ProfiledRawJointHybridPhysicalCompatibleTargetPath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) where
  state : Nat → CompatibleState A strategy hwin initial
  initial_state : state 0 = policy.run []
  initial_code :
    (state 0).1.1 =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  initial_live :
    profiledRawJointHybridCurrentSlots A initialSide (state 0).1.1 () =
      some initialRoot
  rootAt : Nat → ProfiledRawJointThreadRoot A
  transition : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy hwin
      policy (state n) (state (n + 1))
      (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 1))
      (rootAt n)

namespace ProfiledRawJointHybridPhysicalCompatibleTargetPath

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}

/-- The finite child-code branch selected by the exact carried transitions. -/
noncomputable def codeBranch
    (path : ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin
      policy) : Nat → LinkedCode A :=
  fun n ↦ (path.transition n).childCode

/-- Abstract path states are exactly the states of one branch of the selected
compatible policy. -/
theorem state_eq_run
    (path : ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin
      policy) : ∀ n : Nat,
    path.state n = policy.run (branchNode (path.codeBranch A strategy hwin) n) := by
  intro n
  induction n with
  | zero => exact path.initial_state
  | succ n ih =>
      calc
        path.state (n + 1) =
            policy.successor (path.state n)
              (path.codeBranch A strategy hwin n) := by
          simpa [codeBranch] using (path.transition n).successor
        _ = policy.successor
              (policy.run (branchNode
                (path.codeBranch A strategy hwin) n))
              (path.codeBranch A strategy hwin n) := by
          exact congrArg
            (fun state ↦ policy.successor state
              (path.codeBranch A strategy hwin n)) ih
        _ = policy.run
              (branchNode (path.codeBranch A strategy hwin) (n + 1)) := by
          exact policy.successor_at
            (branchNode (path.codeBranch A strategy hwin) n)
            (path.codeBranch A strategy hwin n)

/-- Bare child-code word of this one compatible policy branch. -/
noncomputable def codeWord
    (path : ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin
      policy) : OmegaWord (ProfiledRawJointHybridCode A) :=
  fun n ↦ (path.state (n + 1)).1.1

theorem codeWord_eq_policyRun
    (path : ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin
      policy) (n : Nat) :
    path.codeWord A strategy hwin n =
      (policy.run
        (branchNode (path.codeBranch A strategy hwin) (n + 1))).1.1 := by
  exact congrArg (fun state ↦ state.1.1)
    (path.state_eq_run A strategy hwin (n + 1))

/-- At every positive depth, the code-only alternating monitor is literally
live at the physical target root of the corresponding carried-table block. -/
theorem lineage_live_at_target
    (path : ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin
      policy) : ∀ n : Nat,
    codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridCurrentSlots A)
        (path.codeWord A strategy hwin)
        path.initialSide () (n + 1) =
      (path.codeWord A strategy hwin n,
        .live
          (profiledRawJointHybridPhysicalCompatibleSideAfter path.initialSide
            (n + 1))
          () (path.rootAt n)) := by
  intro n
  induction n with
  | zero =>
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      rw [codedAlternatingIndexedLineageRun_zero]
      have hroot :
          profiledRawJointHybridCurrentSlots A path.initialSide
              (.common ((profiledRawJointCommonWorldFamily A initial
                ).incidenceCode A)) () =
            some path.initialRoot := by
        rw [← path.initial_code]
        exact path.initial_live
      exact codedAlternatingIndexedLineageCodeStep_initial_of
        (profiledRawJointHybridCurrentSlots A)
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (path.codeWord A strategy hwin 0) path.initialSide ()
        path.initialRoot (path.rootAt 0) hroot
        (path.transition 0).child_live
  | succ n ih =>
      change
        codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) childCode ↦ childCode)
            (profiledRawJointHybridCurrentSlots A)
            (codedAlternatingIndexedLineageCodeChild
              (profiledRawJointHybridCurrentSlots A))
            (codedAlternatingIndexedLineageCodeRun
              (.common ((profiledRawJointCommonWorldFamily A initial
                ).incidenceCode A))
              (profiledRawJointHybridCurrentSlots A)
              (path.codeWord A strategy hwin) path.initialSide () (n + 1))
            ((), path.codeWord A strategy hwin (n + 1))
            (path.initialSide, ()) = _
      rw [ih]
      simpa only [
        profiledRawJointHybridPhysicalCompatibleSideAfter_succ] using
        codedAlternatingIndexedLineageCodeStep_live_of
        (profiledRawJointHybridCurrentSlots A)
        (path.codeWord A strategy hwin n)
        (path.codeWord A strategy hwin (n + 1))
        (profiledRawJointHybridPhysicalCompatibleSideAfter path.initialSide
          (n + 1))
        () (path.rootAt n) (path.rootAt (n + 1))
        (path.initialSide, ())
        (path.transition n).child_live
        (path.transition (n + 1)).child_live

end ProfiledRawJointHybridPhysicalCompatibleTargetPath

end

end DetParityAutomaton

end DistributedSynthesis
