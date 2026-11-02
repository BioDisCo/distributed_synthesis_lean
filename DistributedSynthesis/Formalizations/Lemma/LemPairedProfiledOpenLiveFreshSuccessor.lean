/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSemanticLocalFibres
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCorrelatedSemanticStep

/-!
# Fresh provenance of correlated semantic successors

Every nonempty semantic handoff is built from literal fresh children of the
original strategy.  The handoff structure stores this fact indirectly through
its exact memory-step equation.  This file recovers the corresponding
`Proc*ViewClassChildProvenance` for every member of the reified child lane.

Consequently a correlated successor whose two normalized survivor families
are nonempty is again a `ProfiledOpenIndexedLiveFreshSemanticPoint`.  The two
nonemptiness hypotheses are essential for this particular wrapper: the total
correlated semantics deliberately permits one or both lanes to become
inactive when a pivot is absent.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Every reified child member is literally fresh -/

/-- Every member of a right-to-left handoff's left child lane retains a
literal fresh-child provenance witness. -/
noncomputable def ProfiledOpenIndexedRightToLeftSemanticHandoff.childFresh
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : state.right = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (handoff : ProfiledOpenIndexedRightToLeftSemanticHandoff A strategy hwin
      basis state lane hright direction)
    (member : {root // root ∈ handoff.child.source.1}) :
    ProcTwoViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (handoff.child.realization.entry member) := by
  classical
  let lineage := Classical.choose (handoff.child.covers member)
  have hmemberAt : handoff.child.memberAt lineage = some member :=
    Classical.choose_spec (handoff.child.covers member)
  let raw := profiledOpenIndexedRightRawChildCode A
    (state.code A strategy hwin basis)
    (state.move A strategy hwin basis) direction
  have hslot : raw.deduplicateRoots.rootSlots lineage =
      some (.left member.1) := by
    have h := congrFun handoff.child_slots lineage
    simpa [raw, ProfiledOpenIndexedLeftSemanticShadow.slots, hmemberAt] using
      h.symm
  have hrow : ∃ row, raw.deduplicateRoots lineage =
      some (row, .left member.1) :=
    (raw.deduplicateRoots.rootSlots_eq_some_iff lineage
      (.left member.1)).mp hslot
  let row := Classical.choose hrow
  have hcode : raw.deduplicateRoots lineage =
      some (row, .left member.1) := Classical.choose_spec hrow
  let survivor : raw.RootSurvivor :=
    ⟨(lineage, (row, .left member.1)), hcode⟩
  have hmemberEq : handoff.childMember survivor = member := by
    apply Option.some.inj
    exact (handoff.childMember_at survivor).symm.trans hmemberAt
  have hcanonical := pairedStrategyMemory_step_eq_procTwoViewClassChild A
    lane.realization.entry lane.realization.minimum
    (handoff.sourceMember survivor) handoff.semanticPast direction.rightInput
    survivor.row
  have hmemory := handoff.memory_step survivor
  have hentry := (PairedStrategyMemory.processTwo.inj
    (hcanonical.symm.trans hmemory)).1
  refine {
    Index := ULift.{max i u v x y s} {root // root ∈ lane.source.1}
    entry := fun lifted => lane.realization.entry lifted.down
    past := handoff.semanticPast
    input := direction.rightInput
    candidate := (ULift.up (handoff.sourceMember survivor), survivor.row)
    child_eq := ?_ }
  rw [← hmemberEq]
  change handoff.child.realization.entry (handoff.childMember survivor) =
    procTwoViewClassChild strategy lane.realization.entry handoff.semanticPast
      direction.rightInput (handoff.sourceMember survivor, survivor.row)
  exact hentry.symm

/-- Left-to-right mirror: every member of the right child lane is a literal
fresh process-one child. -/
noncomputable def ProfiledOpenIndexedLeftToRightSemanticHandoff.childFresh
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hleft : state.left = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (handoff : ProfiledOpenIndexedLeftToRightSemanticHandoff A strategy hwin
      basis state lane hleft direction)
    (member : {root // root ∈ handoff.child.source.1}) :
    ProcOneViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (handoff.child.realization.entry member) := by
  classical
  let lineage := Classical.choose (handoff.child.covers member)
  have hmemberAt : handoff.child.memberAt lineage = some member :=
    Classical.choose_spec (handoff.child.covers member)
  let raw := profiledOpenIndexedLeftRawChildCode A
    (state.code A strategy hwin basis)
    (state.move A strategy hwin basis) direction
  have hslot : raw.deduplicateRoots.rootSlots lineage =
      some (.right member.1) := by
    have h := congrFun handoff.child_slots lineage
    simpa [raw, ProfiledOpenIndexedRightSemanticShadow.slots, hmemberAt] using
      h.symm
  have hrow : ∃ row, raw.deduplicateRoots lineage =
      some (row, .right member.1) :=
    (raw.deduplicateRoots.rootSlots_eq_some_iff lineage
      (.right member.1)).mp hslot
  let row := Classical.choose hrow
  have hcode : raw.deduplicateRoots lineage =
      some (row, .right member.1) := Classical.choose_spec hrow
  let survivor : raw.RootSurvivor :=
    ⟨(lineage, (row, .right member.1)), hcode⟩
  have hmemberEq : handoff.childMember survivor = member := by
    apply Option.some.inj
    exact (handoff.childMember_at survivor).symm.trans hmemberAt
  have hcanonical := pairedStrategyMemory_step_eq_procOneViewClassChild A
    lane.realization.entry lane.realization.minimum
    (handoff.sourceMember survivor) handoff.semanticPast direction.leftInput
    survivor.row
  have hmemory := handoff.memory_step survivor
  have hentry := (PairedStrategyMemory.processOne.inj
    (hcanonical.symm.trans hmemory)).1
  refine {
    Index := ULift.{max i u v x y s} {root // root ∈ lane.source.1}
    entry := fun lifted => lane.realization.entry lifted.down
    past := handoff.semanticPast
    input := direction.leftInput
    candidate := (ULift.up (handoff.sourceMember survivor), survivor.row)
    child_eq := ?_ }
  rw [← hmemberEq]
  change handoff.child.realization.entry (handoff.childMember survivor) =
    procOneViewClassChild strategy lane.realization.entry handoff.semanticPast
      direction.leftInput (handoff.sourceMember survivor, survivor.row)
  exact hentry.symm

/-! ## A total optional-fresh semantic carrier -/

/-- A correlated semantic state with fresh-child provenance for every member
of every lane which is actually active.  Unlike `LiveFreshSemanticPoint`,
this carrier also represents right-only, left-only, and fully inactive
states. -/
structure ProfiledOpenIndexedOptionalFreshSemanticPoint where
  state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
    (I := I)
  rightFresh : ∀
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I)), state.right = some lane →
    ∀ member : {root // root ∈ lane.source.1},
      ProcOneViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
        (lane.realization.entry member)
  leftFresh : ∀
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I)), state.left = some lane →
    ∀ member : {root // root ∈ lane.source.1},
      ProcTwoViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
        (lane.realization.entry member)

/-- Forget the assertion that both lanes are active while retaining all of
the live point's proof-side provenance. -/
noncomputable def ProfiledOpenIndexedOptionalFreshSemanticPoint.ofLiveFresh
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin basis
      (I := I) where
  state := point.state
  rightFresh := by
    intro lane hactive member
    have hlane : lane = point.rightLane := by
      exact Option.some.inj (hactive.symm.trans point.right_eq)
    subst lane
    exact point.rightFresh member
  leftFresh := by
    intro lane hactive member
    have hlane : lane = point.leftLane := by
      exact Option.some.inj (hactive.symm.trans point.left_eq)
    subst lane
    exact point.leftFresh member

/-- The four exhaustive activity shapes of a correlated semantic state. -/
inductive ProfiledOpenIndexedCorrelatedLaneShape
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) where
  | both
      (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I))
      (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I))
      (right_eq : state.right = some rightLane)
      (left_eq : state.left = some leftLane)
  | rightOnly
      (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I))
      (right_eq : state.right = some rightLane)
      (left_eq : state.left = none)
  | leftOnly
      (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I))
      (right_eq : state.right = none)
      (left_eq : state.left = some leftLane)
  | inactive (right_eq : state.right = none) (left_eq : state.left = none)

/-- Every correlated state is constructively classified into its live-both,
single-lane, or inactive shape. -/
def ProfiledOpenIndexedCorrelatedSemanticState.laneShape
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedCorrelatedLaneShape A strategy hwin basis state := by
  cases hright : state.right with
  | none =>
      cases hleft : state.left with
      | none => exact .inactive hright hleft
      | some leftLane => exact .leftOnly leftLane hright hleft
  | some rightLane =>
      cases hleft : state.left with
      | none => exact .rightOnly rightLane hright hleft
      | some leftLane => exact .both rightLane leftLane hright hleft

/-- The live-both case of the total optional carrier recovers exactly the old
source-bank input type. -/
noncomputable def ProfiledOpenIndexedOptionalFreshSemanticPoint.toLiveFresh
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (right_eq : point.state.right = some rightLane)
    (left_eq : point.state.left = some leftLane) :
    ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I) where
  state := point.state
  rightLane := rightLane
  right_eq := right_eq
  leftLane := leftLane
  left_eq := left_eq
  rightFresh := point.rightFresh rightLane right_eq
  leftFresh := point.leftFresh leftLane left_eq

/-- The total correlated successor preserves optional freshness
unconditionally.  If one normalized family is empty, that lane is absent and
there is no bogus provenance obligation for it. -/
noncomputable def profiledOpenIndexedOptionalFreshSemanticNext
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin basis
      (I := I) where
  state := profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
    point.state direction
  rightFresh := by
    intro child hactive member
    by_cases hsurvivor : Nonempty
        (profiledOpenIndexedLeftRawChildCode A
          (point.state.code A strategy hwin basis)
          (point.state.move A strategy hwin basis) direction).RootSurvivor
    · let oldLane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin
        basis point.state direction hsurvivor
      let hold := profiledOpenIndexedLeftLaneOfSurvivor_spec A strategy hwin
        basis point.state direction hsurvivor
      let handoff := profiledOpenIndexedChosenLeftToRightHandoff A strategy
        hwin basis point.state oldLane hold direction hsurvivor
      have hstored :
          (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
            point.state direction).right = some handoff.child := by
        simp [profiledOpenIndexedCorrelatedSemanticNext,
          profiledOpenIndexedCorrelatedNextRight, hsurvivor, oldLane,
          handoff]
      have hchild : child = handoff.child :=
        Option.some.inj (hactive.symm.trans hstored)
      subst child
      exact ProfiledOpenIndexedLeftToRightSemanticHandoff.childFresh A
        strategy hwin basis point.state oldLane hold direction handoff member
    · have hnone :
          (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
            point.state direction).right = none := by
        simp [profiledOpenIndexedCorrelatedSemanticNext,
          profiledOpenIndexedCorrelatedNextRight, hsurvivor]
      cases hactive.symm.trans hnone
  leftFresh := by
    intro child hactive member
    by_cases hsurvivor : Nonempty
        (profiledOpenIndexedRightRawChildCode A
          (point.state.code A strategy hwin basis)
          (point.state.move A strategy hwin basis) direction).RootSurvivor
    · let oldLane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin
        basis point.state direction hsurvivor
      let hold := profiledOpenIndexedRightLaneOfSurvivor_spec A strategy hwin
        basis point.state direction hsurvivor
      let handoff := profiledOpenIndexedChosenRightToLeftHandoff A strategy
        hwin basis point.state oldLane hold direction hsurvivor
      have hstored :
          (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
            point.state direction).left = some handoff.child := by
        simp [profiledOpenIndexedCorrelatedSemanticNext,
          profiledOpenIndexedCorrelatedNextLeft, hsurvivor, oldLane,
          handoff]
      have hchild : child = handoff.child :=
        Option.some.inj (hactive.symm.trans hstored)
      subst child
      exact ProfiledOpenIndexedRightToLeftSemanticHandoff.childFresh A
        strategy hwin basis point.state oldLane hold direction handoff member
    · have hnone :
          (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
            point.state direction).left = none := by
        simp [profiledOpenIndexedCorrelatedSemanticNext,
          profiledOpenIndexedCorrelatedNextLeft, hsurvivor]
      cases hactive.symm.trans hnone

/-! ## Exact activity routing by the two survivor tests -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The successor right lane is active exactly when the old left raw child
family has a normalized survivor. -/
theorem profiledOpenIndexedCorrelatedSemanticNext_right_active_iff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (∃ lane, (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
        state direction).right = some lane) ↔
      Nonempty
        (profiledOpenIndexedLeftRawChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).RootSurvivor := by
  classical
  constructor
  · rintro ⟨lane, hactive⟩
    by_contra hdead
    have hnone :
        (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
          state direction).right = none := by
      simp [profiledOpenIndexedCorrelatedSemanticNext,
        profiledOpenIndexedCorrelatedNextRight, hdead]
    cases hactive.symm.trans hnone
  · intro hlive
    let lane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin basis
      state direction hlive
    let hleft := profiledOpenIndexedLeftLaneOfSurvivor_spec A strategy hwin
      basis state direction hlive
    let handoff := profiledOpenIndexedChosenLeftToRightHandoff A strategy hwin
      basis state lane hleft direction hlive
    refine ⟨handoff.child, ?_⟩
    simp [profiledOpenIndexedCorrelatedSemanticNext,
      profiledOpenIndexedCorrelatedNextRight, hlive, lane, handoff]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-lane mirror of the exact activity test. -/
theorem profiledOpenIndexedCorrelatedSemanticNext_left_active_iff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (∃ lane, (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
        state direction).left = some lane) ↔
      Nonempty
        (profiledOpenIndexedRightRawChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).RootSurvivor := by
  classical
  constructor
  · rintro ⟨lane, hactive⟩
    by_contra hdead
    have hnone :
        (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
          state direction).left = none := by
      simp [profiledOpenIndexedCorrelatedSemanticNext,
        profiledOpenIndexedCorrelatedNextLeft, hdead]
    cases hactive.symm.trans hnone
  · intro hlive
    let lane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin basis
      state direction hlive
    let hright := profiledOpenIndexedRightLaneOfSurvivor_spec A strategy hwin
      basis state direction hlive
    let handoff := profiledOpenIndexedChosenRightToLeftHandoff A strategy hwin
      basis state lane hright direction hlive
    refine ⟨handoff.child, ?_⟩
    simp [profiledOpenIndexedCorrelatedSemanticNext,
      profiledOpenIndexedCorrelatedNextLeft, hlive, lane, handoff]

/-! ## Conditional closure of the live-fresh wrapper -/

/-- If both normalized survivor families are nonempty, the total correlated
successor is again live on both sides and every member of both child lanes has
literal fresh provenance. -/
noncomputable def profiledOpenIndexedLiveFreshSemanticNext
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hrightSurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (point.state.code A strategy hwin basis)
        (point.state.move A strategy hwin basis) direction).RootSurvivor)
    (hleftSurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (point.state.code A strategy hwin basis)
        (point.state.move A strategy hwin basis) direction).RootSurvivor) :
    ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I) := by
  let rightSurvivor := Classical.choice hrightSurvivor
  let leftSurvivor := Classical.choice hleftSurvivor
  let rightHandoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A
    strategy hwin basis point.state direction rightSurvivor
  let leftHandoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A
    strategy hwin basis point.state direction leftSurvivor
  exact {
    state := profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
      point.state direction
    rightLane := rightHandoff.child
    right_eq := by
      simpa [rightHandoff, rightSurvivor] using
        profiledOpenIndexedCorrelatedSemanticNext_right_eq_child A strategy
          hwin basis point.state direction rightSurvivor
    leftLane := leftHandoff.child
    left_eq := by
      simpa [leftHandoff, leftSurvivor] using
        profiledOpenIndexedCorrelatedSemanticNext_left_eq_child A strategy
          hwin basis point.state direction leftSurvivor
    rightFresh := fun member =>
      ProfiledOpenIndexedLeftToRightSemanticHandoff.childFresh A strategy hwin
        basis _ _ _ _ rightHandoff member
    leftFresh := fun member =>
      ProfiledOpenIndexedRightToLeftSemanticHandoff.childFresh A strategy hwin
        basis _ _ _ _ leftHandoff member }

end

end DetParityAutomaton

end DistributedSynthesis
