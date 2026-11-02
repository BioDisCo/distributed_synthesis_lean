/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSurvivorLane
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedRightSurvivorLane

/-!
# Correlated semantic handoff through normalized indexed survivors

The right-to-left theorem below is the first complete model-specific raw
semantic step.  A single shared family-controller node yields one common
hidden past.  The normalized survivors are reified as one semantic child
lane, their public slots and reset pattern are exact, and every retained
memory is literally one operational step of the original winning strategy.
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

/-- Complete literal data of one nonempty right-to-left normalized handoff. -/
structure ProfiledOpenIndexedRightToLeftSemanticHandoff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : state.right = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) where
  semanticPast : List (In₂ × In₁)
  sourceMember :
    (profiledOpenIndexedRightRawChildCode A
      (state.code A strategy hwin basis)
      (state.move A strategy hwin basis) direction).RootSurvivor →
      {root // root ∈ lane.source.1}
  sourceMember_at : ∀ survivor,
    lane.memberAt survivor.lineage = some (sourceMember survivor)
  child : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis (I := I)
  child_slots :
    ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin basis
        (some child) =
      (profiledOpenIndexedRightChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).rootSlots
  child_pattern :
    ProfiledOpenIndexedLeftSemanticShadow.pattern A strategy hwin basis
        (some child) =
      profiledOpenIndexedActiveCanonicalRowPattern A
        (profiledOpenIndexedRightChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).rootSlots
  childMember :
    (profiledOpenIndexedRightRawChildCode A
      (state.code A strategy hwin basis)
      (state.move A strategy hwin basis) direction).RootSurvivor →
      {root // root ∈ child.source.1}
  childMember_at : ∀ survivor,
    child.memberAt survivor.lineage = some (childMember survivor)
  memory_step : ∀ survivor,
    PairedStrategyMemory.step (A := A)
        (.processOne (lane.realization.entry (sourceMember survivor))
          (lane.realization.minimum (sourceMember survivor)))
        (.fromOne survivor.row semanticPast direction.rightInput) =
      .processTwo (child.realization.entry (childMember survivor))
        (child.realization.minimum (childMember survivor))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- One common shared-node provenance produces a complete literal normalized
right-to-left handoff. -/
theorem exists_profiledOpenIndexedRightToLeftSemanticHandoff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : state.right = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    Nonempty (ProfiledOpenIndexedRightToLeftSemanticHandoff A strategy hwin
      basis state lane hright direction) := by
  classical
  let code := state.code A strategy hwin basis
  let move := state.move A strategy hwin basis
  let raw := profiledOpenIndexedRightRawChildCode A code move direction
  let table := (lane.realization.coherentTable A).table.toClassified A
    lane.source
  let leftMove := state.left.move A strategy hwin basis
  have hmove : move = (.right lane.source table, leftMove) := by
    simp [move, ProfiledOpenIndexedCorrelatedSemanticState.move, hright,
      ProfiledOpenIndexedRightSemanticShadow.move, table, leftMove]
  have hvalid : ProfiledOpenIndexedRightLaneValid A code.rightSlots
      (.right lane.source table) := by
    have hstateValid := (state.valid A strategy hwin basis).1
    change ProfiledOpenIndexedRightLaneValid A code.rightSlots move.1 at hstateValid
    rw [hmove] at hstateValid
    exact hstateValid
  rcases exists_profiledOpenRightClassifiedSharedNode_correlatedStep A
      lane.realization
      (profiledOpenIndexedRightSharedNode A code lane.source
        direction.rightTaggedPast)
      direction.rightInput with ⟨taggedPast, hroots, hviews⟩
  let semanticPast := taggedPast.map fun old => (old.1.2, old.2)
  let sourceMember : raw.RootSurvivor → {root // root ∈ lane.source.1} :=
    fun survivor => Classical.choose
      (state.rightSurvivor_literal A strategy hwin basis lane hright direction
        survivor)
  have sourceMember_spec (survivor : raw.RootSurvivor) :
      lane.memberAt survivor.lineage = some (sourceMember survivor) ∧
      code.rightPattern (survivor.lineage, survivor.row)
          direction.rightPivot = true ∧
      survivor.root = profiledOpenIndexedRightChildAnchor A code move direction
        (survivor.lineage, survivor.row) := by
    exact Classical.choose_spec
      (state.rightSurvivor_literal A strategy hwin basis lane hright direction
        survivor)
  have sourceSlot (survivor : raw.RootSurvivor) :
      code.rightSlots survivor.lineage =
        some (.right (sourceMember survivor).1) := by
    simp [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hright,
      ProfiledOpenIndexedRightSemanticShadow.slots,
      (sourceMember_spec survivor).1]
  let entry : raw.RootSurvivor → ProcTwoPairedEntryRep strategy :=
    fun survivor => procTwoViewClassChild strategy lane.realization.entry
      semanticPast direction.rightInput (sourceMember survivor, survivor.row)
  let minimum : raw.RootSurvivor → A.State :=
    fun survivor => procTwoViewClassChildMinimum A lane.realization.entry
      semanticPast (sourceMember survivor, survivor.row)
  let semanticRoot : raw.RootSurvivor → ProfiledOpenLeftRoot A :=
    fun survivor => profiledOpenLeftRootOfWinning A strategy hwin
      (entry survivor) (minimum survivor) basis
  have hclassified (survivor : raw.RootSurvivor) :
      survivor.root = .left (semanticRoot survivor) := by
    calc
      survivor.root = profiledOpenIndexedRightChildAnchor A code move direction
          (survivor.lineage, survivor.row) :=
        (sourceMember_spec survivor).2.2
      _ = profiledOpenIndexedRightChildAnchor A code
          (.right lane.source table, leftMove) direction
          (survivor.lineage, survivor.row) := by rw [hmove]
      _ = .left
          (((profiledOpenRightClassifiedSharedNodeOutput A lane.source table
            (profiledOpenIndexedRightSharedNode A code lane.source
              direction.rightTaggedPast)
            (sourceMember survivor) direction.rightInput).2
            survivor.row).1) :=
        profiledOpenIndexedRightChildAnchor_eq_sharedNodeOutput A code
          lane.source table leftMove direction survivor.lineage survivor.row
          (sourceMember survivor) hvalid (sourceSlot survivor)
      _ = .left (semanticRoot survivor) := by
        apply congrArg ProfiledOpenClassifiedAnchor.left
        exact hroots (sourceMember survivor) survivor.row
  let pivot : raw.RootSurvivor := Classical.choice hsurvivor
  have hpivotMember : ∃ member : {root // root ∈ lane.source.1},
      lane.memberAt direction.rightPivot.1 = some member := by
    apply Option.ne_none_iff_exists'.mp
    intro hmember
    have hpattern := (sourceMember_spec pivot).2.1
    simp [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hright,
      ProfiledOpenIndexedRightSemanticShadow.pattern,
      (sourceMember_spec pivot).1, hmember] at hpattern
  let pivotMember : {root // root ∈ lane.source.1} :=
    Classical.choose hpivotMember
  have pivotMember_at :
      lane.memberAt direction.rightPivot.1 = some pivotMember :=
    Classical.choose_spec hpivotMember
  have hviewToSelectedPivot (survivor : raw.RootSurvivor) :
      currentView Proc.two (entry survivor).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy lane.realization.entry semanticPast
            direction.rightInput
            (pivotMember, direction.rightPivot.2)).rightHistory := by
    apply (hviews (sourceMember survivor, survivor.row)
      (pivotMember, direction.rightPivot.2)).2
    have hpattern := (sourceMember_spec survivor).2.1
    simpa [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hright,
      ProfiledOpenIndexedRightSemanticShadow.pattern,
      (sourceMember_spec survivor).1, pivotMember_at] using hpattern
  have hchildView (survivor : raw.RootSurvivor) :
      currentView Proc.two (entry survivor).rightHistory =
        currentView Proc.two (entry pivot).rightHistory := by
    exact (hviewToSelectedPivot survivor).trans
      (hviewToSelectedPivot pivot).symm
  let childPackage := profiledOpenIndexedLeftSurvivorLanePackage A strategy
    hwin basis raw hsurvivor entry minimum semanticRoot hclassified
    (fun survivor => rfl) pivot hchildView
  have hliteralPattern :
      procTwoEntryOppositeViewPattern strategy entry =
        indexedLineageCanonicalRowPattern raw.RootSurvivor := by
    exact procTwoChildFamily_oppositeViewPattern_eq_canonical strategy
      lane.realization.entry semanticPast direction.rightInput
      (fun survivor => (sourceMember survivor, survivor.row))
      (fun left right =>
        (hchildView left).trans (hchildView right).symm)
  have hchildPattern := childPackage.pattern_eq_canonical A strategy hwin
    basis raw entry minimum hliteralPattern
  let childMember : raw.RootSurvivor →
      {root // root ∈ childPackage.lane.source.1} := fun survivor =>
    Classical.choose (childPackage.literal survivor)
  have childMember_spec (survivor : raw.RootSurvivor) :
      childPackage.lane.memberAt survivor.lineage =
          some (childMember survivor) ∧
        childPackage.lane.realization.entry (childMember survivor) =
          entry survivor ∧
        childPackage.lane.realization.minimum (childMember survivor) =
          minimum survivor :=
    Classical.choose_spec (childPackage.literal survivor)
  refine ⟨{
    semanticPast := semanticPast
    sourceMember := sourceMember
    sourceMember_at := fun survivor => (sourceMember_spec survivor).1
    child := childPackage.lane
    child_slots := ?_
    child_pattern := ?_
    childMember := childMember
    childMember_at := fun survivor => (childMember_spec survivor).1
    memory_step := ?_ }⟩
  · exact childPackage.slots_eq
  · exact hchildPattern
  · intro survivor
    have hstep := pairedStrategyMemory_step_eq_procTwoViewClassChild A
      lane.realization.entry lane.realization.minimum (sourceMember survivor)
      semanticPast direction.rightInput survivor.row
    rw [(childMember_spec survivor).2.1,
      (childMember_spec survivor).2.2]
    exact hstep

/-! ## Left-to-right mirror -/

/-- Complete literal data of one nonempty left-to-right normalized handoff. -/
structure ProfiledOpenIndexedLeftToRightSemanticHandoff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hleft : state.left = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) where
  semanticPast : List (In₁ × In₂)
  sourceMember :
    (profiledOpenIndexedLeftRawChildCode A
      (state.code A strategy hwin basis)
      (state.move A strategy hwin basis) direction).RootSurvivor →
      {root // root ∈ lane.source.1}
  sourceMember_at : ∀ survivor,
    lane.memberAt survivor.lineage = some (sourceMember survivor)
  child : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis (I := I)
  child_slots :
    ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin basis
        (some child) =
      (profiledOpenIndexedLeftChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).rootSlots
  child_pattern :
    ProfiledOpenIndexedRightSemanticShadow.pattern A strategy hwin basis
        (some child) =
      profiledOpenIndexedActiveCanonicalRowPattern A
        (profiledOpenIndexedLeftChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction).rootSlots
  childMember :
    (profiledOpenIndexedLeftRawChildCode A
      (state.code A strategy hwin basis)
      (state.move A strategy hwin basis) direction).RootSurvivor →
      {root // root ∈ child.source.1}
  childMember_at : ∀ survivor,
    child.memberAt survivor.lineage = some (childMember survivor)
  memory_step : ∀ survivor,
    PairedStrategyMemory.step (A := A)
        (.processTwo (lane.realization.entry (sourceMember survivor))
          (lane.realization.minimum (sourceMember survivor)))
        (.fromTwo survivor.row semanticPast direction.leftInput) =
      .processOne (child.realization.entry (childMember survivor))
        (child.realization.minimum (childMember survivor))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- One common shared-node provenance produces a complete literal normalized
left-to-right handoff. -/
theorem exists_profiledOpenIndexedLeftToRightSemanticHandoff
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hleft : state.left = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsurvivor : Nonempty
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    Nonempty (ProfiledOpenIndexedLeftToRightSemanticHandoff A strategy hwin
      basis state lane hleft direction) := by
  classical
  let code := state.code A strategy hwin basis
  let move := state.move A strategy hwin basis
  let raw := profiledOpenIndexedLeftRawChildCode A code move direction
  let table := (lane.realization.coherentTable A).table.toClassified A
    lane.source
  let rightMove := state.right.move A strategy hwin basis
  have hmove : move = (rightMove, .left lane.source table) := by
    simp [move, ProfiledOpenIndexedCorrelatedSemanticState.move, hleft,
      ProfiledOpenIndexedLeftSemanticShadow.move, table, rightMove]
  have hvalid : ProfiledOpenIndexedLeftLaneValid A code.leftSlots
      (.left lane.source table) := by
    have hstateValid := (state.valid A strategy hwin basis).2.1
    change ProfiledOpenIndexedLeftLaneValid A code.leftSlots move.2 at hstateValid
    rw [hmove] at hstateValid
    exact hstateValid
  rcases exists_profiledOpenLeftClassifiedSharedNode_correlatedStep A
      lane.realization
      (profiledOpenIndexedLeftSharedNode A code lane.source
        direction.leftTaggedPast)
      direction.leftInput with ⟨taggedPast, hroots, hviews⟩
  let semanticPast := taggedPast.map fun old => (old.1.2, old.2)
  let sourceMember : raw.RootSurvivor → {root // root ∈ lane.source.1} :=
    fun survivor => Classical.choose
      (state.leftSurvivor_literal A strategy hwin basis lane hleft direction
        survivor)
  have sourceMember_spec (survivor : raw.RootSurvivor) :
      lane.memberAt survivor.lineage = some (sourceMember survivor) ∧
      code.leftPattern (survivor.lineage, survivor.row)
          direction.leftPivot = true ∧
      survivor.root = profiledOpenIndexedLeftChildAnchor A code move direction
        (survivor.lineage, survivor.row) := by
    exact Classical.choose_spec
      (state.leftSurvivor_literal A strategy hwin basis lane hleft direction
        survivor)
  have sourceSlot (survivor : raw.RootSurvivor) :
      code.leftSlots survivor.lineage =
        some (.left (sourceMember survivor).1) := by
    simp [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hleft,
      ProfiledOpenIndexedLeftSemanticShadow.slots,
      (sourceMember_spec survivor).1]
  let entry : raw.RootSurvivor → ProcOnePairedEntryRep strategy :=
    fun survivor => procOneViewClassChild strategy lane.realization.entry
      semanticPast direction.leftInput (sourceMember survivor, survivor.row)
  let minimum : raw.RootSurvivor → A.State :=
    fun survivor => procOneViewClassChildMinimum A lane.realization.entry
      semanticPast (sourceMember survivor, survivor.row)
  let semanticRoot : raw.RootSurvivor → ProfiledOpenRightRoot A :=
    fun survivor => profiledOpenRightRootOfWinning A strategy hwin
      (entry survivor) (minimum survivor) basis
  have hclassified (survivor : raw.RootSurvivor) :
      survivor.root = .right (semanticRoot survivor) := by
    calc
      survivor.root = profiledOpenIndexedLeftChildAnchor A code move direction
          (survivor.lineage, survivor.row) :=
        (sourceMember_spec survivor).2.2
      _ = profiledOpenIndexedLeftChildAnchor A code
          (rightMove, .left lane.source table) direction
          (survivor.lineage, survivor.row) := by rw [hmove]
      _ = .right
          (((profiledOpenLeftClassifiedSharedNodeOutput A lane.source table
            (profiledOpenIndexedLeftSharedNode A code lane.source
              direction.leftTaggedPast)
            (sourceMember survivor) direction.leftInput).2
            survivor.row).1) :=
        profiledOpenIndexedLeftChildAnchor_eq_sharedNodeOutput A code
          rightMove lane.source table direction survivor.lineage survivor.row
          (sourceMember survivor) hvalid (sourceSlot survivor)
      _ = .right (semanticRoot survivor) := by
        apply congrArg ProfiledOpenClassifiedAnchor.right
        exact hroots (sourceMember survivor) survivor.row
  let pivot : raw.RootSurvivor := Classical.choice hsurvivor
  have hpivotMember : ∃ member : {root // root ∈ lane.source.1},
      lane.memberAt direction.leftPivot.1 = some member := by
    apply Option.ne_none_iff_exists'.mp
    intro hmember
    have hpattern := (sourceMember_spec pivot).2.1
    simp [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hleft,
      ProfiledOpenIndexedLeftSemanticShadow.pattern,
      (sourceMember_spec pivot).1, hmember] at hpattern
  let pivotMember : {root // root ∈ lane.source.1} :=
    Classical.choose hpivotMember
  have pivotMember_at :
      lane.memberAt direction.leftPivot.1 = some pivotMember :=
    Classical.choose_spec hpivotMember
  have hviewToSelectedPivot (survivor : raw.RootSurvivor) :
      currentView Proc.one (entry survivor).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy lane.realization.entry semanticPast
            direction.leftInput
            (pivotMember, direction.leftPivot.2)).leftHistory := by
    apply (hviews (sourceMember survivor, survivor.row)
      (pivotMember, direction.leftPivot.2)).2
    have hpattern := (sourceMember_spec survivor).2.1
    simpa [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hleft,
      ProfiledOpenIndexedLeftSemanticShadow.pattern,
      (sourceMember_spec survivor).1, pivotMember_at] using hpattern
  have hchildView (survivor : raw.RootSurvivor) :
      currentView Proc.one (entry survivor).leftHistory =
        currentView Proc.one (entry pivot).leftHistory := by
    exact (hviewToSelectedPivot survivor).trans
      (hviewToSelectedPivot pivot).symm
  let childPackage := profiledOpenIndexedRightSurvivorLanePackage A strategy
    hwin basis raw hsurvivor entry minimum semanticRoot hclassified
    (fun survivor => rfl) pivot hchildView
  have hliteralPattern :
      procOneEntryOppositeViewPattern strategy entry =
        indexedLineageCanonicalRowPattern raw.RootSurvivor := by
    exact procOneChildFamily_oppositeViewPattern_eq_canonical strategy
      lane.realization.entry semanticPast direction.leftInput
      (fun survivor => (sourceMember survivor, survivor.row))
      (fun left right =>
        (hchildView left).trans (hchildView right).symm)
  have hchildPattern := childPackage.pattern_eq_canonical A strategy hwin
    basis raw entry minimum hliteralPattern
  let childMember : raw.RootSurvivor →
      {root // root ∈ childPackage.lane.source.1} := fun survivor =>
    Classical.choose (childPackage.literal survivor)
  have childMember_spec (survivor : raw.RootSurvivor) :
      childPackage.lane.memberAt survivor.lineage =
          some (childMember survivor) ∧
        childPackage.lane.realization.entry (childMember survivor) =
          entry survivor ∧
        childPackage.lane.realization.minimum (childMember survivor) =
          minimum survivor :=
    Classical.choose_spec (childPackage.literal survivor)
  refine ⟨{
    semanticPast := semanticPast
    sourceMember := sourceMember
    sourceMember_at := fun survivor => (sourceMember_spec survivor).1
    child := childPackage.lane
    child_slots := ?_
    child_pattern := ?_
    childMember := childMember
    childMember_at := fun survivor => (childMember_spec survivor).1
    memory_step := ?_ }⟩
  · exact childPackage.slots_eq
  · exact hchildPattern
  · intro survivor
    have hstep := pairedStrategyMemory_step_eq_procOneViewClassChild A
      lane.realization.entry lane.realization.minimum (sourceMember survivor)
      semanticPast direction.leftInput survivor.row
    rw [(childMember_spec survivor).2.1,
      (childMember_spec survivor).2.2]
    exact hstep

end

end DetParityAutomaton

end DistributedSynthesis
