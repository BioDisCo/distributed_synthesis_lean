/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSharedNodeMapping

/-!
# Extensional API for the indexed shared-node successor

The total indexed successor is deliberately defensive: malformed moves,
absent pivots, and absent members are sent to the inactive lane.  Semantic
closure, however, always applies it at a valid lane and an active pivot.
This file packages that active case into equations which expose exactly one
shared family-controller query and one finite equality-pattern test.

These are proof APIs only.  The source member, pivot row, and persistent
lineage remain hidden coordinates and are not exposed to either process.
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

/-! ## The generic active gate -/

section
omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂]

/-- On an active pivot and active member, the defensive materializer is
exactly the ordinary pattern materializer. -/
theorem profiledOpenIndexedGatedChildCode_eq_of_active
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → ProfiledOpenClassifiedAnchor A)
    (pivot : IndexedLineageCandidate I) (member : I)
    (hpivot : slots pivot.1 ≠ none) (hmember : slots member ≠ none) :
    profiledOpenIndexedGatedChildCode A slots pattern root pivot member =
      indexedLineageChildCodeOfPattern pattern root pivot member := by
  cases hpivotSlot : slots pivot.1 with
  | none => exact (hpivot hpivotSlot).elim
  | some pivotRoot =>
      cases hmemberSlot : slots member with
      | none => exact (hmember hmemberSlot).elim
      | some memberRoot =>
          simp [profiledOpenIndexedGatedChildCode, hpivotSlot, hmemberSlot]

/-- Consequently the active gated code has the same exact membership law as
the source-free pattern materializer. -/
theorem profiledOpenIndexedGatedChildCode_eq_some_iff_of_active
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → ProfiledOpenClassifiedAnchor A)
    (pivot : IndexedLineageCandidate I)
    (hfunctional : pattern.RowFunctionalAt pivot)
    (member : I) (row : PairedEntryRow)
    (hpivot : slots pivot.1 ≠ none) (hmember : slots member ≠ none) :
    profiledOpenIndexedGatedChildCode A slots pattern root pivot member =
        some (row, root (member, row)) ↔
      pattern (member, row) pivot = true := by
  rw [profiledOpenIndexedGatedChildCode_eq_of_active A slots pattern root
    pivot member hpivot hmember]
  exact indexedLineageChildCodeOfPattern_eq_some_iff pattern root pivot
    hfunctional member row

/-- Eliminate an arbitrary active `some`: its row satisfies the pattern and
its root is the root function evaluated at that very candidate. -/
theorem profiledOpenIndexedGatedChildCode_eq_some_elim_of_active
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → ProfiledOpenClassifiedAnchor A)
    (pivot : IndexedLineageCandidate I) (member : I)
    (row : PairedEntryRow) (result : ProfiledOpenClassifiedAnchor A)
    (hpivot : slots pivot.1 ≠ none) (hmember : slots member ≠ none)
    (hcode : profiledOpenIndexedGatedChildCode A slots pattern root pivot
      member = some (row, result)) :
    pattern (member, row) pivot = true ∧
      result = root (member, row) := by
  rw [profiledOpenIndexedGatedChildCode_eq_of_active A slots pattern root
    pivot member hpivot hmember] at hcode
  cases row with
  | first =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · have hcode' :
            some (PairedEntryRow.first,
              root (member, PairedEntryRow.first)) =
              some (PairedEntryRow.first, result) := by
          simpa [indexedLineageChildCodeOfPattern, hfirst] using hcode
        exact ⟨hfirst,
          (congrArg Prod.snd (Option.some.inj hcode')).symm⟩
      · simp [indexedLineageChildCodeOfPattern, hfirst] at hcode
  | both =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · simp [indexedLineageChildCodeOfPattern, hfirst] at hcode
      · by_cases hboth : pattern (member, .both) pivot = true
        · have hcode' :
              some (PairedEntryRow.both,
                root (member, PairedEntryRow.both)) =
                some (PairedEntryRow.both, result) := by
            simpa [indexedLineageChildCodeOfPattern, hfirst, hboth] using hcode
          exact ⟨hboth,
            (congrArg Prod.snd (Option.some.inj hcode')).symm⟩
        · simp [indexedLineageChildCodeOfPattern, hfirst, hboth] at hcode

end

/-! ## Exact active shared-node queries -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At a valid active right lane, the total child-anchor function is exactly
the selected row of the complete response table at the one shared decoded
node.  The explicit source member avoids all proof-term dependence in the
subtype tag. -/
theorem profiledOpenIndexedRightChildAnchor_eq_sharedNodeOutput
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (leftMove : ProfiledOpenClassifiedMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (hvalid : ProfiledOpenIndexedRightLaneValid A code.rightSlots
      (.right source table))
    (hslot : code.rightSlots lineage = some (.right member.1)) :
    profiledOpenIndexedRightChildAnchor A code
        (.right source table, leftMove) direction (lineage, row) =
      .left
        (((profiledOpenRightClassifiedSharedNodeOutput A source table
          (profiledOpenIndexedRightSharedNode A code source
            direction.rightTaggedPast)
          member direction.rightInput).2 row).1) := by
  classical
  have hmem : member.1 ∈ source.1 := member.2
  have hdecoded :
      profiledOpenIndexedRightSourceMember A code source lineage = member := by
    apply Subtype.ext
    exact profiledOpenIndexedRightSourceMember_val_of_laneValid A code source
      table lineage member.1 hvalid hslot
  simp only [profiledOpenIndexedRightChildAnchor, hslot, hmem, dif_pos]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right mirror of the exact active shared-node query. -/
theorem profiledOpenIndexedLeftChildAnchor_eq_sharedNodeOutput
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (rightMove : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (hvalid : ProfiledOpenIndexedLeftLaneValid A code.leftSlots
      (.left source table))
    (hslot : code.leftSlots lineage = some (.left member.1)) :
    profiledOpenIndexedLeftChildAnchor A code
        (rightMove, .left source table) direction (lineage, row) =
      .right
        (((profiledOpenLeftClassifiedSharedNodeOutput A source table
          (profiledOpenIndexedLeftSharedNode A code source
            direction.leftTaggedPast)
          member direction.leftInput).2 row).1) := by
  classical
  have hmem : member.1 ∈ source.1 := member.2
  have hdecoded :
      profiledOpenIndexedLeftSourceMember A code source lineage = member := by
    apply Subtype.ext
    exact profiledOpenIndexedLeftSourceMember_val_of_laneValid A code source
      table lineage member.1 hvalid hslot
  simp only [profiledOpenIndexedLeftChildAnchor, hslot, hmem, dif_pos]

/-! ## Active child-code membership -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- One active right lineage contributes exactly the row selected by the
stored equality pattern, and its root is exactly the shared table output. -/
theorem profiledOpenIndexedRightRawChildCode_eq_some_iff
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (leftMove : ProfiledOpenClassifiedMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (hvalid : ProfiledOpenIndexedRightLaneValid A code.rightSlots
      (.right source table))
    (hpivot : code.rightSlots direction.rightPivot.1 ≠ none)
    (hslot : code.rightSlots lineage = some (.right member.1))
    (hfunctional : code.rightPattern.RowFunctionalAt direction.rightPivot) :
    profiledOpenIndexedRightRawChildCode A code
          (.right source table, leftMove) direction lineage =
        some (row, .left
          (((profiledOpenRightClassifiedSharedNodeOutput A source table
            (profiledOpenIndexedRightSharedNode A code source
              direction.rightTaggedPast)
            member direction.rightInput).2 row).1)) ↔
      code.rightPattern (lineage, row) direction.rightPivot = true := by
  have hmember : code.rightSlots lineage ≠ none := by
    rw [hslot]
    simp
  rw [show profiledOpenIndexedRightRawChildCode A code
      (.right source table, leftMove) direction lineage =
      profiledOpenIndexedGatedChildCode A code.rightSlots code.rightPattern
        (profiledOpenIndexedRightChildAnchor A code
          (.right source table, leftMove) direction)
        direction.rightPivot lineage from rfl]
  rw [← profiledOpenIndexedRightChildAnchor_eq_sharedNodeOutput A code source
    table leftMove direction lineage row member hvalid hslot]
  exact profiledOpenIndexedGatedChildCode_eq_some_iff_of_active A
    code.rightSlots code.rightPattern
    (profiledOpenIndexedRightChildAnchor A code
      (.right source table, leftMove) direction)
    direction.rightPivot hfunctional lineage row hpivot hmember

/-- Left active child-code membership mirror. -/
theorem profiledOpenIndexedLeftRawChildCode_eq_some_iff
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (rightMove : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (hvalid : ProfiledOpenIndexedLeftLaneValid A code.leftSlots
      (.left source table))
    (hpivot : code.leftSlots direction.leftPivot.1 ≠ none)
    (hslot : code.leftSlots lineage = some (.left member.1))
    (hfunctional : code.leftPattern.RowFunctionalAt direction.leftPivot) :
    profiledOpenIndexedLeftRawChildCode A code
          (rightMove, .left source table) direction lineage =
        some (row, .right
          (((profiledOpenLeftClassifiedSharedNodeOutput A source table
            (profiledOpenIndexedLeftSharedNode A code source
              direction.leftTaggedPast)
            member direction.leftInput).2 row).1)) ↔
      code.leftPattern (lineage, row) direction.leftPivot = true := by
  have hmember : code.leftSlots lineage ≠ none := by
    rw [hslot]
    simp
  rw [show profiledOpenIndexedLeftRawChildCode A code
      (rightMove, .left source table) direction lineage =
      profiledOpenIndexedGatedChildCode A code.leftSlots code.leftPattern
        (profiledOpenIndexedLeftChildAnchor A code
          (rightMove, .left source table) direction)
        direction.leftPivot lineage from rfl]
  rw [← profiledOpenIndexedLeftChildAnchor_eq_sharedNodeOutput A code
    rightMove source table direction lineage row member hvalid hslot]
  exact profiledOpenIndexedGatedChildCode_eq_some_iff_of_active A
    code.leftSlots code.leftPattern
    (profiledOpenIndexedLeftChildAnchor A code
      (rightMove, .left source table) direction)
    direction.leftPivot hfunctional lineage row hpivot hmember

/-- Eliminate an arbitrary active right raw-child entry.  Besides exposing
the equality-pattern test, this identifies the returned root with the exact
row of the single shared-node table query.  This formulation is convenient
for semantic closure, where the target root is learned from an existing
`some` equation rather than chosen in advance. -/
theorem profiledOpenIndexedRightRawChildCode_eq_some_elim
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (leftMove : ProfiledOpenClassifiedMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (result : ProfiledOpenClassifiedAnchor A)
    (hvalid : ProfiledOpenIndexedRightLaneValid A code.rightSlots
      (.right source table))
    (hpivot : code.rightSlots direction.rightPivot.1 ≠ none)
    (hslot : code.rightSlots lineage = some (.right member.1))
    (hraw : profiledOpenIndexedRightRawChildCode A code
      (.right source table, leftMove) direction lineage =
        some (row, result)) :
    code.rightPattern (lineage, row) direction.rightPivot = true ∧
      result = .left
        (((profiledOpenRightClassifiedSharedNodeOutput A source table
          (profiledOpenIndexedRightSharedNode A code source
            direction.rightTaggedPast)
          member direction.rightInput).2 row).1) := by
  have hmember : code.rightSlots lineage ≠ none := by
    rw [hslot]
    simp
  have helim := profiledOpenIndexedGatedChildCode_eq_some_elim_of_active A
    code.rightSlots code.rightPattern
    (profiledOpenIndexedRightChildAnchor A code
      (.right source table, leftMove) direction)
    direction.rightPivot lineage row result hpivot hmember (by
      simpa only [profiledOpenIndexedRightRawChildCode] using hraw)
  refine ⟨helim.1, helim.2.trans ?_⟩
  exact profiledOpenIndexedRightChildAnchor_eq_sharedNodeOutput A code source
    table leftMove direction lineage row member hvalid hslot

/-- Left-to-right mirror of arbitrary raw-child elimination. -/
theorem profiledOpenIndexedLeftRawChildCode_eq_some_elim
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (rightMove : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (result : ProfiledOpenClassifiedAnchor A)
    (hvalid : ProfiledOpenIndexedLeftLaneValid A code.leftSlots
      (.left source table))
    (hpivot : code.leftSlots direction.leftPivot.1 ≠ none)
    (hslot : code.leftSlots lineage = some (.left member.1))
    (hraw : profiledOpenIndexedLeftRawChildCode A code
      (rightMove, .left source table) direction lineage =
        some (row, result)) :
    code.leftPattern (lineage, row) direction.leftPivot = true ∧
      result = .right
        (((profiledOpenLeftClassifiedSharedNodeOutput A source table
          (profiledOpenIndexedLeftSharedNode A code source
            direction.leftTaggedPast)
          member direction.leftInput).2 row).1) := by
  have hmember : code.leftSlots lineage ≠ none := by
    rw [hslot]
    simp
  have helim := profiledOpenIndexedGatedChildCode_eq_some_elim_of_active A
    code.leftSlots code.leftPattern
    (profiledOpenIndexedLeftChildAnchor A code
      (rightMove, .left source table) direction)
    direction.leftPivot lineage row result hpivot hmember (by
      simpa only [profiledOpenIndexedLeftRawChildCode] using hraw)
  refine ⟨helim.1, helim.2.trans ?_⟩
  exact profiledOpenIndexedLeftChildAnchor_eq_sharedNodeOutput A code
    rightMove source table direction lineage row member hvalid hslot

end

/-! ## Canonical normalized survivors -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The public right child code retains the raw pattern-selected candidate
exactly when its lineage is the canonical representative of the emitted
finite root. -/
theorem profiledOpenIndexedRightChildCode_eq_some_iff
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (leftMove : ProfiledOpenClassifiedMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (hvalid : ProfiledOpenIndexedRightLaneValid A code.rightSlots
      (.right source table))
    (hpivot : code.rightSlots direction.rightPivot.1 ≠ none)
    (hslot : code.rightSlots lineage = some (.right member.1))
    (hfunctional : code.rightPattern.RowFunctionalAt direction.rightPivot) :
    let target : ProfiledOpenClassifiedAnchor A := .left
      (((profiledOpenRightClassifiedSharedNodeOutput A source table
        (profiledOpenIndexedRightSharedNode A code source
          direction.rightTaggedPast)
        member direction.rightInput).2 row).1)
    profiledOpenIndexedRightChildCode A code
          (.right source table, leftMove) direction lineage =
        some (row, target) ↔
      code.rightPattern (lineage, row) direction.rightPivot = true ∧
        (profiledOpenIndexedRightRawChildCode A code
          (.right source table, leftMove) direction).rootRepresentative?
            target = some lineage := by
  dsimp only
  rw [profiledOpenIndexedRightChildCode,
    IndexedLineageChildCode.deduplicateRoots_eq_some_iff]
  rw [profiledOpenIndexedRightRawChildCode_eq_some_iff A code source table
    leftMove direction lineage row member hvalid hpivot hslot hfunctional]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Normalized left survivor equation. -/
theorem profiledOpenIndexedLeftChildCode_eq_some_iff
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (rightMove : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (member : {root // root ∈ source.1})
    (hvalid : ProfiledOpenIndexedLeftLaneValid A code.leftSlots
      (.left source table))
    (hpivot : code.leftSlots direction.leftPivot.1 ≠ none)
    (hslot : code.leftSlots lineage = some (.left member.1))
    (hfunctional : code.leftPattern.RowFunctionalAt direction.leftPivot) :
    let target : ProfiledOpenClassifiedAnchor A := .right
      (((profiledOpenLeftClassifiedSharedNodeOutput A source table
        (profiledOpenIndexedLeftSharedNode A code source
          direction.leftTaggedPast)
        member direction.leftInput).2 row).1)
    profiledOpenIndexedLeftChildCode A code
          (rightMove, .left source table) direction lineage =
        some (row, target) ↔
      code.leftPattern (lineage, row) direction.leftPivot = true ∧
        (profiledOpenIndexedLeftRawChildCode A code
          (rightMove, .left source table) direction).rootRepresentative?
            target = some lineage := by
  dsimp only
  rw [profiledOpenIndexedLeftChildCode,
    IndexedLineageChildCode.deduplicateRoots_eq_some_iff]
  rw [profiledOpenIndexedLeftRawChildCode_eq_some_iff A code rightMove source
    table direction lineage row member hvalid hpivot hslot hfunctional]

/-! ## Root-set preservation and active injectivity -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Membership in the unordered public slot-root set is generic root
occurrence in the ordered child code. -/
theorem mem_profiledOpenIndexedSlotRoots_rootSlots_iff
    (child : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (root : ProfiledOpenClassifiedAnchor A) :
    root ∈ profiledOpenIndexedSlotRoots A child.rootSlots ↔
      child.RootOccurs root := by
  rw [← child.exists_rootSlots_eq_some_iff_rootOccurs]
  constructor
  · intro hroot
    simp only [profiledOpenIndexedSlotRoots, Finset.mem_biUnion,
      Finset.mem_univ, true_and] at hroot
    rcases hroot with ⟨lineage, hroot⟩
    cases hslot : child.rootSlots lineage with
    | none => simp [hslot] at hroot
    | some value =>
        have hreverse : root = value := by simpa [hslot] using hroot
        have hvalue : value = root := hreverse.symm
        subst value
        exact ⟨lineage, hslot⟩
  · rintro ⟨lineage, hslot⟩
    simp only [profiledOpenIndexedSlotRoots, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    refine ⟨lineage, ?_⟩
    simp [hslot]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Root normalization changes only the surviving lineage, not the finite
set of roots represented by the lane. -/
theorem profiledOpenIndexedSlotRoots_deduplicateRoots_rootSlots
    (child : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A)) :
    profiledOpenIndexedSlotRoots A child.deduplicateRoots.rootSlots =
      profiledOpenIndexedSlotRoots A child.rootSlots := by
  classical
  ext root
  rw [mem_profiledOpenIndexedSlotRoots_rootSlots_iff A,
    mem_profiledOpenIndexedSlotRoots_rootSlots_iff A,
    child.rootOccurs_deduplicateRoots_iff]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The normalized right child carries exactly the raw child root set. -/
theorem profiledOpenIndexedRightChildCode_slotRoots_eq_raw
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedSlotRoots A
        (profiledOpenIndexedRightChildCode A code move direction).rootSlots =
      profiledOpenIndexedSlotRoots A
        (profiledOpenIndexedRightRawChildCode A code move direction).rootSlots := by
  exact profiledOpenIndexedSlotRoots_deduplicateRoots_rootSlots A
    (profiledOpenIndexedRightRawChildCode A code move direction)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left root-set preservation mirror. -/
theorem profiledOpenIndexedLeftChildCode_slotRoots_eq_raw
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedSlotRoots A
        (profiledOpenIndexedLeftChildCode A code move direction).rootSlots =
      profiledOpenIndexedSlotRoots A
        (profiledOpenIndexedLeftRawChildCode A code move direction).rootSlots := by
  exact profiledOpenIndexedSlotRoots_deduplicateRoots_rootSlots A
    (profiledOpenIndexedLeftRawChildCode A code move direction)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Equal active roots in the normalized right child have the same persistent
lineage. -/
theorem profiledOpenIndexedRightChildCode_rootSlots_injective
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    {left right : I} {root : ProfiledOpenClassifiedAnchor A}
    (hleft : (profiledOpenIndexedRightChildCode A code move direction).rootSlots
      left = some root)
    (hright : (profiledOpenIndexedRightChildCode A code move direction).rootSlots
      right = some root) :
    left = right := by
  exact (profiledOpenIndexedRightRawChildCode A code move direction)
    |>.deduplicateRoots_rootSlots_injective hleft hright

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left active-root injectivity mirror. -/
theorem profiledOpenIndexedLeftChildCode_rootSlots_injective
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    {left right : I} {root : ProfiledOpenClassifiedAnchor A}
    (hleft : (profiledOpenIndexedLeftChildCode A code move direction).rootSlots
      left = some root)
    (hright : (profiledOpenIndexedLeftChildCode A code move direction).rootSlots
      right = some root) :
    left = right := by
  exact (profiledOpenIndexedLeftRawChildCode A code move direction)
    |>.deduplicateRoots_rootSlots_injective hleft hright

end

end DetParityAutomaton

end DistributedSynthesis
