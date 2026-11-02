/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedLineage

/-!
# Canonical root deduplication for persistent lineages

Several semantic candidates may produce the same finite successor root while
retaining different literal histories.  A finite family realization has one
representative per root, so allowing all such candidates to remain live would
permit a later representative switch.  This file gives the source-free
normalization used to avoid that splice: for every occurring root it keeps
one classically chosen lineage and makes all duplicate lineages inactive.

The normalization preserves exactly the set of occurring roots, never
resurrects an absent lineage, and makes the live root slots injective.  The
choice is proof-side finite data; it is not an observation of either process.
-/

namespace DistributedSynthesis

universe i r

namespace DetParityAutomaton

/-- A finite child root occurs in at least one persistent lineage slot. -/
def IndexedLineageChildCode.RootOccurs
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (root : Root) : Prop :=
  ∃ lineage row, code lineage = some (row, root)

/-- One fixed representative lineage when the root occurs, and `none`
otherwise.  The optional form makes the operation total even when `I` is
empty. -/
noncomputable def IndexedLineageChildCode.rootRepresentative?
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (root : Root) : Option I := by
  classical
  exact if hoccurs : code.RootOccurs root then
    some (Classical.choose hoccurs)
  else none

theorem IndexedLineageChildCode.rootRepresentative?_eq_some
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (root : Root) (hoccurs : code.RootOccurs root) :
    ∃ representative row,
      code.rootRepresentative? root = some representative ∧
        code representative = some (row, root) := by
  classical
  refine ⟨Classical.choose hoccurs, Classical.choose (Classical.choose_spec
    hoccurs), ?_, Classical.choose_spec (Classical.choose_spec hoccurs)⟩
  simp [IndexedLineageChildCode.rootRepresentative?, hoccurs]

/-- Retain exactly one lineage for every occurring finite root. -/
noncomputable def IndexedLineageChildCode.deduplicateRoots
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root) :
    IndexedLineageChildCode I Root := by
  classical
  intro lineage
  exact match code lineage with
    | none => none
    | some value =>
        if code.rootRepresentative? value.2 = some lineage then
          some value
        else none

/-- An absent lineage remains absent under root deduplication. -/
@[simp] theorem IndexedLineageChildCode.deduplicateRoots_none_of_none
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (lineage : I) (hnone : code lineage = none) :
    code.deduplicateRoots lineage = none := by
  classical
  simp [IndexedLineageChildCode.deduplicateRoots, hnone]

/-- Every retained slot is literally an old slot. -/
theorem IndexedLineageChildCode.eq_of_deduplicateRoots_eq_some
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (lineage : I) (row : PairedEntryRow) (root : Root)
    (hslot : code.deduplicateRoots lineage = some (row, root)) :
    code lineage = some (row, root) := by
  classical
  cases hvalue : code lineage with
  | none =>
      simp [IndexedLineageChildCode.deduplicateRoots, hvalue] at hslot
  | some value =>
      simp only [IndexedLineageChildCode.deduplicateRoots, hvalue] at hslot
      split at hslot
      · have : value = (row, root) := Option.some.inj hslot
        simpa [this] using hvalue
      · contradiction

/-- Exact survivor equation: a slot is retained precisely when it is the
chosen representative of its finite root. -/
theorem IndexedLineageChildCode.deduplicateRoots_eq_some_iff
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (lineage : I) (row : PairedEntryRow) (root : Root) :
    code.deduplicateRoots lineage = some (row, root) ↔
      code lineage = some (row, root) ∧
        code.rootRepresentative? root = some lineage := by
  classical
  constructor
  · intro hslot
    have hold := code.eq_of_deduplicateRoots_eq_some lineage row root hslot
    refine ⟨hold, ?_⟩
    simpa [IndexedLineageChildCode.deduplicateRoots, hold] using hslot
  · rintro ⟨hold, hrepresentative⟩
    simp [IndexedLineageChildCode.deduplicateRoots, hold, hrepresentative]

/-- Forgetting rows, a root occurs exactly when it is present in some root
slot. -/
theorem IndexedLineageChildCode.rootSlots_eq_some_iff
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (lineage : I) (root : Root) :
    code.rootSlots lineage = some root ↔
      ∃ row, code lineage = some (row, root) := by
  cases hslot : code lineage with
  | none => simp [IndexedLineageChildCode.rootSlots, hslot]
  | some value =>
      rcases value with ⟨row, valueRoot⟩
      simp [IndexedLineageChildCode.rootSlots, hslot]

/-- Every old root still occurs after deduplication, at its chosen
representative lineage. -/
theorem IndexedLineageChildCode.rootOccurs_deduplicateRoots
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (root : Root) (hoccurs : code.RootOccurs root) :
    code.deduplicateRoots.RootOccurs root := by
  classical
  rcases code.rootRepresentative?_eq_some root hoccurs with
    ⟨representative, row, hrepresentative, hrow⟩
  refine ⟨representative, row, ?_⟩
  simp [IndexedLineageChildCode.deduplicateRoots, hrow, hrepresentative]

/-- Deduplication preserves root occurrence in both directions. -/
theorem IndexedLineageChildCode.rootOccurs_deduplicateRoots_iff
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (root : Root) :
    code.deduplicateRoots.RootOccurs root ↔ code.RootOccurs root := by
  constructor
  · rintro ⟨lineage, row, hslot⟩
    exact ⟨lineage, row,
      code.eq_of_deduplicateRoots_eq_some lineage row root hslot⟩
  · exact code.rootOccurs_deduplicateRoots root

/-- Root occurrence can equivalently be stated on the root-slot projection. -/
theorem IndexedLineageChildCode.exists_rootSlots_eq_some_iff_rootOccurs
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (root : Root) :
    (∃ lineage, code.rootSlots lineage = some root) ↔ code.RootOccurs root := by
  constructor
  · rintro ⟨lineage, hslot⟩
    cases hcode : code lineage with
    | none => simp [IndexedLineageChildCode.rootSlots, hcode] at hslot
    | some value =>
        rcases value with ⟨row, valueRoot⟩
        have hroot : valueRoot = root := by
          simpa [IndexedLineageChildCode.rootSlots, hcode] using hslot
        subst valueRoot
        exact ⟨lineage, row, hcode⟩
  · rintro ⟨lineage, row, hcode⟩
    exact ⟨lineage, by simp [IndexedLineageChildCode.rootSlots, hcode]⟩

/-- Deduplication preserves exactly the roots occurring in projected slots. -/
theorem IndexedLineageChildCode.exists_deduplicateRoots_rootSlots_iff
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    (root : Root) :
    (∃ lineage, code.deduplicateRoots.rootSlots lineage = some root) ↔
      ∃ lineage, code.rootSlots lineage = some root := by
  rw [code.deduplicateRoots.exists_rootSlots_eq_some_iff_rootOccurs,
    code.exists_rootSlots_eq_some_iff_rootOccurs,
    code.rootOccurs_deduplicateRoots_iff]

/-- At most one retained lineage carries any fixed root. -/
theorem IndexedLineageChildCode.deduplicateRoots_lineage_unique
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    {left right : I} {leftRow rightRow : PairedEntryRow} {root : Root}
    (hleft : code.deduplicateRoots left = some (leftRow, root))
    (hright : code.deduplicateRoots right = some (rightRow, root)) :
    left = right := by
  classical
  have hleftOld := code.eq_of_deduplicateRoots_eq_some left leftRow root hleft
  have hrightOld := code.eq_of_deduplicateRoots_eq_some right rightRow root hright
  have hleftRep : code.rootRepresentative? root = some left := by
    simp only [IndexedLineageChildCode.deduplicateRoots, hleftOld] at hleft
    split at hleft
    · assumption
    · contradiction
  have hrightRep : code.rootRepresentative? root = some right := by
    simp only [IndexedLineageChildCode.deduplicateRoots, hrightOld] at hright
    split at hright
    · assumption
    · contradiction
  exact Option.some.inj (hleftRep.symm.trans hrightRep)

/-- The retained root slots are injective on their active carrier. -/
theorem IndexedLineageChildCode.deduplicateRoots_rootSlots_injective
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root)
    {left right : I} {root : Root}
    (hleft : code.deduplicateRoots.rootSlots left = some root)
    (hright : code.deduplicateRoots.rootSlots right = some root) :
    left = right := by
  rw [code.deduplicateRoots.rootSlots_eq_some_iff] at hleft hright
  rcases hleft with ⟨leftRow, hleft⟩
  rcases hright with ⟨rightRow, hright⟩
  exact code.deduplicateRoots_lineage_unique hleft hright

end DetParityAutomaton

end DistributedSynthesis
