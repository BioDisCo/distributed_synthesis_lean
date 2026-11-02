/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemIndexedLineageRootDeduplication

/-!
# The literal survivor family of a deduplicated lineage code

Root deduplication is consumed semantically through the subtype of slots
which actually survive.  Its root projection is injective: hence a canonical
finite realization indexed by these survivors must choose the literal
history attached to that survivor, rather than another history with the same
finite root.
-/

namespace DistributedSynthesis

universe i r

namespace DetParityAutomaton

noncomputable section

/-- Invert a materialized pattern slot without knowing its root in advance.
The selected row really belongs to the pivot class, and the stored root is
the root function at that exact candidate. -/
theorem indexedLineageChildCodeOfPattern_eq_some_elim
    {I : Type i} {Root : Type r}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I) (lineage : I)
    (row : PairedEntryRow) (stored : Root)
    (hslot : indexedLineageChildCodeOfPattern pattern root pivot lineage =
      some (row, stored)) :
    pattern (lineage, row) pivot = true ∧
      stored = root (lineage, row) := by
  cases row with
  | first =>
      by_cases hfirst : pattern (lineage, .first) pivot = true
      · simp [indexedLineageChildCodeOfPattern, hfirst] at hslot
        exact ⟨hfirst, hslot.symm⟩
      · simp [indexedLineageChildCodeOfPattern, hfirst] at hslot
  | both =>
      by_cases hfirst : pattern (lineage, .first) pivot = true
      · simp [indexedLineageChildCodeOfPattern, hfirst] at hslot
      · by_cases hboth : pattern (lineage, .both) pivot = true
        · simp [indexedLineageChildCodeOfPattern, hfirst, hboth] at hslot
          exact ⟨hboth, hslot.symm⟩
        · simp [indexedLineageChildCodeOfPattern, hfirst, hboth] at hslot

/-- A literal slot retained by root deduplication. -/
def IndexedLineageChildCode.RootSurvivor
    {I : Type i} {Root : Type r} (code : IndexedLineageChildCode I Root) :=
  { value : I × (PairedEntryRow × Root) //
    code.deduplicateRoots value.1 = some value.2 }

namespace IndexedLineageChildCode.RootSurvivor

variable {I : Type i} {Root : Type r}
variable {code : IndexedLineageChildCode I Root}

noncomputable instance [Fintype I] [Fintype Root] :
    Fintype code.RootSurvivor := by
  classical
  exact Fintype.ofInjective
    (fun survivor : code.RootSurvivor => survivor.1)
    (fun _ _ h => Subtype.ext h)

/-- Persistent lineage of a surviving slot. -/
def lineage (survivor : code.RootSurvivor) : I := survivor.1.1

/-- The selected row retained at the lineage. -/
def row (survivor : code.RootSurvivor) : PairedEntryRow := survivor.1.2.1

/-- Finite root retained at the lineage. -/
def root (survivor : code.RootSurvivor) : Root := survivor.1.2.2

@[simp] theorem slot (survivor : code.RootSurvivor) :
    code.deduplicateRoots survivor.lineage =
      some (survivor.row, survivor.root) :=
  survivor.2

/-- A normalized child code stores at most one value at a fixed lineage. -/
theorem lineage_injective : Function.Injective (lineage (code := code)) := by
  intro left right hlineage
  have hvalue : (left.row, left.root) = (right.row, right.root) := by
    apply Option.some.inj
    calc
      some (left.row, left.root) =
          code.deduplicateRoots left.lineage := left.slot.symm
      _ = code.deduplicateRoots right.lineage := congrArg _ hlineage
      _ = some (right.row, right.root) := right.slot
  apply Subtype.ext
  exact Prod.ext hlineage hvalue

/-- Distinct survivors have distinct roots.  This is the semantic content of
root deduplication, including the row stored at the unique live lineage. -/
theorem root_injective : Function.Injective (root (code := code)) := by
  intro left right hroot
  have hright : code.deduplicateRoots right.lineage =
      some (right.row, left.root) := by
    simpa [hroot] using right.slot
  have hlineage : left.lineage = right.lineage :=
    code.deduplicateRoots_lineage_unique left.slot hright
  have hvalue : (left.row, left.root) = (right.row, right.root) := by
    apply Option.some.inj
    calc
      some (left.row, left.root) =
          code.deduplicateRoots left.lineage := left.slot.symm
      _ = code.deduplicateRoots right.lineage := congrArg _ hlineage
      _ = some (right.row, right.root) := right.slot
  apply Subtype.ext
  apply Prod.ext hlineage
  exact hvalue

/-- Every occurring old root has a literal survivor. -/
theorem exists_of_rootOccurs (root : Root) (hoccurs : code.RootOccurs root) :
    ∃ survivor : code.RootSurvivor, survivor.root = root := by
  rcases code.rootOccurs_deduplicateRoots root hoccurs with
    ⟨lineage, row, hslot⟩
  exact ⟨⟨(lineage, (row, root)), hslot⟩, rfl⟩

/-- A survivor witnesses occurrence in both the normalized and raw code. -/
theorem rootOccurs (survivor : code.RootSurvivor) :
    code.RootOccurs survivor.root := by
  rw [← code.rootOccurs_deduplicateRoots_iff]
  exact ⟨survivor.lineage, survivor.row, survivor.slot⟩

/-- If there is no normalized survivor, every normalized root slot is
inactive.  This is the generic inactive-lane half of the semantic handoff. -/
theorem rootSlots_eq_none_of_not_nonempty
    (hdead : ¬ Nonempty code.RootSurvivor) :
    code.deduplicateRoots.rootSlots = fun _ => none := by
  classical
  funext lineage
  cases hslot : code.deduplicateRoots.rootSlots lineage with
  | none => rfl
  | some root =>
      exfalso
      apply hdead
      rw [IndexedLineageChildCode.rootSlots_eq_some_iff] at hslot
      rcases hslot with ⟨row, hcode⟩
      exact ⟨⟨(lineage, (row, root)), hcode⟩⟩

end IndexedLineageChildCode.RootSurvivor

end

end DetParityAutomaton

end DistributedSynthesis
