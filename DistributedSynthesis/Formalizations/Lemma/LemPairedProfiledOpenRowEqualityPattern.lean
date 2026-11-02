/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenChildViewEquality

/-!
# The finite cross-row equality pattern

A Boolean open family contains two persistent proof-side lineages.  Each
lineage is itself a pending two-row entry.  At a reversal, the exact view
class among the four possible children is not determined by the width bound
alone: it also depends on which row of the first lineage has the same hidden
receiver view as which row of the second lineage.

That missing information is finite.  It is the `2 x 2` Boolean matrix
`PairedCrossRowEqualityPattern`.  This file proves that, for a genuine
same-view family, the matrix computes the complete successor partition.  The
computation uses no selected leader or orientation observation.  Lineage and
row are proof-side coordinates only.
-/

namespace DistributedSynthesis

universe u v x y

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Finite matrix and its induced four-corner partition -/

/-- The row-pair equality matrix between the two persistent lineages. -/
abbrev PairedCrossRowEqualityPattern :=
  PairedEntryRow → PairedEntryRow → Bool

noncomputable instance : Fintype PairedCrossRowEqualityPattern := by
  classical
  infer_instance

/-- The matrix carried by a genuine process-one family.  Its entries compare
the process-two views, which are the views that determine the next left
family. -/
def procOneFamilyCrossRowEqualityPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (entry : Bool → ProcOnePairedEntryRep strategy) :
    PairedCrossRowEqualityPattern := by
  classical
  exact fun leftRow rightRow => decide (
    currentView Proc.two
        (procOneViewClassRowHistory entry (false, leftRow)) =
      currentView Proc.two
        (procOneViewClassRowHistory entry (true, rightRow)))

/-- Mirror matrix for a process-two family. -/
def procTwoFamilyCrossRowEqualityPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (entry : Bool → ProcTwoPairedEntryRep strategy) :
    PairedCrossRowEqualityPattern := by
  classical
  exact fun leftRow rightRow => decide (
    currentView Proc.one
        (procTwoViewClassRowHistory entry (false, leftRow)) =
      currentView Proc.one
        (procTwoViewClassRowHistory entry (true, rightRow)))

/-- Source-free equality test on two four-corner coordinates.  On the same
lineage, row injectivity says that only the identical row is possible.  Across
lineages, the matrix is read in its fixed `false`-then-`true` order. -/
def pairedCrossRowEquivalent
    (pattern : PairedCrossRowEqualityPattern)
    (left right : Bool × PairedEntryRow) : Bool :=
  if left.1 = right.1 then decide (left.2 = right.2)
  else if left.1 = false then pattern left.2 right.2
  else pattern right.2 left.2

/-- The complete source-free class containing `pivot`. -/
noncomputable def pairedCrossRowClass
    (pattern : PairedCrossRowEqualityPattern)
    (pivot : Bool × PairedEntryRow) : Finset (Bool × PairedEntryRow) := by
  classical
  exact Finset.univ.filter fun candidate =>
    pairedCrossRowEquivalent pattern candidate pivot

@[simp] theorem mem_pairedCrossRowClass
    (pattern : PairedCrossRowEqualityPattern)
    (pivot candidate : Bool × PairedEntryRow) :
    candidate ∈ pairedCrossRowClass pattern pivot ↔
      pairedCrossRowEquivalent pattern candidate pivot = true := by
  classical
  simp [pairedCrossRowClass]

/-! ## Same-lineage row injectivity in matrix form -/

theorem procOneViewClassRowHistory_same_member_eq_iff
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : Bool → ProcOnePairedEntryRep strategy)
    (member : Bool) (leftRow rightRow : PairedEntryRow) :
    currentView Proc.two
        (procOneViewClassRowHistory entry (member, leftRow)) =
      currentView Proc.two
        (procOneViewClassRowHistory entry (member, rightRow)) ↔
      leftRow = rightRow := by
  cases leftRow <;> cases rightRow
  · simp
  · simpa [procOneViewClassRowHistory] using
      iff_false_intro (entry member).other_view_ne
  · simpa [procOneViewClassRowHistory] using
      iff_false_intro (entry member).other_view_ne.symm
  · simp

theorem procTwoViewClassRowHistory_same_member_eq_iff
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : Bool → ProcTwoPairedEntryRep strategy)
    (member : Bool) (leftRow rightRow : PairedEntryRow) :
    currentView Proc.one
        (procTwoViewClassRowHistory entry (member, leftRow)) =
      currentView Proc.one
        (procTwoViewClassRowHistory entry (member, rightRow)) ↔
      leftRow = rightRow := by
  cases leftRow <;> cases rightRow
  · simp
  · simpa [procTwoViewClassRowHistory] using
      iff_false_intro (entry member).other_view_ne
  · simpa [procTwoViewClassRowHistory] using
      iff_false_intro (entry member).other_view_ne.symm
  · simp

/-! ## The source-free matrix computes the semantic partition -/

/-- Exact right-to-left grouping theorem. -/
theorem procTwoChildViewClass_eq_pairedCrossRowClass
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcOnePairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.one (entry left).leftHistory =
        currentView Proc.one (entry right).leftHistory)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : Bool × PairedEntryRow) :
    procTwoChildViewClass strategy entry past input pivot =
      pairedCrossRowClass
        (procOneFamilyCrossRowEqualityPattern strategy entry) pivot := by
  classical
  ext candidate
  rw [mem_procTwoChildViewClass, mem_pairedCrossRowClass,
    procTwoViewClassChild_view_eq_iff strategy entry hblind]
  rcases candidate with ⟨candidateMember, candidateRow⟩
  rcases pivot with ⟨pivotMember, pivotRow⟩
  cases candidateMember <;> cases pivotMember
  · rw [procOneViewClassRowHistory_same_member_eq_iff]
    simp [pairedCrossRowEquivalent]
  · simp [pairedCrossRowEquivalent, procOneFamilyCrossRowEqualityPattern]
  · simp [pairedCrossRowEquivalent, procOneFamilyCrossRowEqualityPattern,
      eq_comm]
  · rw [procOneViewClassRowHistory_same_member_eq_iff]
    simp [pairedCrossRowEquivalent]

/-- Exact left-to-right mirror grouping theorem. -/
theorem procOneChildViewClass_eq_pairedCrossRowClass
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcTwoPairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.two (entry left).rightHistory =
        currentView Proc.two (entry right).rightHistory)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : Bool × PairedEntryRow) :
    procOneChildViewClass strategy entry past input pivot =
      pairedCrossRowClass
        (procTwoFamilyCrossRowEqualityPattern strategy entry) pivot := by
  classical
  ext candidate
  rw [mem_procOneChildViewClass, mem_pairedCrossRowClass,
    procOneViewClassChild_view_eq_iff strategy entry hblind]
  rcases candidate with ⟨candidateMember, candidateRow⟩
  rcases pivot with ⟨pivotMember, pivotRow⟩
  cases candidateMember <;> cases pivotMember
  · rw [procTwoViewClassRowHistory_same_member_eq_iff]
    simp [pairedCrossRowEquivalent]
  · simp [pairedCrossRowEquivalent, procTwoFamilyCrossRowEqualityPattern]
  · simp [pairedCrossRowEquivalent, procTwoFamilyCrossRowEqualityPattern,
      eq_comm]
  · rw [procTwoViewClassRowHistory_same_member_eq_iff]
    simp [pairedCrossRowEquivalent]

end

end DetParityAutomaton

end DistributedSynthesis
