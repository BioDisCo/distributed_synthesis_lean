/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenChildViewEquality
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenObservableThreads

/-!
# Finite indexed lineage across a reversal

A reversal starts with the four proof-side corners
`I × PairedEntryRow`.  The next blind-view class must not be supplied as an
arbitrary set by a direction: it is the equality class of the selected pivot
in one finite cross-candidate equality pattern.  This file materializes that
class as an ordered finite code

`I → Option (PairedEntryRow × Root)`.

Thus every old lineage keeps its index, and the code records at most one of
its two physical rows.  Exact histories and semantic representatives occur
only in the proof that the semantic construction produces such a code; they
do not occur in the code's type.  The right-to-left and left-to-right codes
are phase-specific, so no runtime orientation or strict-leader bit is stored
or delivered to a process.
-/

namespace DistributedSynthesis

universe i r u v x y s

namespace DetParityAutomaton

/-! ## Generic finite equality-pattern interface -/

/-- The four-corner candidate attached to one persistent lineage. -/
abbrev IndexedLineageCandidate (I : Type i) := I × PairedEntryRow

/-- A finite equality pattern on all cross-row candidates.  In the concrete
model its Boolean entries are maintained by the exact-view pair monitor. -/
abbrev IndexedLineageEqualityPattern (I : Type i) :=
  IndexedLineageCandidate I → IndexedLineageCandidate I → Bool

/-- The canonical post-handoff pattern: equality depends only on the physical
row, never on the persistent lineage index. -/
def indexedLineageCanonicalRowPattern (I : Type i) :
    IndexedLineageEqualityPattern I :=
  fun left right => decide (left.2 = right.2)

/-- At one selected pivot, no old lineage contributes both physical rows.
This is the exact condition needed to turn an equality class into a partial
function on persistent indices. -/
def IndexedLineageEqualityPattern.RowFunctionalAt
    {I : Type i} (pattern : IndexedLineageEqualityPattern I)
    (pivot : IndexedLineageCandidate I) : Prop :=
  ∀ member,
    ¬ (pattern (member, .first) pivot = true ∧
      pattern (member, .both) pivot = true)

theorem indexedLineageCanonicalRowPattern_rowFunctionalAt
    {I : Type i} (pivot : IndexedLineageCandidate I) :
    (indexedLineageCanonicalRowPattern I).RowFunctionalAt pivot := by
  intro member hboth
  have hfirst : PairedEntryRow.first = pivot.2 := by
    simpa [indexedLineageCanonicalRowPattern] using hboth.1
  have hboth' : PairedEntryRow.both = pivot.2 := by
    simpa [indexedLineageCanonicalRowPattern] using hboth.2
  have : PairedEntryRow.first = PairedEntryRow.both :=
    hfirst.trans hboth'.symm
  cases this

/-- An ordered successor class.  `member` is the persistent hidden lineage;
the optional value is the unique physical row and the finite successor root.
-/
abbrev IndexedLineageChildCode (I : Type i) (Root : Type u) :=
  I → Option (PairedEntryRow × Root)

noncomputable instance indexedLineageChildCodeFintype
    {I : Type i} {Root : Type u} [Fintype I] [Fintype Root] :
    Fintype (IndexedLineageChildCode I Root) := by
  classical
  infer_instance

/-- Materialize the pivot's class from the finite equality pattern.  The
first row has only a deterministic tie-breaking role; `RowFunctionalAt`
proves that the tie can never occur for a semantic pattern. -/
def indexedLineageChildCodeOfPattern
    {I : Type i} {Root : Type u}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I) : IndexedLineageChildCode I Root :=
  fun member =>
    if pattern (member, .first) pivot = true then
      some (.first, root (member, .first))
    else if pattern (member, .both) pivot = true then
      some (.both, root (member, .both))
    else none

@[simp] theorem indexedLineageChildCodeOfPattern_first
    {I : Type i} {Root : Type u}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I) (member : I)
    (hfirst : pattern (member, .first) pivot = true) :
    indexedLineageChildCodeOfPattern pattern root pivot member =
      some (.first, root (member, .first)) := by
  simp [indexedLineageChildCodeOfPattern, hfirst]

@[simp] theorem indexedLineageChildCodeOfPattern_both
    {I : Type i} {Root : Type u}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I) (member : I)
    (hfirst : pattern (member, .first) pivot ≠ true)
    (hboth : pattern (member, .both) pivot = true) :
    indexedLineageChildCodeOfPattern pattern root pivot member =
      some (.both, root (member, .both)) := by
  simp [indexedLineageChildCodeOfPattern, hfirst, hboth]

@[simp] theorem indexedLineageChildCodeOfPattern_none
    {I : Type i} {Root : Type u}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I) (member : I)
    (hfirst : pattern (member, .first) pivot ≠ true)
    (hboth : pattern (member, .both) pivot ≠ true) :
    indexedLineageChildCodeOfPattern pattern root pivot member = none := by
  simp [indexedLineageChildCodeOfPattern, hfirst, hboth]

/-- Source-free membership equation: after the equality pattern and pivot
are fixed, the ordered code contains exactly the candidates equal to the
pivot.  No semantic source or arbitrary announced grouping occurs here. -/
theorem indexedLineageChildCodeOfPattern_eq_some_iff
    {I : Type i} {Root : Type u}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I)
    (hfunctional : pattern.RowFunctionalAt pivot)
    (member : I) (row : PairedEntryRow) :
    indexedLineageChildCodeOfPattern pattern root pivot member =
        some (row, root (member, row)) ↔
      pattern (member, row) pivot = true := by
  cases row with
  | first =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · simp [indexedLineageChildCodeOfPattern, hfirst]
      · simp [indexedLineageChildCodeOfPattern, hfirst]
  | both =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · have hboth : pattern (member, .both) pivot ≠ true := by
          intro hboth
          exact hfunctional member ⟨hfirst, hboth⟩
        simp [indexedLineageChildCodeOfPattern, hfirst, hboth]
      · simp [indexedLineageChildCodeOfPattern, hfirst]

/-- Forget the physical row but retain the ordered successor-root slots. -/
def IndexedLineageChildCode.rootSlots
    {I : Type i} {Root : Type u} (code : IndexedLineageChildCode I Root) :
    I → Option Root :=
  fun member => (code member).map Prod.snd

theorem IndexedLineageChildCode.rootSlots_eq_some_of
    {I : Type i} {Root : Type u} (code : IndexedLineageChildCode I Root)
    {member : I} {row : PairedEntryRow} {root : Root}
    (hcode : code member = some (row, root)) :
    code.rootSlots member = some root := by
  simp [IndexedLineageChildCode.rootSlots, hcode]

/-- Forget successor roots and retain exactly the partial row assignment of
the selected equality class. -/
def IndexedLineageChildCode.rowSlots
    {I : Type i} {Root : Type u} (code : IndexedLineageChildCode I Root) :
    I → Option PairedEntryRow :=
  fun member => (code member).map Prod.fst

/-- The partial row assignment is computed only from the finite pattern and
the pivot. -/
theorem indexedLineageChildCodeOfPattern_rowSlots_eq_some_iff
    {I : Type i} {Root : Type u}
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I)
    (hfunctional : pattern.RowFunctionalAt pivot)
    (member : I) (row : PairedEntryRow) :
    (indexedLineageChildCodeOfPattern pattern root pivot).rowSlots member =
        some row ↔
      pattern (member, row) pivot = true := by
  cases row with
  | first =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · simp [IndexedLineageChildCode.rowSlots,
          indexedLineageChildCodeOfPattern, hfirst]
      · simp [IndexedLineageChildCode.rowSlots,
          indexedLineageChildCodeOfPattern, hfirst]
  | both =>
      by_cases hfirst : pattern (member, .first) pivot = true
      · have hboth : pattern (member, .both) pivot ≠ true := by
          intro hboth
          exact hfunctional member ⟨hfirst, hboth⟩
        simp [IndexedLineageChildCode.rowSlots,
          indexedLineageChildCodeOfPattern, hfirst, hboth]
      · simp [IndexedLineageChildCode.rowSlots,
          indexedLineageChildCodeOfPattern, hfirst]

/-- In the canonical reset pattern, every persistent lineage follows exactly
the pivot's row. -/
theorem indexedLineageCanonicalRowCode_rowSlots
    {I : Type i} {Root : Type u}
    (root : IndexedLineageCandidate I → Root)
    (pivot : IndexedLineageCandidate I) (member : I) :
    (indexedLineageChildCodeOfPattern
        (indexedLineageCanonicalRowPattern I) root pivot).rowSlots member =
      some pivot.2 := by
  apply (indexedLineageChildCodeOfPattern_rowSlots_eq_some_iff
    (indexedLineageCanonicalRowPattern I) root pivot
    (indexedLineageCanonicalRowPattern_rowFunctionalAt pivot) member
    pivot.2).2
  simp [indexedLineageCanonicalRowPattern]

/-! ## The concrete semantic pattern, used only to certify the finite code -/

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

/-- Exact process-two equality matrix of the four right-to-left semantic
children.  This matrix is proof-side here; a separate transfer theorem can
identify it with the matrix computed by the finite exact-view monitor. -/
noncomputable def procTwoChildViewPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    IndexedLineageEqualityPattern I := by
  classical
  exact fun left right => decide (
    currentView Proc.two
        (procTwoViewClassChild strategy entry past input left).rightHistory =
      currentView Proc.two
        (procTwoViewClassChild strategy entry past input right).rightHistory)

/-- Process-one mirror matrix. -/
noncomputable def procOneChildViewPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    IndexedLineageEqualityPattern I := by
  classical
  exact fun left right => decide (
    currentView Proc.one
        (procOneViewClassChild strategy entry past input left).leftHistory =
      currentView Proc.one
        (procOneViewClassChild strategy entry past input right).leftHistory)

/-- Finite right-to-left grouping pattern before the homogeneous block.  It
compares only the old opposite views selected by the two rows. -/
noncomputable def procOneEntryOppositeViewPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy) :
    IndexedLineageEqualityPattern I := by
  classical
  exact fun left right => decide (
    currentView Proc.two (procOneViewClassRowHistory entry left) =
      currentView Proc.two (procOneViewClassRowHistory entry right))

/-- Left-to-right old opposite-view pattern. -/
noncomputable def procTwoEntryOppositeViewPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy) :
    IndexedLineageEqualityPattern I := by
  classical
  exact fun left right => decide (
    currentView Proc.one (procTwoViewClassRowHistory entry left) =
      currentView Proc.one (procTwoViewClassRowHistory entry right))

@[simp] theorem procTwoChildViewPattern_eq_true_iff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (left right : IndexedLineageCandidate I) :
    procTwoChildViewPattern strategy entry past input left right = true ↔
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input left).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input right).rightHistory := by
  classical
  simp [procTwoChildViewPattern]

@[simp] theorem procOneChildViewPattern_eq_true_iff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (left right : IndexedLineageCandidate I) :
    procOneChildViewPattern strategy entry past input left right = true ↔
      currentView Proc.one
          (procOneViewClassChild strategy entry past input left).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input right).leftHistory := by
  classical
  simp [procOneChildViewPattern]

variable [Inhabited In₁] [Inhabited In₂]

section
omit [Inhabited In₁] [Inhabited In₂]

/-- The complete child grouping pattern is determined before the block: it
is exactly equality of the row-selected old opposite views.  Hence neither
`past` nor `input` is part of the grouping code. -/
theorem procTwoChildViewPattern_eq_oppositeViewPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.one (entry left).leftHistory =
        currentView Proc.one (entry right).leftHistory)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    procTwoChildViewPattern strategy entry past input =
      procOneEntryOppositeViewPattern strategy entry := by
  classical
  funext left right
  change decide (
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input left).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input right).rightHistory) =
    decide (
      currentView Proc.two (procOneViewClassRowHistory entry left) =
        currentView Proc.two (procOneViewClassRowHistory entry right))
  rw [propext (procTwoViewClassChild_view_eq_iff strategy entry hblind past
    input left right)]

/-- Left-to-right source-free grouping mirror. -/
theorem procOneChildViewPattern_eq_oppositeViewPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.two (entry left).rightHistory =
        currentView Proc.two (entry right).rightHistory)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    procOneChildViewPattern strategy entry past input =
      procTwoEntryOppositeViewPattern strategy entry := by
  classical
  funext left right
  change decide (
      currentView Proc.one
          (procOneViewClassChild strategy entry past input left).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input right).leftHistory) =
    decide (
      currentView Proc.one (procTwoViewClassRowHistory entry left) =
        currentView Proc.one (procTwoViewClassRowHistory entry right))
  rw [propext (procOneViewClassChild_view_eq_iff strategy entry hblind past
    input left right)]

/-- Any right-to-left successor family chosen from one new blind-view class
has the canonical diagonal opposite-view pattern.  The index type `J` can be
the represented class itself; its elements remain persistent lineages. -/
theorem procTwoChildFamily_oppositeViewPattern_eq_canonical
    {J : Type i}
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (candidate : J → IndexedLineageCandidate I)
    (hclass : ∀ left right,
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input
            (candidate left)).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input
            (candidate right)).rightHistory) :
    procTwoEntryOppositeViewPattern strategy (fun member =>
        procTwoViewClassChild strategy entry past input (candidate member)) =
      indexedLineageCanonicalRowPattern J := by
  classical
  funext left right
  change decide (
      currentView Proc.one
          (procTwoViewClassRowHistory
            (fun member => procTwoViewClassChild strategy entry past input
              (candidate member)) left) =
        currentView Proc.one
          (procTwoViewClassRowHistory
            (fun member => procTwoViewClassChild strategy entry past input
              (candidate member)) right)) =
    decide (left.2 = right.2)
  exact Bool.decide_congr (by
    simpa [procTwoViewClassRowHistory] using
      (procTwoViewClassChild_opposite_view_eq_iff_row_eq strategy entry past
        input (candidate left.1) (candidate right.1)
        (hclass left.1 right.1) left.2 right.2))

/-- Left-to-right reset mirror. -/
theorem procOneChildFamily_oppositeViewPattern_eq_canonical
    {J : Type i}
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (candidate : J → IndexedLineageCandidate I)
    (hclass : ∀ left right,
      currentView Proc.one
          (procOneViewClassChild strategy entry past input
            (candidate left)).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input
            (candidate right)).leftHistory) :
    procOneEntryOppositeViewPattern strategy (fun member =>
        procOneViewClassChild strategy entry past input (candidate member)) =
      indexedLineageCanonicalRowPattern J := by
  classical
  funext left right
  change decide (
      currentView Proc.two
          (procOneViewClassRowHistory
            (fun member => procOneViewClassChild strategy entry past input
              (candidate member)) left) =
        currentView Proc.two
          (procOneViewClassRowHistory
            (fun member => procOneViewClassChild strategy entry past input
              (candidate member)) right)) =
    decide (left.2 = right.2)
  exact Bool.decide_congr (by
    simpa [procOneViewClassRowHistory] using
      (procOneViewClassChild_opposite_view_eq_iff_row_eq strategy entry past
        input (candidate left.1) (candidate right.1)
        (hclass left.1 right.1) left.2 right.2))

/-- The model's four-corner separation makes every semantic process-two
equality class row-functional. -/
theorem procTwoChildViewPattern_rowFunctionalAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : IndexedLineageCandidate I) :
    (procTwoChildViewPattern strategy entry past input).RowFunctionalAt
      pivot := by
  intro member hboth
  have hfirst := (procTwoChildViewPattern_eq_true_iff strategy entry past
    input (member, .first) pivot).mp hboth.1
  have hsecond := (procTwoChildViewPattern_eq_true_iff strategy entry past
    input (member, .both) pivot).mp hboth.2
  have hrow := procTwoViewClassChild_row_injective strategy entry past input
    member .first .both (hfirst.trans hsecond.symm)
  cases hrow

/-- Left mirror row-functionality. -/
theorem procOneChildViewPattern_rowFunctionalAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : IndexedLineageCandidate I) :
    (procOneChildViewPattern strategy entry past input).RowFunctionalAt
      pivot := by
  intro member hboth
  have hfirst := (procOneChildViewPattern_eq_true_iff strategy entry past
    input (member, .first) pivot).mp hboth.1
  have hsecond := (procOneChildViewPattern_eq_true_iff strategy entry past
    input (member, .both) pivot).mp hboth.2
  have hrow := procOneViewClassChild_row_injective strategy entry past input
    member .first .both (hfirst.trans hsecond.symm)
  cases hrow

end

variable [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype I]

/-- The finite root attached to a right-to-left semantic candidate. -/
noncomputable def procTwoIndexedChildRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (candidate : IndexedLineageCandidate I) : ProfiledOpenLeftRoot A :=
  profiledOpenLeftRootOfWinning A strategy hwin
    (procTwoViewClassChild strategy entry past input candidate)
    (procTwoViewClassChildMinimum A entry past candidate) basis

/-- Left-to-right finite child root. -/
noncomputable def procOneIndexedChildRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (candidate : IndexedLineageCandidate I) : ProfiledOpenRightRoot A :=
  profiledOpenRightRootOfWinning A strategy hwin
    (procOneViewClassChild strategy entry past input candidate)
    (procOneViewClassChildMinimum A entry past candidate) basis

/-- Ordered right-to-left successor code.  Its value type is finite and
contains neither a history nor a semantic representative. -/
noncomputable def procTwoIndexedChildCode
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) :
    IndexedLineageChildCode I (ProfiledOpenLeftRoot A) :=
  indexedLineageChildCodeOfPattern
    (procTwoChildViewPattern strategy entry past input)
    (procTwoIndexedChildRoot A strategy hwin entry past input basis) pivot

/-- Ordered left-to-right successor code. -/
noncomputable def procOneIndexedChildCode
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) :
    IndexedLineageChildCode I (ProfiledOpenRightRoot A) :=
  indexedLineageChildCodeOfPattern
    (procOneChildViewPattern strategy entry past input)
    (procOneIndexedChildRoot A strategy hwin entry past input basis) pivot

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Exact source-free update equation for the right-to-left code: a slot is
present precisely when its finite pattern entry equals the pivot. -/
theorem procTwoIndexedChildCode_eq_some_iff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) (member : I)
    (row : PairedEntryRow) :
    procTwoIndexedChildCode A strategy hwin entry past input basis pivot
          member =
        some (row, procTwoIndexedChildRoot A strategy hwin entry past input
          basis (member, row)) ↔
      (member, row) ∈
        procTwoChildViewClass strategy entry past input pivot := by
  rw [procTwoIndexedChildCode,
    indexedLineageChildCodeOfPattern_eq_some_iff _ _ _
      (procTwoChildViewPattern_rowFunctionalAt strategy entry past input pivot)]
  exact (procTwoChildViewPattern_eq_true_iff strategy entry past input
    (member, row) pivot).trans
      (mem_procTwoChildViewClass strategy entry past input pivot
        (member, row)).symm

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-to-right source-free update equation. -/
theorem procOneIndexedChildCode_eq_some_iff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) (member : I)
    (row : PairedEntryRow) :
    procOneIndexedChildCode A strategy hwin entry past input basis pivot
          member =
        some (row, procOneIndexedChildRoot A strategy hwin entry past input
          basis (member, row)) ↔
      (member, row) ∈
        procOneChildViewClass strategy entry past input pivot := by
  rw [procOneIndexedChildCode,
    indexedLineageChildCodeOfPattern_eq_some_iff _ _ _
      (procOneChildViewPattern_rowFunctionalAt strategy entry past input pivot)]
  exact (procOneChildViewPattern_eq_true_iff strategy entry past input
    (member, row) pivot).trans
      (mem_procOneChildViewClass strategy entry past input pivot
        (member, row)).symm

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] [Fintype I] in
/-- The ordered right-to-left row update is genuinely source-free: its
domain is determined by the old finite opposite-view pattern, independently
of the homogeneous block history and closing input. -/
theorem procTwoIndexedChildCode_rowSlots_eq_some_iff_oldPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.one (entry left).leftHistory =
        currentView Proc.one (entry right).leftHistory)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) (member : I)
    (row : PairedEntryRow) :
    (procTwoIndexedChildCode A strategy hwin entry past input basis pivot).rowSlots
          member = some row ↔
      procOneEntryOppositeViewPattern strategy entry (member, row) pivot =
        true := by
  rw [procTwoIndexedChildCode,
    indexedLineageChildCodeOfPattern_rowSlots_eq_some_iff _ _ _
      (procTwoChildViewPattern_rowFunctionalAt strategy entry past input pivot),
    procTwoChildViewPattern_eq_oppositeViewPattern strategy entry hblind past
      input]

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] [Fintype I] in
/-- Source-free left-to-right row update. -/
theorem procOneIndexedChildCode_rowSlots_eq_some_iff_oldPattern
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.two (entry left).rightHistory =
        currentView Proc.two (entry right).rightHistory)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) (member : I)
    (row : PairedEntryRow) :
    (procOneIndexedChildCode A strategy hwin entry past input basis pivot).rowSlots
          member = some row ↔
      procTwoEntryOppositeViewPattern strategy entry (member, row) pivot =
        true := by
  rw [procOneIndexedChildCode,
    indexedLineageChildCodeOfPattern_rowSlots_eq_some_iff _ _ _
      (procOneChildViewPattern_rowFunctionalAt strategy entry past input pivot),
    procOneChildViewPattern_eq_oppositeViewPattern strategy entry hblind past
      input]

end

end


/-! ## Persistent finite hidden lineage state -/

/-- Refinement of the existing hidden thread state by one persistent lineage
index.  The index is monitor state, not a process observation or output. -/
inductive IndexedLineageThreadState (I : Type i) (Root : Type r) where
  | initial
  | live (lineage : I) (root : Root)
  | dead

noncomputable instance indexedLineageThreadStateFintype
    {I : Type i} {Root : Type r} [Fintype I] [Fintype Root] :
    Fintype (IndexedLineageThreadState I Root) := by
  classical
  let Rep := Bool ⊕ (I × Root)
  let e : IndexedLineageThreadState I Root ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .initial => .inl false
        | .dead => .inl true
        | .live lineage anchor => .inr (lineage, anchor)
      invFun := fun state =>
        match state with
        | .inl false => .initial
        | .inl true => .dead
        | .inr value => .live value.1 value.2
      left_inv := by intro state; cases state <;> rfl
      right_inv := by
        intro state
        rcases state with bit | value
        · cases bit <;> rfl
        · rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- Source-free update of one live lineage.  `current` is the ordered current
root code and `child` is the pattern-derived successor code.  The transition
never accepts a new lineage index from a direction. -/
noncomputable def indexedLineageThreadUpdate
    {I : Type i} {Root : Type r}
    (current : I → Option Root)
    (state : IndexedLineageThreadState I Root)
    (child : IndexedLineageChildCode I Root) :
    IndexedLineageThreadState I Root := by
  classical
  exact match state with
    | .initial => .initial
    | .dead => .dead
    | .live lineage anchor =>
        if current lineage = some anchor then
          match child lineage with
          | none => .dead
          | some (_, next) => .live lineage next
        else .dead

/-- The update retains the lineage index and follows the unique coded row. -/
theorem indexedLineageThreadUpdate_live_of
    {I : Type i} {Root : Type r}
    (current : I → Option Root)
    (child : IndexedLineageChildCode I Root)
    (lineage : I) (root next : Root)
    (row : PairedEntryRow)
    (hcurrent : current lineage = some root)
    (hchild : child lineage = some (row, next)) :
    indexedLineageThreadUpdate current (.live lineage root) child =
      .live lineage next := by
  simp [indexedLineageThreadUpdate, hcurrent, hchild]

/-! ## Compatibility with the existing anchor-only thread system -/

/-- Forget the persistent lineage and recover the repository's current
anchor-only thread state. -/
def indexedProfiledOpenThreadStateErase
    {I : Type i}
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    {A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)} :
    IndexedLineageThreadState I (ProfiledOpenClassifiedAnchor A) →
      ProfiledOpenThreadState A
  | .initial => .initial
  | .dead => .dead
  | .live _ anchor => .live anchor

/-- Erasing a successful indexed update gives the same live anchor as the
current anchor-only interface. -/
theorem indexedProfiledOpenThreadStateErase_update_live_of
    {I : Type i}
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    {A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (current : I → Option (ProfiledOpenClassifiedAnchor A))
    (child : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (lineage : I) (anchor next : ProfiledOpenClassifiedAnchor A)
    (row : PairedEntryRow)
    (hcurrent : current lineage = some anchor)
    (hchild : child lineage = some (row, next)) :
    indexedProfiledOpenThreadStateErase
        (indexedLineageThreadUpdate current (.live lineage anchor) child) =
      .live next := by
  rw [indexedLineageThreadUpdate_live_of current child lineage anchor next row
    hcurrent hchild]
  rfl

/-- Precise compatibility with the old live-step equation.  The indexed
update adds only persistence of `lineage`; after erasure it is the existing
anchor transition. -/
theorem indexedProfiledOpenThreadUpdate_erase_eq_oldStep
    {I : Type i}
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (initialObservation : ProfiledOpenObservation A)
    (currentSlots : I → Option (ProfiledOpenClassifiedAnchor A))
    (childCode : IndexedLineageChildCode I
      (ProfiledOpenClassifiedAnchor A))
    (lineage : I) (current next : ProfiledOpenClassifiedAnchor A)
    (row : PairedEntryRow)
    (letter : ProfiledOpenRepresentableMove A × ProfiledOpenObservation A)
    (direction : ProfiledOpenClassifiedDirection A)
    (hcurrent : currentSlots lineage = some current)
    (hchild : childCode lineage = some (row, next))
    (hsource : direction.anchor A = current)
    (hsuccessor : (letter.1.successor A direction).1 = next)
    (hclass : (letter.1.successor A direction).2 = letter.2.roots A) :
    indexedProfiledOpenThreadStateErase
        (indexedLineageThreadUpdate currentSlots
          (.live lineage current) childCode) =
      profiledOpenThreadStep A initialObservation (.live current) letter
        direction := by
  rw [indexedProfiledOpenThreadStateErase_update_live_of currentSlots
    childCode lineage current next row hcurrent hchild]
  rw [profiledOpenThreadStep_live_of A initialObservation current letter
    direction hsource hclass, hsuccessor]

/-- Why the refinement is necessary: the old state erases distinct live
lineages whenever their finite roots coincide.  Width `≤ 2` alone does not
make roots injective, so the old anchor state cannot in general prevent a
lineage switch at such a merge. -/
theorem indexedProfiledOpenThreadState_erase_live_eq
    {I : Type i}
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    {A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (left right : I) (anchor : ProfiledOpenClassifiedAnchor A) :
    indexedProfiledOpenThreadStateErase
        (IndexedLineageThreadState.live left anchor) =
      indexedProfiledOpenThreadStateErase
        (IndexedLineageThreadState.live right anchor) :=
  rfl

end DetParityAutomaton

end DistributedSynthesis
