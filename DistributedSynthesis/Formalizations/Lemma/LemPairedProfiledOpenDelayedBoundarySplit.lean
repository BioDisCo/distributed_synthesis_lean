/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenZeroOpenStutterRepair
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPhysicalQueryCoverage

/-!
# Delayed exact cuts at a simultaneous boundary

The row of the *next* paired direction determines the graph of the current
closing round.  Consequently a simultaneous physical round has two exact
uses, decided by the first strict side after it.

* If the strict side changes, the preceding direction closes directly on the
  simultaneous round; the following direction starts in row `both`.
* If the strict side repeats, the preceding direction closes on its last
  strict round and the simultaneous round is a real zero-open direction of
  the opposite orientation.  This is the exact construction proved in
  `LemPairedProfiledOpenZeroOpenStutterRepair`.

This file proves the missing direct-switch half and records that the finite
table/query interface can finish an accumulator at an arbitrary physical
letter.  The old `ProfiledOpenWitnessedPhysicalEpochQueryCovered` wrapper
adds `graph = both`, but its finite-tag membership theorem never needed that
premise.  Thus the table interface already supports the delayed strict close;
only the physical clock deciding when to consume one or two queries remains
to be changed.

All sides, rows, and lineages below are proof-side data.  No process is given
an orientation or strict-leader bit.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

/-! ## The direct-switch alternative -/

/-- If a right strict run is followed by a left strict run, the old right
direction closes directly on the actual simultaneous round. -/
theorem pairedDirectionChunk_rightToLeft_directBoth
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow)
    (strictPrefix : List (In₂ × In₁)) (lastStrict : In₂ × In₁)
    (closing : In₁ × In₂)
    (nextPast : List (In₁ × In₂)) (nextMove : In₁ × In₂) :
    pairedDirectionChunk
        (.fromOne row (strictPrefix ++ [lastStrict])
          (closing.2, closing.1))
        (.fromTwo .both nextPast nextMove) =
      strictPrefix.map rightEnvironment ++
        [rightEnvironment lastStrict,
          { inputOne := closing.1, inputTwo := closing.2,
            graph := .both }] := by
  simp [pairedDirectionChunk, pairedClosingGraph, rightEnvironment,
    List.map_append, List.append_assoc]

/-- Mirror: a left strict run followed by a right strict run closes directly
on the actual simultaneous round. -/
theorem pairedDirectionChunk_leftToRight_directBoth
    {In₁ : Type u} {In₂ : Type v}
    (row : PairedEntryRow)
    (strictPrefix : List (In₁ × In₂)) (lastStrict : In₁ × In₂)
    (closing : In₁ × In₂)
    (nextPast : List (In₂ × In₁)) (nextMove : In₂ × In₁) :
    pairedDirectionChunk
        (.fromTwo row (strictPrefix ++ [lastStrict]) closing)
        (.fromOne .both nextPast nextMove) =
      strictPrefix.map leftEnvironment ++
        [leftEnvironment lastStrict,
          { inputOne := closing.1, inputTwo := closing.2,
            graph := .both }] := by
  simp [pairedDirectionChunk, pairedClosingGraph, leftEnvironment,
    List.map_append, List.append_assoc]

/-! ## Exact strategy outputs on the chosen cuts -/

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  {A₀ : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {strategy₀ : StrategyPair In₁ In₂ Out₁ Out₂}
variable [Inhabited In₁] [Inhabited In₂]

/-- Two compatible paired directions do not merely reproduce the environment
word: extending the original distributed strategy through their two chunks
lands at the literal selected history after the two semantic memory steps.
Thus the boundary split preserves the physical outputs exactly. -/
theorem extend_selectedHistory_twoChunks
    (memory : PairedStrategyMemory A₀ strategy₀)
    (current middle next :
      PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcurrent : PairedStrategyMemory.DirectionCompatible
      (A := A₀) memory current)
    (hmiddle : PairedStrategyMemory.DirectionCompatible (A := A₀)
      (memory.step (A := A₀) current) middle)
    (hnext : PairedStrategyMemory.DirectionCompatible (A := A₀)
      ((memory.step (A := A₀) current).step (A := A₀) middle) next) :
    extendPrefix strategy₀
        (PairedStrategyMemory.selectedHistory memory current)
        (pairedDirectionChunk current middle ++
          pairedDirectionChunk middle next) =
      PairedStrategyMemory.selectedHistory
        ((memory.step (A := A₀) current).step (A := A₀) middle)
        next := by
  rw [PairedStrategyMemory.extendPrefix_append]
  rw [PairedStrategyMemory.extend_selectedHistory_chunk memory current middle
    hcurrent hmiddle]
  exact PairedStrategyMemory.extend_selectedHistory_chunk
    (memory.step (A := A₀) current) middle next hmiddle hnext

/-- The one-chunk direct-switch alternative also preserves the literal
strategy history and hence every emitted output. -/
theorem extend_selectedHistory_directChunk
    (memory : PairedStrategyMemory A₀ strategy₀)
    (current next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcurrent : PairedStrategyMemory.DirectionCompatible
      (A := A₀) memory current)
    (hnext : PairedStrategyMemory.DirectionCompatible (A := A₀)
      (memory.step (A := A₀) current) next) :
    extendPrefix strategy₀
        (PairedStrategyMemory.selectedHistory memory current)
        (pairedDirectionChunk current next) =
      PairedStrategyMemory.selectedHistory
        (memory.step (A := A₀) current) next :=
  PairedStrategyMemory.extend_selectedHistory_chunk memory current next
    hcurrent hnext

/-! ## Finite queries may close on any physical letter -/

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## The requested pivot root and its exact priority survive normalization -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The literal right-to-left pivot candidate occurs in the normalized child
code.  Root deduplication may change its persistent lineage representative,
but it cannot discard the pivot's finite root. -/
theorem procTwoIndexedPivotRoot_survivesDeduplication
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) :
    (procTwoIndexedChildCode A strategy hwin entry past input basis pivot
      ).deduplicateRoots.RootOccurs
        (procTwoIndexedChildRoot A strategy hwin entry past input basis
          pivot) := by
  let code := procTwoIndexedChildCode A strategy hwin entry past input basis
    pivot
  have hpivot : code pivot.1 = some (pivot.2,
      procTwoIndexedChildRoot A strategy hwin entry past input basis pivot) :=
    (procTwoIndexedChildCode_eq_some_iff A strategy hwin entry past input
      basis pivot pivot.1 pivot.2).2
        (pivot_mem_procTwoChildViewClass strategy entry past input pivot)
  apply code.rootOccurs_deduplicateRoots
  exact ⟨pivot.1, pivot.2, hpivot⟩

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-to-right mirror of pivot-root preservation. -/
theorem procOneIndexedPivotRoot_survivesDeduplication
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) :
    (procOneIndexedChildCode A strategy hwin entry past input basis pivot
      ).deduplicateRoots.RootOccurs
        (procOneIndexedChildRoot A strategy hwin entry past input basis
          pivot) := by
  let code := procOneIndexedChildCode A strategy hwin entry past input basis
    pivot
  have hpivot : code pivot.1 = some (pivot.2,
      procOneIndexedChildRoot A strategy hwin entry past input basis pivot) :=
    (procOneIndexedChildCode_eq_some_iff A strategy hwin entry past input
      basis pivot pivot.1 pivot.2).2
        (pivot_mem_procOneChildViewClass strategy entry past input pivot)
  apply code.rootOccurs_deduplicateRoots
  exact ⟨pivot.1, pivot.2, hpivot⟩

omit [Fintype I] [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- The surviving right-to-left pivot root records exactly the block minimum
of the requested physical row.  This equality is independent of which
lineage root deduplication chooses. -/
theorem profiledOpenIndexedPivotLeftRoot_priority_eq_blockMin
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) :
    profiledOpenClassifiedAnchorPriority A
        (.left (procTwoIndexedChildRoot A strategy hwin entry past input
          basis pivot)) =
      A.priority (procTwoViewClassChildMinimum A entry past pivot) := by
  rfl

omit [Fintype I] [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Mirror exact block-minimum equality. -/
theorem profiledOpenIndexedPivotRightRoot_priority_eq_blockMin
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (pivot : IndexedLineageCandidate I) :
    profiledOpenClassifiedAnchorPriority A
        (.right (procOneIndexedChildRoot A strategy hwin entry past input
          basis pivot)) =
      A.priority (procOneViewClassChildMinimum A entry past pivot) := by
  rfl

/-- The finite part of physical query coverage, without imposing a graph on
the letter whose inputs finish the retained accumulator. -/
def ProfiledOpenWitnessedPhysicalDirectionQueryCovered
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (carriedQuery literalQuery :
      ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivots leftPivots : Finset (IndexedLineageCandidate I))
    (inputOne : In₁) (inputTwo : In₂) : Prop :=
  literalQuery ∈ phase.finishedQueriesForSide A initialCode carriedQuery
    side rightPivots leftPivots inputOne inputTwo

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every accumulated physical strict history can be finished at arbitrary
current inputs.  In particular the current letter may be the last strict
letter rather than a simultaneous letter. -/
theorem profiledOpenWitnessedPhysicalDirectionQueryCovered_of_strictHistory
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (carriedQuery : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (currentInputOne : In₁) (currentInputTwo : In₂) :
    let phase := profiledOpenPhysicalStrictPhaseRun A initialCode history
    let direction := profiledOpenPhysicalStrictHistoryDirection history
      rightPivot leftPivot currentInputOne currentInputTwo
    let literalQuery := profiledOpenWitnessedTableQueryWithDirection A
      initialCode carriedQuery side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          direction⟩
    ProfiledOpenWitnessedPhysicalDirectionQueryCovered A initialCode phase
      carriedQuery literalQuery side Finset.univ Finset.univ
      currentInputOne currentInputTwo := by
  classical
  dsimp only
  unfold ProfiledOpenWitnessedPhysicalDirectionQueryCovered
  rw [← profiledOpenPhysicalStrictAccumulatorRun_finish_eq_summary
    A initialCode move history rightPivot leftPivot currentInputOne
      currentInputTwo]
  exact ProfiledOpenPhysicalRecutPhase.mem_finishedQueriesForSide
    A initialCode _ carriedQuery side Finset.univ Finset.univ
    (ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
      (profiledOpenPhysicalStrictAccumulatorRun A initialCode move history))
    rightPivot leftPivot currentInputOne currentInputTwo
    (profiledOpenPhysicalStrictAccumulatorRun_mem A initialCode move history)
    (Finset.mem_univ _) (Finset.mem_univ _)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The delayed same-side repair's zero-open query is already an ordinary
finite table query: use an empty accumulator and row `first`. -/
theorem profiledOpenWitnessedPhysicalDirectionQueryCovered_zeroOpen_first
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (carriedQuery : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (inputOne : In₁) (inputTwo : In₂) :
    let pivot : IndexedLineageCandidate I := (default, .first)
    let phase := profiledOpenPhysicalStrictPhaseRun A initialCode []
    let direction := profiledOpenPhysicalStrictHistoryDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) [] pivot pivot inputOne inputTwo
    let literalQuery := profiledOpenWitnessedTableQueryWithDirection A
      initialCode carriedQuery side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          direction⟩
    ProfiledOpenWitnessedPhysicalDirectionQueryCovered A initialCode phase
      carriedQuery literalQuery side Finset.univ Finset.univ inputOne
        inputTwo := by
  exact profiledOpenWitnessedPhysicalDirectionQueryCovered_of_strictHistory
    A initialCode move [] carriedQuery side (default, .first)
      (default, .first) inputOne inputTwo

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- After a simultaneous close, the first direction of the next strict run
can likewise be installed with row `both`.  The row is finite tag data, not a
locally detected leader flag. -/
theorem profiledOpenWitnessedPhysicalDirectionQueryCovered_empty_bothRow
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (carriedQuery : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (inputOne : In₁) (inputTwo : In₂) :
    let pivot : IndexedLineageCandidate I := (default, .both)
    let phase := profiledOpenPhysicalStrictPhaseRun A initialCode []
    let direction := profiledOpenPhysicalStrictHistoryDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) [] pivot pivot inputOne inputTwo
    let literalQuery := profiledOpenWitnessedTableQueryWithDirection A
      initialCode carriedQuery side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          direction⟩
    ProfiledOpenWitnessedPhysicalDirectionQueryCovered A initialCode phase
      carriedQuery literalQuery side Finset.univ Finset.univ inputOne
        inputTwo := by
  exact profiledOpenWitnessedPhysicalDirectionQueryCovered_of_strictHistory
    A initialCode move [] carriedQuery side (default, .both)
      (default, .both) inputOne inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
