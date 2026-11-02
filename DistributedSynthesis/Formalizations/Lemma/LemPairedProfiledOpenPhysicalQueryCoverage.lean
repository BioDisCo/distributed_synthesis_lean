/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedRecutPhase
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenStickyRowBankAdapterTest

/-!
# Physical-history coverage of witnessed closing queries

This file discharges the finite-history part of
`ProfiledOpenWitnessedPhysicalEpochQueryCovered`.  A strict physical history
is recorded proof-side by its actual lineage at each round.  The executable
phase does not select that lineage: it advances every lineage in `Finset.univ`.
Likewise, at the closing `both` round it retains every row-carrying pivot in
`Finset.univ`.

The central induction proves that the accumulator following the actual
lineage is a member of the retained finite phase after an arbitrary sequence
of strict-right and strict-left rounds, including arbitrarily many direct
reversals and re-reversals.  A second induction identifies its accumulator
with the old extensional two-list direction scan.  Consequently the literal
old direction summary belongs to the closing query set.

No process is told the side, lineage, pivot, sticky row, graph, or strict
leader.  These are witnesses used only to point to one member of a finite set
that retains all alternatives.
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

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## Actual strict histories and their retained finite runs -/

/-- One proof-side strict physical letter.  `side` is not executable local
state: it merely records whether the public graph was `right` or `left` so
that the proof can name the actual retained lineage member. -/
structure ProfiledOpenPhysicalStrictLetter where
  side : IndexedLineageSide
  lineage : I
  inputOne : In₁
  inputTwo : In₂

/-- The corresponding physical environment round. -/
def ProfiledOpenPhysicalStrictLetter.round
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) : EnvironmentRound In₁ In₂ :=
  { inputOne := letter.inputOne
    inputTwo := letter.inputTwo
    graph := match letter.side with
      | .right => .right
      | .left => .left }

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem ProfiledOpenPhysicalStrictLetter.round_graph_right
    (lineage : I) (inputOne : In₁) (inputTwo : In₂) :
    (ProfiledOpenPhysicalStrictLetter.round
      (ProfiledOpenPhysicalStrictLetter.mk .right lineage inputOne inputTwo)
      ).graph = .right :=
  rfl

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem ProfiledOpenPhysicalStrictLetter.round_graph_left
    (lineage : I) (inputOne : In₁) (inputTwo : In₂) :
    (ProfiledOpenPhysicalStrictLetter.round
      (ProfiledOpenPhysicalStrictLetter.mk .left lineage inputOne inputTwo)
      ).graph = .left :=
  rfl

/-- Advance one fixed-move accumulator along the distinguished proof-side
lineage of a strict physical letter. -/
noncomputable def profiledOpenPhysicalStrictAccumulatorStep
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (accumulator : ProfiledOpenIndexedDirectionAccumulator A move)
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :
    ProfiledOpenIndexedDirectionAccumulator A move :=
  match letter.side with
  | .right =>
      profiledOpenIndexedDirectionAccumulatorStepRight A initialCode move
        accumulator (((letter.lineage, letter.inputTwo), letter.inputOne))
  | .left =>
      profiledOpenIndexedDirectionAccumulatorStepLeft A initialCode move
        accumulator (((letter.lineage, letter.inputOne), letter.inputTwo))

/-- Accumulator scan from an arbitrary already-retained accumulator. -/
noncomputable def profiledOpenPhysicalStrictAccumulatorRunFrom
    (move : ProfiledOpenIndexedBiBeliefMove A) :
    ProfiledOpenIndexedDirectionAccumulator A move →
      List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
        (In₂ := In₂)) →
      ProfiledOpenIndexedDirectionAccumulator A move
  | accumulator, [] => accumulator
  | accumulator, letter :: history =>
      profiledOpenPhysicalStrictAccumulatorRunFrom move
        (profiledOpenPhysicalStrictAccumulatorStep A initialCode move
          accumulator letter) history

/-- Phase scan through the same strict history.  Both lineage arguments are
`Finset.univ`: the finite global witness retains every possible lineage and
does not choose an orientation-dependent one. -/
noncomputable def profiledOpenPhysicalStrictPhaseRunFrom
    (phase : ProfiledOpenPhysicalRecutPhase A) :
    List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) → ProfiledOpenPhysicalRecutPhase A
  | [] => phase
  | letter :: history =>
      profiledOpenPhysicalStrictPhaseRunFrom
        (phase.advance A initialCode Finset.univ Finset.univ letter.round)
        history

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenPhysicalStrictAccumulatorRunFrom_mem
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (accumulator : ProfiledOpenIndexedDirectionAccumulator A move)
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (hmem : (ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
      accumulator) ∈ phase.candidates) :
    ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
        (profiledOpenPhysicalStrictAccumulatorRunFrom A initialCode move
          accumulator history) ∈
      (profiledOpenPhysicalStrictPhaseRunFrom A initialCode phase history
        ).candidates := by
  induction history generalizing accumulator phase with
  | nil => exact hmem
  | cons letter history ih =>
      apply ih
      cases hside : letter.side with
      | right =>
          have hstep := ProfiledOpenPhysicalRecutPhase.mem_advance_right
            A initialCode phase Finset.univ Finset.univ
            (ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
              accumulator) letter.lineage letter.inputOne letter.inputTwo
            hmem (Finset.mem_univ _)
          simpa [profiledOpenPhysicalStrictAccumulatorStep,
            ProfiledOpenPhysicalStrictLetter.round, hside] using hstep
      | left =>
          have hstep := ProfiledOpenPhysicalRecutPhase.mem_advance_left
            A initialCode phase Finset.univ Finset.univ
            (ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
              accumulator) letter.lineage letter.inputOne letter.inputTwo
            hmem (Finset.mem_univ _)
          simpa [profiledOpenPhysicalStrictAccumulatorStep,
            ProfiledOpenPhysicalStrictLetter.round, hside] using hstep

/-- Start the distinguished scan at the empty accumulator for `move`. -/
noncomputable def profiledOpenPhysicalStrictAccumulatorRun
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    ProfiledOpenIndexedDirectionAccumulator A move :=
  profiledOpenPhysicalStrictAccumulatorRunFrom A initialCode move
    (profiledOpenIndexedDirectionAccumulatorInitial A move) history

/-- Start with every finite table move. -/
noncomputable def profiledOpenPhysicalStrictPhaseRun
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    ProfiledOpenPhysicalRecutPhase A :=
  profiledOpenPhysicalStrictPhaseRunFrom A initialCode
    (profiledOpenPhysicalRecutPhaseInitial A Finset.univ) history

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- **Arbitrary-history lineage coverage.**  Every actual move and lineage
thread is retained by the finite phase after every finite strict history. -/
theorem profiledOpenPhysicalStrictAccumulatorRun_mem
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
        (profiledOpenPhysicalStrictAccumulatorRun A initialCode move history)
      ∈ (profiledOpenPhysicalStrictPhaseRun A initialCode history).candidates := by
  apply profiledOpenPhysicalStrictAccumulatorRunFrom_mem A initialCode
  exact mem_profiledOpenPhysicalRecutPhaseInitial A Finset.univ move
    (Finset.mem_univ _)

/-! ## Equality with the extensional direction summary -/

/-- Right-oriented letters, in their original physical order. -/
def profiledOpenPhysicalStrictRightPast
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    List ((I × In₂) × In₁) :=
  history.filterMap fun letter =>
    match letter.side with
    | .right => some (((letter.lineage, letter.inputTwo), letter.inputOne))
    | .left => none

/-- Left-oriented letters, in their original physical order. -/
def profiledOpenPhysicalStrictLeftPast
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    List ((I × In₁) × In₂) :=
  history.filterMap fun letter =>
    match letter.side with
    | .right => none
    | .left => some (((letter.lineage, letter.inputOne), letter.inputTwo))

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
theorem profiledOpenPhysicalStrictAccumulatorRunFrom_append
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (accumulator : ProfiledOpenIndexedDirectionAccumulator A move)
    (left right : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    profiledOpenPhysicalStrictAccumulatorRunFrom A initialCode move
        accumulator (left ++ right) =
      profiledOpenPhysicalStrictAccumulatorRunFrom A initialCode move
        (profiledOpenPhysicalStrictAccumulatorRunFrom A initialCode move
          accumulator left) right := by
  induction left generalizing accumulator with
  | nil => rfl
  | cons letter left ih =>
      simp only [List.cons_append,
        profiledOpenPhysicalStrictAccumulatorRunFrom]
      exact ih _

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- The streaming physical scan is exactly the pre-existing two-list scan for
an arbitrary interleaving of strict directions. -/
theorem profiledOpenPhysicalStrictAccumulatorRun_eq_scan
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    profiledOpenPhysicalStrictAccumulatorRun A initialCode move history =
      profiledOpenIndexedDirectionAccumulatorScan A initialCode move
        (profiledOpenPhysicalStrictRightPast history)
        (profiledOpenPhysicalStrictLeftPast history) := by
  induction history using List.reverseRecOn with
  | nil => rfl
  | append_singleton history letter ih =>
      rw [profiledOpenPhysicalStrictAccumulatorRun,
        profiledOpenPhysicalStrictAccumulatorRunFrom_append]
      simp only [profiledOpenPhysicalStrictAccumulatorRunFrom]
      change profiledOpenPhysicalStrictAccumulatorStep A initialCode move
          (profiledOpenPhysicalStrictAccumulatorRun A initialCode move
            history) letter = _
      rw [ih]
      cases hside : letter.side with
      | right =>
          simpa [profiledOpenPhysicalStrictAccumulatorStep,
            profiledOpenPhysicalStrictRightPast,
            profiledOpenPhysicalStrictLeftPast, hside] using
            (profiledOpenIndexedDirectionAccumulatorScan_append_right
              A initialCode move
              (profiledOpenPhysicalStrictRightPast history)
              (profiledOpenPhysicalStrictLeftPast history)
              (((letter.lineage, letter.inputTwo), letter.inputOne)))
      | left =>
          simpa [profiledOpenPhysicalStrictAccumulatorStep,
            profiledOpenPhysicalStrictRightPast,
            profiledOpenPhysicalStrictLeftPast, hside] using
            (profiledOpenIndexedDirectionAccumulatorScan_append_left
              A initialCode move
              (profiledOpenPhysicalStrictRightPast history)
              (profiledOpenPhysicalStrictLeftPast history)
              (((letter.lineage, letter.inputOne), letter.inputTwo)))

/-- Raw old-style direction represented by one strict physical history and
the literal two closing pivots. -/
def profiledOpenPhysicalStrictHistoryDirection
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (closingInputOne : In₁) (closingInputTwo : In₂) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  { rightPivot := rightPivot
    rightTaggedPast := profiledOpenPhysicalStrictRightPast history
    rightInput := (closingInputTwo, closingInputOne)
    leftPivot := leftPivot
    leftTaggedPast := profiledOpenPhysicalStrictLeftPast history
    leftInput := (closingInputOne, closingInputTwo) }

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- Closing the retained actual accumulator gives literally the old finite
direction summary. -/
theorem profiledOpenPhysicalStrictAccumulatorRun_finish_eq_summary
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (closingInputOne : In₁) (closingInputTwo : In₂) :
    (ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
      (profiledOpenPhysicalStrictAccumulatorRun A initialCode move history)
      ).finish A rightPivot leftPivot closingInputOne closingInputTwo =
      ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
        (profiledOpenPhysicalStrictHistoryDirection history rightPivot
          leftPivot closingInputOne closingInputTwo)⟩ := by
  simp only [ProfiledOpenPhysicalDirectionAccumulatorCandidate.finish]
  rw [profiledOpenPhysicalStrictAccumulatorRun_eq_scan]
  exact congrArg (Sigma.mk move)
    (profiledOpenIndexedDirectionAccumulator_finish_scan A initialCode move
      (profiledOpenPhysicalStrictHistoryDirection history rightPivot leftPivot
        closingInputOne closingInputTwo))

/-! ## The unconditional closing coverage test -/

section
omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- **Arbitrary strict-history coverage test.**  For every finite physical
strict history, every actual move, every pair of actual sticky-row pivots, and
either proof-side closing side, the literal old summarized query is among the
finite queries produced at `both`.

All candidate domains are `Finset.univ`, so this theorem has no lineage,
pivot, row-recovery, leader-detection, or orientation-observability premise. -/
theorem profiledOpenWitnessedPhysicalEpochQueryCovered_of_strictHistory
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (carriedQuery : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (closingInputOne : In₁) (closingInputTwo : In₂) :
    let phase := profiledOpenPhysicalStrictPhaseRun A initialCode history
    let direction := profiledOpenPhysicalStrictHistoryDirection history
      rightPivot leftPivot closingInputOne closingInputTwo
    let literalQuery := profiledOpenWitnessedTableQueryWithDirection A
      initialCode carriedQuery side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          direction⟩
    ProfiledOpenWitnessedPhysicalEpochQueryCovered A initialCode phase
      carriedQuery literalQuery side Finset.univ Finset.univ
      { inputOne := closingInputOne, inputTwo := closingInputTwo,
        graph := .both } := by
  classical
  dsimp only
  constructor
  · rfl
  · rw [← profiledOpenPhysicalStrictAccumulatorRun_finish_eq_summary
      A initialCode move history rightPivot leftPivot closingInputOne
      closingInputTwo]
    exact ProfiledOpenPhysicalRecutPhase.mem_finishedQueriesForSide
      A initialCode _ carriedQuery side Finset.univ Finset.univ
      (ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
        (profiledOpenPhysicalStrictAccumulatorRun A initialCode move history))
      rightPivot leftPivot closingInputOne closingInputTwo
      (profiledOpenPhysicalStrictAccumulatorRun_mem A initialCode move history)
      (Finset.mem_univ _) (Finset.mem_univ _)

/-- Adapter-clock form of the coverage theorem.  `advancePhase` is evaluated
on the closing `both` round before the adapter invokes `restartPhase`; the
closing phase has returned to `boundary`, but its candidate set is
definitionally the same retained set. -/
theorem profiledOpenWitnessedPhysicalEpochQueryCovered_after_both
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (carriedQuery : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (closingInputOne : In₁) (closingInputTwo : In₂) :
    let openPhase := profiledOpenPhysicalStrictPhaseRun A initialCode history
    let closingRound : EnvironmentRound In₁ In₂ :=
      { inputOne := closingInputOne, inputTwo := closingInputTwo,
        graph := .both }
    let phase := openPhase.advance A initialCode Finset.univ Finset.univ
      closingRound
    let direction := profiledOpenPhysicalStrictHistoryDirection history
      rightPivot leftPivot closingInputOne closingInputTwo
    let literalQuery := profiledOpenWitnessedTableQueryWithDirection A
      initialCode carriedQuery side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          direction⟩
    phase.tier = .boundary ∧
      ProfiledOpenWitnessedPhysicalEpochQueryCovered A initialCode phase
        carriedQuery literalQuery side Finset.univ Finset.univ closingRound := by
  classical
  dsimp only
  constructor
  · rfl
  · constructor
    · rfl
    · rw [← profiledOpenPhysicalStrictAccumulatorRun_finish_eq_summary
        A initialCode move history rightPivot leftPivot closingInputOne
        closingInputTwo]
      exact ProfiledOpenPhysicalRecutPhase.mem_finishedQueriesForSide
        A initialCode _ carriedQuery side Finset.univ Finset.univ
        (ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk move
          (profiledOpenPhysicalStrictAccumulatorRun A initialCode move history))
        rightPivot leftPivot closingInputOne closingInputTwo
        (profiledOpenPhysicalStrictAccumulatorRun_mem A initialCode move
          history)
        (Finset.mem_univ _) (Finset.mem_univ _)

/-- Same statement for an arbitrary supplied closing record known to have
graph `both`.  This is the shape directly consumed by a physical-round
adapter invariant. -/
theorem profiledOpenWitnessedPhysicalEpochQueryCovered_after_closingRound
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (carriedQuery : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (closingRound : EnvironmentRound In₁ In₂)
    (hboth : closingRound.graph = .both) :
    let openPhase := profiledOpenPhysicalStrictPhaseRun A initialCode history
    let phase := openPhase.advance A initialCode Finset.univ Finset.univ
      closingRound
    let direction := profiledOpenPhysicalStrictHistoryDirection history
      rightPivot leftPivot closingRound.inputOne closingRound.inputTwo
    let literalQuery := profiledOpenWitnessedTableQueryWithDirection A
      initialCode carriedQuery side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          direction⟩
    phase.tier = .boundary ∧
      ProfiledOpenWitnessedPhysicalEpochQueryCovered A initialCode phase
        carriedQuery literalQuery side Finset.univ Finset.univ closingRound := by
  rcases closingRound with ⟨inputOne, inputTwo, graph⟩
  dsimp only at hboth ⊢
  subst graph
  exact profiledOpenWitnessedPhysicalEpochQueryCovered_after_both A
    initialCode move history carriedQuery side rightPivot leftPivot inputOne
    inputTwo

end

end

end DetParityAutomaton

end DistributedSynthesis
