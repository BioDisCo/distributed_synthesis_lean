/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedStreamingQueryAccumulator
import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageStutterAudit

/-!
# Repeated-side physical recut audit

The code-lineage objective alternates its hidden side after every code
letter.  The physical streaming adapter instead closes on every `.both`
round, resets its recut phase to `boundary`, and derives the next query side
from the strict history following that reset.

This file records two exact consequences of those definitions.

* Two consecutive `right*; both` epochs (and likewise two left epochs) select
  the same completed-query side.  The physical clock therefore does not
  establish the alternation required by the current code thread.
* A `.both` round cannot be hidden inside one grouped strict history: every
  `ProfiledOpenPhysicalStrictLetter` has graph `.right` or `.left`.  Hence the
  current direction/query interface cannot merge two same-side epochs while
  preserving the intervening physical round.

Together with `alternatingAcceptance_does_not_imply_retainSideAcceptance`,
this rules out inheriting parity by a mere recut or same-side stutter.  A
repair must strengthen the objective/transition interface (or prove a new
semantic composition theorem); it cannot be obtained from the present
alternating monitor and strict-history scanner definitionally.
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

/-- The side which the concrete streaming accumulator places in a completed
query after scanning one strict history.  Empty histories use the adapter's
documented default `.right`. -/
def profiledOpenPhysicalCompletedQuerySide
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂))) : IndexedLineageSide :=
  (profiledOpenPhysicalStrictPhaseRun A initialCode history).tier.activeSide
    |>.getD .right

/-- A nonempty one-round right epoch selects the right query side. -/
@[simp] theorem profiledOpenPhysicalCompletedQuerySide_single_right
    (lineage : I) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenPhysicalCompletedQuerySide A initialCode
      [⟨.right, lineage, inputOne, inputTwo⟩] = .right := by
  rfl

/-- Left mirror. -/
@[simp] theorem profiledOpenPhysicalCompletedQuerySide_single_left
    (lineage : I) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenPhysicalCompletedQuerySide A initialCode
      [⟨.left, lineage, inputOne, inputTwo⟩] = .left := by
  rfl

/-- The completed side can repeat across two independently reset physical
epochs, so it is not forced to be the previous side's opposite. -/
theorem profiledOpenPhysicalCompletedQuerySide_can_repeat_right
    (lineage₁ lineage₂ : I)
    (inputOne₁ inputOne₂ : In₁) (inputTwo₁ inputTwo₂ : In₂) :
    let first := profiledOpenPhysicalCompletedQuerySide A initialCode
      [⟨.right, lineage₁, inputOne₁, inputTwo₁⟩]
    let second := profiledOpenPhysicalCompletedQuerySide A initialCode
      [⟨.right, lineage₂, inputOne₂, inputTwo₂⟩]
    first = .right ∧ second = .right ∧ second ≠ first.other := by
  dsimp only
  rw [profiledOpenPhysicalCompletedQuerySide_single_right,
    profiledOpenPhysicalCompletedQuerySide_single_right]
  simp [IndexedLineageSide.other]

/-- Left mirror of the repeated-side witness. -/
theorem profiledOpenPhysicalCompletedQuerySide_can_repeat_left
    (lineage₁ lineage₂ : I)
    (inputOne₁ inputOne₂ : In₁) (inputTwo₁ inputTwo₂ : In₂) :
    let first := profiledOpenPhysicalCompletedQuerySide A initialCode
      [⟨.left, lineage₁, inputOne₁, inputTwo₁⟩]
    let second := profiledOpenPhysicalCompletedQuerySide A initialCode
      [⟨.left, lineage₂, inputOne₂, inputTwo₂⟩]
    first = .left ∧ second = .left ∧ second ≠ first.other := by
  dsimp only
  rw [profiledOpenPhysicalCompletedQuerySide_single_left,
    profiledOpenPhysicalCompletedQuerySide_single_left]
  simp [IndexedLineageSide.other]

/-! ## An intervening `.both` cannot be absorbed by the strict scanner -/

/-- Every letter admitted by the current grouped-direction scanner is
strict: its graph is definitionally never `.both`. -/
theorem ProfiledOpenPhysicalStrictLetter.round_graph_ne_both
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :
    letter.round.graph ≠ .both := by
  rcases letter with ⟨side, lineage, inputOne, inputTwo⟩
  cases side <;> simp [ProfiledOpenPhysicalStrictLetter.round]

/-- Physical rounds represented by a strict history. -/
def profiledOpenPhysicalStrictHistoryRounds
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂))) : List (EnvironmentRound In₁ In₂) :=
  history.map ProfiledOpenPhysicalStrictLetter.round

/-- No simultaneous round occurs in the image of a strict history. -/
theorem closingRound_not_mem_profiledOpenPhysicalStrictHistoryRounds
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    ({ inputOne := inputOne, inputTwo := inputTwo, graph := .both } :
        EnvironmentRound In₁ In₂) ∉
      profiledOpenPhysicalStrictHistoryRounds history := by
  intro hmem
  rw [profiledOpenPhysicalStrictHistoryRounds, List.mem_map] at hmem
  rcases hmem with ⟨letter, _hletter, heq⟩
  have hgraph := congrArg EnvironmentRound.graph heq
  exact letter.round_graph_ne_both (by simpa using hgraph)

/-- Exact obstruction to the proposed recut: two strict subhistories with an
intervening physical `.both` round cannot be represented by one history in
the current direction alphabet. -/
theorem no_strictHistory_groups_across_both
    (before after : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    ¬ ∃ grouped : List (ProfiledOpenPhysicalStrictLetter (I := I)
        (In₁ := In₁) (In₂ := In₂)),
      profiledOpenPhysicalStrictHistoryRounds grouped =
        profiledOpenPhysicalStrictHistoryRounds before ++
          [{ inputOne := inputOne, inputTwo := inputTwo, graph := .both }] ++
          profiledOpenPhysicalStrictHistoryRounds after := by
  rintro ⟨grouped, hgrouped⟩
  let closing : EnvironmentRound In₁ In₂ :=
    { inputOne := inputOne, inputTwo := inputTwo, graph := .both }
  have hclosingRight : closing ∈
      profiledOpenPhysicalStrictHistoryRounds before ++ [closing] ++
        profiledOpenPhysicalStrictHistoryRounds after := by
    simp [closing]
  have hclosingLeft : closing ∈
      profiledOpenPhysicalStrictHistoryRounds grouped := by
    rw [hgrouped]
    exact hclosingRight
  exact closingRound_not_mem_profiledOpenPhysicalStrictHistoryRounds
    (history := grouped) inputOne inputTwo hclosingLeft

end

end DetParityAutomaton

end DistributedSynthesis
