/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenViewClassWidth

/-!
# Finite equality pattern of profiled open-family children

The full successor source of a two-member open family has four proof-side
corners: an old member and its physical `first`/`both` row.  Width alone says
that one new blind-view class contains at most one row of each member.  For a
source-free belief transition we also need to know how membership in that
class is computed.

This file proves the exact model fact.  Provided the old family has one common
blind view, equality of two new blind views is equivalent to equality of the
old *opposite* views selected by their rows.  The equivalence is independent
of the length and contents of the intervening homogeneous block.  Therefore
the four-corner quotient is determined by a finite `2 x 2` equality pattern;
no exact history, selected leader, or orientation observation is needed in the
finite transition.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂]

/-! ## Equality under a common environment extension -/

omit [Inhabited In₁] [Inhabited In₂] in
/-- Exact equality of both local views is preserved when the same environment
word is played from two histories of one fixed strategy.  Outputs may differ,
but views are output-independent. -/
theorem currentViews_extendPrefix_eq_of_currentViews_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hone : currentView Proc.one left = currentView Proc.one right)
    (htwo : currentView Proc.two left = currentView Proc.two right)
    (envs : List (EnvironmentRound In₁ In₂)) :
    currentView Proc.one (extendPrefix strategy left envs) =
        currentView Proc.one (extendPrefix strategy right envs) ∧
      currentView Proc.two (extendPrefix strategy left envs) =
        currentView Proc.two (extendPrefix strategy right envs) := by
  induction envs using List.reverseRecOn with
  | nil => exact ⟨hone, htwo⟩
  | append_singleton envs env ih =>
      rw [extendPrefix_snoc, extendPrefix_snoc]
      obtain ⟨ihone, ihtwo⟩ := ih
      rcases env with ⟨inputOne, inputTwo, graph⟩
      cases graph <;>
        simp [currentView_one_append, currentView_two_append, nextRound,
          ihone, ihtwo]

/-! ## Row-selected old histories -/

/-- Old concrete history selected by one process-one family corner. -/
def procOneViewClassRowHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcOnePairedEntryRep strategy)
    (candidate : I × PairedEntryRow) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match candidate.2 with
  | .first => (entry candidate.1).leftHistory
  | .both => (entry candidate.1).bothHistory

/-- Mirror row-selected history. -/
def procTwoViewClassRowHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcTwoPairedEntryRep strategy)
    (candidate : I × PairedEntryRow) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match candidate.2 with
  | .first => (entry candidate.1).rightHistory
  | .both => (entry candidate.1).bothHistory

section
omit [Inhabited In₁] [Inhabited In₂]

/-- Every selected process-one row has the same blind view when the family
representatives do. -/
theorem procOneViewClassRowHistory_blind_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcOnePairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.one (entry left).leftHistory =
        currentView Proc.one (entry right).leftHistory)
    (left right : I × PairedEntryRow) :
    currentView Proc.one (procOneViewClassRowHistory entry left) =
      currentView Proc.one (procOneViewClassRowHistory entry right) := by
  rcases left with ⟨left, leftRow⟩
  rcases right with ⟨right, rightRow⟩
  cases leftRow <;> cases rightRow
  · exact hblind left right
  · exact (hblind left right).trans (entry right).view_eq
  · exact (entry left).view_eq.symm.trans (hblind left right)
  · exact (entry left).view_eq.symm.trans
      ((hblind left right).trans (entry right).view_eq)

/-- Process-two mirror. -/
theorem procTwoViewClassRowHistory_blind_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcTwoPairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.two (entry left).rightHistory =
        currentView Proc.two (entry right).rightHistory)
    (left right : I × PairedEntryRow) :
    currentView Proc.two (procTwoViewClassRowHistory entry left) =
      currentView Proc.two (procTwoViewClassRowHistory entry right) := by
  rcases left with ⟨left, leftRow⟩
  rcases right with ⟨right, rightRow⟩
  cases leftRow <;> cases rightRow
  · exact hblind left right
  · exact (hblind left right).trans (entry right).view_eq
  · exact (entry left).view_eq.symm.trans (hblind left right)
  · exact (entry left).view_eq.symm.trans
      ((hblind left right).trans (entry right).view_eq)

/-- Definitional view equation for a right-to-left child. -/
theorem procTwoViewClassChild_right_view
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (candidate : I × PairedEntryRow) :
    currentView Proc.two
        (procTwoViewClassChild strategy entry past input candidate).rightHistory =
      .recv
        (currentView Proc.two
          (extendPrefix strategy (procOneViewClassRowHistory entry candidate)
            (past.map rightEnvironment)))
        (.inr input.1)
        (currentView Proc.one
          (extendPrefix strategy (procOneViewClassRowHistory entry candidate)
            (past.map rightEnvironment)))
        (.inl input.2) := by
  rcases candidate with ⟨member, row⟩
  cases row <;>
    simp [procTwoViewClassChild, procOneViewClassRowHistory,
      procTwoFreshPair, currentView_two_append, nextRound]

/-- Definitional mirror view equation. -/
theorem procOneViewClassChild_left_view
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (candidate : I × PairedEntryRow) :
    currentView Proc.one
        (procOneViewClassChild strategy entry past input candidate).leftHistory =
      .recv
        (currentView Proc.one
          (extendPrefix strategy (procTwoViewClassRowHistory entry candidate)
            (past.map leftEnvironment)))
        (.inl input.1)
        (currentView Proc.two
          (extendPrefix strategy (procTwoViewClassRowHistory entry candidate)
            (past.map leftEnvironment)))
        (.inr input.2) := by
  rcases candidate with ⟨member, row⟩
  cases row <;>
    simp [procOneViewClassChild, procTwoViewClassRowHistory,
      procOneFreshPair, currentView_one_append, nextRound]

/-- Process-one view of the `right` row inside a fresh process-two child. -/
theorem procTwoViewClassChild_opposite_right_view
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (candidate : I × PairedEntryRow) :
    currentView Proc.one
        (procTwoViewClassChild strategy entry past input candidate).rightHistory =
      .noRecv
        (currentView Proc.one
          (extendPrefix strategy (procOneViewClassRowHistory entry candidate)
            (past.map rightEnvironment)))
        (.inl input.2) := by
  rcases candidate with ⟨member, row⟩
  cases row <;>
    simp [procTwoViewClassChild, procOneViewClassRowHistory,
      procTwoFreshPair, currentView_one_append, nextRound]

/-- Process-one view of the `both` row inside the same fresh child. -/
theorem procTwoViewClassChild_opposite_both_view
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (candidate : I × PairedEntryRow) :
    currentView Proc.one
        (procTwoViewClassChild strategy entry past input candidate).bothHistory =
      .recv
        (currentView Proc.one
          (extendPrefix strategy (procOneViewClassRowHistory entry candidate)
            (past.map rightEnvironment)))
        (.inl input.2)
        (currentView Proc.two
          (extendPrefix strategy (procOneViewClassRowHistory entry candidate)
            (past.map rightEnvironment)))
        (.inr input.1) := by
  rcases candidate with ⟨member, row⟩
  cases row <;>
    simp [procTwoViewClassChild, procOneViewClassRowHistory,
      procTwoFreshPair, currentView_one_append, nextRound]

/-- Mirror opposite `left`-row view. -/
theorem procOneViewClassChild_opposite_left_view
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (candidate : I × PairedEntryRow) :
    currentView Proc.two
        (procOneViewClassChild strategy entry past input candidate).leftHistory =
      .noRecv
        (currentView Proc.two
          (extendPrefix strategy (procTwoViewClassRowHistory entry candidate)
            (past.map leftEnvironment)))
        (.inr input.2) := by
  rcases candidate with ⟨member, row⟩
  cases row <;>
    simp [procOneViewClassChild, procTwoViewClassRowHistory,
      procOneFreshPair, currentView_two_append, nextRound]

/-- Mirror opposite `both`-row view. -/
theorem procOneViewClassChild_opposite_both_view
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (candidate : I × PairedEntryRow) :
    currentView Proc.two
        (procOneViewClassChild strategy entry past input candidate).bothHistory =
      .recv
        (currentView Proc.two
          (extendPrefix strategy (procTwoViewClassRowHistory entry candidate)
            (past.map leftEnvironment)))
        (.inr input.2)
        (currentView Proc.one
          (extendPrefix strategy (procTwoViewClassRowHistory entry candidate)
            (past.map leftEnvironment)))
        (.inl input.1) := by
  rcases candidate with ⟨member, row⟩
  cases row <;>
    simp [procOneViewClassChild, procTwoViewClassRowHistory,
      procOneFreshPair, currentView_two_append, nextRound]

end

/-! ## Source-free equality of successor classes -/

omit [Inhabited In₁] [Inhabited In₂] in
/-- Right-to-left child equality is exactly old process-two equality.  The
homogeneous block cannot create or erase an equality once the common
process-one blind view is fixed. -/
theorem procTwoViewClassChild_view_eq_iff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.one (entry left).leftHistory =
        currentView Proc.one (entry right).leftHistory)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (left right : I × PairedEntryRow) :
    currentView Proc.two
        (procTwoViewClassChild strategy entry past input left).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input right).rightHistory ↔
      currentView Proc.two (procOneViewClassRowHistory entry left) =
        currentView Proc.two (procOneViewClassRowHistory entry right) := by
  let leftHistory := procOneViewClassRowHistory entry left
  let rightHistory := procOneViewClassRowHistory entry right
  have hone : currentView Proc.one leftHistory =
      currentView Proc.one rightHistory :=
    procOneViewClassRowHistory_blind_eq entry hblind left right
  constructor
  · intro hchild
    by_contra hold
    have hbaseNe := procTwo_ne_preserved_by_right_extension strategy
      leftHistory rightHistory hold past
    rw [procTwoViewClassChild_right_view strategy entry past input left,
      procTwoViewClassChild_right_view strategy entry past input right] at hchild
    apply hbaseNe
    simpa [leftHistory, rightHistory] using (View.recv.inj hchild).1
  · intro htwo
    have hbase := currentViews_extendPrefix_eq_of_currentViews_eq strategy
      leftHistory rightHistory hone htwo (past.map rightEnvironment)
    have hbaseOne :
        currentView Proc.one
            (extendPrefix strategy (procOneViewClassRowHistory entry left)
              (past.map rightEnvironment)) =
          currentView Proc.one
            (extendPrefix strategy (procOneViewClassRowHistory entry right)
              (past.map rightEnvironment)) := by
      simpa [leftHistory, rightHistory] using hbase.1
    have hbaseTwo :
        currentView Proc.two
            (extendPrefix strategy (procOneViewClassRowHistory entry left)
              (past.map rightEnvironment)) =
          currentView Proc.two
            (extendPrefix strategy (procOneViewClassRowHistory entry right)
              (past.map rightEnvironment)) := by
      simpa [leftHistory, rightHistory] using hbase.2
    rw [procTwoViewClassChild_right_view strategy entry past input left,
      procTwoViewClassChild_right_view strategy entry past input right,
      hbaseOne, hbaseTwo]

omit [Inhabited In₁] [Inhabited In₂] in
/-- Left-to-right mirror. -/
theorem procOneViewClassChild_view_eq_iff
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.two (entry left).rightHistory =
        currentView Proc.two (entry right).rightHistory)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (left right : I × PairedEntryRow) :
    currentView Proc.one
        (procOneViewClassChild strategy entry past input left).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input right).leftHistory ↔
      currentView Proc.one (procTwoViewClassRowHistory entry left) =
        currentView Proc.one (procTwoViewClassRowHistory entry right) := by
  let leftHistory := procTwoViewClassRowHistory entry left
  let rightHistory := procTwoViewClassRowHistory entry right
  have htwo : currentView Proc.two leftHistory =
      currentView Proc.two rightHistory :=
    procTwoViewClassRowHistory_blind_eq entry hblind left right
  constructor
  · intro hchild
    by_contra hold
    have hbaseNe := procOne_ne_preserved_by_left_extension strategy
      leftHistory rightHistory hold past
    rw [procOneViewClassChild_left_view strategy entry past input left,
      procOneViewClassChild_left_view strategy entry past input right] at hchild
    apply hbaseNe
    simpa [leftHistory, rightHistory] using (View.recv.inj hchild).1
  · intro hone
    have hbase := currentViews_extendPrefix_eq_of_currentViews_eq strategy
      leftHistory rightHistory hone htwo (past.map leftEnvironment)
    have hbaseOne :
        currentView Proc.one
            (extendPrefix strategy (procTwoViewClassRowHistory entry left)
              (past.map leftEnvironment)) =
          currentView Proc.one
            (extendPrefix strategy (procTwoViewClassRowHistory entry right)
              (past.map leftEnvironment)) := by
      simpa [leftHistory, rightHistory] using hbase.1
    have hbaseTwo :
        currentView Proc.two
            (extendPrefix strategy (procTwoViewClassRowHistory entry left)
              (past.map leftEnvironment)) =
          currentView Proc.two
            (extendPrefix strategy (procTwoViewClassRowHistory entry right)
              (past.map leftEnvironment)) := by
      simpa [leftHistory, rightHistory] using hbase.2
    rw [procOneViewClassChild_left_view strategy entry past input left,
      procOneViewClassChild_left_view strategy entry past input right,
      hbaseOne, hbaseTwo]

/-! ## The equality pattern resets after a handoff -/

omit [Inhabited In₁] [Inhabited In₂] in
/-- Once two fresh process-two children lie in the same new blind-view class,
their opposite views have the constant row pattern: `right` matches `right`,
`both` matches `both`, and the two rows never cross. -/
theorem procTwoViewClassChild_opposite_view_eq_iff_row_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (left right : I × PairedEntryRow)
    (hclass :
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input left).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input right).rightHistory)
    (leftRow rightRow : PairedEntryRow) :
    currentView Proc.one
        (match leftRow with
        | .first =>
            (procTwoViewClassChild strategy entry past input left).rightHistory
        | .both =>
            (procTwoViewClassChild strategy entry past input left).bothHistory) =
      currentView Proc.one
        (match rightRow with
        | .first =>
            (procTwoViewClassChild strategy entry past input right).rightHistory
        | .both =>
            (procTwoViewClassChild strategy entry past input right).bothHistory) ↔
      leftRow = rightRow := by
  rw [procTwoViewClassChild_right_view strategy entry past input left,
    procTwoViewClassChild_right_view strategy entry past input right] at hclass
  have hbaseTwo := (View.recv.inj hclass).1
  have hbaseOne := (View.recv.inj hclass).2.2.1
  cases leftRow <;> cases rightRow
  · rw [procTwoViewClassChild_opposite_right_view strategy entry past input left,
      procTwoViewClassChild_opposite_right_view strategy entry past input right,
      hbaseOne]
    simp
  · rw [procTwoViewClassChild_opposite_right_view strategy entry past input left,
      procTwoViewClassChild_opposite_both_view strategy entry past input right]
    simp
  · rw [procTwoViewClassChild_opposite_both_view strategy entry past input left,
      procTwoViewClassChild_opposite_right_view strategy entry past input right]
    simp
  · rw [procTwoViewClassChild_opposite_both_view strategy entry past input left,
      procTwoViewClassChild_opposite_both_view strategy entry past input right,
      hbaseOne, hbaseTwo]
    simp

omit [Inhabited In₁] [Inhabited In₂] in
/-- Left-to-right reset mirror. -/
theorem procOneViewClassChild_opposite_view_eq_iff_row_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (left right : I × PairedEntryRow)
    (hclass :
      currentView Proc.one
          (procOneViewClassChild strategy entry past input left).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input right).leftHistory)
    (leftRow rightRow : PairedEntryRow) :
    currentView Proc.two
        (match leftRow with
        | .first =>
            (procOneViewClassChild strategy entry past input left).leftHistory
        | .both =>
            (procOneViewClassChild strategy entry past input left).bothHistory) =
      currentView Proc.two
        (match rightRow with
        | .first =>
            (procOneViewClassChild strategy entry past input right).leftHistory
        | .both =>
            (procOneViewClassChild strategy entry past input right).bothHistory) ↔
      leftRow = rightRow := by
  rw [procOneViewClassChild_left_view strategy entry past input left,
    procOneViewClassChild_left_view strategy entry past input right] at hclass
  have hbaseOne := (View.recv.inj hclass).1
  have hbaseTwo := (View.recv.inj hclass).2.2.1
  cases leftRow <;> cases rightRow
  · rw [procOneViewClassChild_opposite_left_view strategy entry past input left,
      procOneViewClassChild_opposite_left_view strategy entry past input right,
      hbaseTwo]
    simp
  · rw [procOneViewClassChild_opposite_left_view strategy entry past input left,
      procOneViewClassChild_opposite_both_view strategy entry past input right]
    simp
  · rw [procOneViewClassChild_opposite_both_view strategy entry past input left,
      procOneViewClassChild_opposite_left_view strategy entry past input right]
    simp
  · rw [procOneViewClassChild_opposite_both_view strategy entry past input left,
      procOneViewClassChild_opposite_both_view strategy entry past input right,
      hbaseTwo, hbaseOne]
    simp

end

end


end DetParityAutomaton

end DistributedSynthesis
