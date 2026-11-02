/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSiblingInstallAudit

/-!
# Raw-strategy initial-output coherence

This file isolates the model fact needed before any finite-table extraction.
For a blind sender, equality of the sender's current local view determines
the complete sender strategy.  For a receiver, the next receive view contains
both old local views, so equality of both old views determines the initial
receiver output.

The statements are about literal paired-entry representatives of one fixed
raw strategy.  They do not assume coherence of already extracted tables.
-/

namespace DistributedSynthesis

universe i j u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## The literal history selected by a receiver row -/

/-- History underlying one row of a process-one paired entry. -/
def procOnePairedEntryRowHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) (row : PairedEntryRow) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match row with
  | .first => entry.leftHistory
  | .both => entry.bothHistory

/-- History underlying one row of a process-two paired entry. -/
def procTwoPairedEntryRowHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) (row : PairedEntryRow) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match row with
  | .first => entry.rightHistory
  | .both => entry.bothHistory

/-! ## Proof-side fresh-child provenance -/

/-- A literal process-two entry together with the data showing that it is a
fresh right-to-left child of the raw strategy.  The witness is proof-side;
none of its index, row, past, or orientation data is an input of a process. -/
structure ProcTwoViewClassChildProvenance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (child : ProcTwoPairedEntryRep strategy) where
  Index : Type i
  entry : Index → ProcOnePairedEntryRep strategy
  past : List (In₂ × In₁)
  input : In₂ × In₁
  candidate : Index × PairedEntryRow
  child_eq : child =
    procTwoViewClassChild strategy entry past input candidate

/-- Fresh left-to-right process-one provenance. -/
structure ProcOneViewClassChildProvenance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (child : ProcOnePairedEntryRep strategy) where
  Index : Type i
  entry : Index → ProcTwoPairedEntryRep strategy
  past : List (In₁ × In₂)
  input : In₁ × In₂
  candidate : Index × PairedEntryRow
  child_eq : child =
    procOneViewClassChild strategy entry past input candidate

/-! ## Fresh-child view inversion -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂]

/-- Fully cross-state right-to-left inversion.  The two fresh children may
come from different finite families, different homogeneous pasts, and
different closing inputs.  Equality of their receiving process-two views
recovers both immediately preceding views and the complete closing input. -/
theorem procTwoViewClassChildren_preReceiveData_eq_of_view_eq
    {I : Type i} {J : Type j}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (leftEntry : I → ProcOnePairedEntryRep strategy)
    (rightEntry : J → ProcOnePairedEntryRep strategy)
    (leftPast : List (In₂ × In₁)) (rightPast : List (In₂ × In₁))
    (leftInput rightInput : In₂ × In₁)
    (left : I × PairedEntryRow) (right : J × PairedEntryRow)
    (hview :
      currentView Proc.two
          (procTwoViewClassChild strategy leftEntry leftPast leftInput left
            ).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy rightEntry rightPast rightInput right
            ).rightHistory) :
    currentView Proc.one
          (extendPrefix strategy (procOneViewClassRowHistory leftEntry left)
            (leftPast.map rightEnvironment)) =
        currentView Proc.one
          (extendPrefix strategy (procOneViewClassRowHistory rightEntry right)
            (rightPast.map rightEnvironment)) ∧
      currentView Proc.two
          (extendPrefix strategy (procOneViewClassRowHistory leftEntry left)
            (leftPast.map rightEnvironment)) =
        currentView Proc.two
          (extendPrefix strategy (procOneViewClassRowHistory rightEntry right)
            (rightPast.map rightEnvironment)) ∧
      leftInput = rightInput := by
  rw [procTwoViewClassChild_right_view strategy leftEntry leftPast leftInput left,
    procTwoViewClassChild_right_view strategy rightEntry rightPast rightInput
      right] at hview
  have hrecv := View.recv.inj hview
  refine ⟨hrecv.2.2.1, hrecv.1, ?_⟩
  apply Prod.ext
  · exact PSum.inr.inj hrecv.2.1
  · exact PSum.inl.inj hrecv.2.2.2

/-- Fully cross-state left-to-right inversion. -/
theorem procOneViewClassChildren_preReceiveData_eq_of_view_eq
    {I : Type i} {J : Type j}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (leftEntry : I → ProcTwoPairedEntryRep strategy)
    (rightEntry : J → ProcTwoPairedEntryRep strategy)
    (leftPast : List (In₁ × In₂)) (rightPast : List (In₁ × In₂))
    (leftInput rightInput : In₁ × In₂)
    (left : I × PairedEntryRow) (right : J × PairedEntryRow)
    (hview :
      currentView Proc.one
          (procOneViewClassChild strategy leftEntry leftPast leftInput left
            ).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy rightEntry rightPast rightInput right
            ).leftHistory) :
    currentView Proc.one
          (extendPrefix strategy (procTwoViewClassRowHistory leftEntry left)
            (leftPast.map leftEnvironment)) =
        currentView Proc.one
          (extendPrefix strategy (procTwoViewClassRowHistory rightEntry right)
            (rightPast.map leftEnvironment)) ∧
      currentView Proc.two
          (extendPrefix strategy (procTwoViewClassRowHistory leftEntry left)
            (leftPast.map leftEnvironment)) =
        currentView Proc.two
          (extendPrefix strategy (procTwoViewClassRowHistory rightEntry right)
            (rightPast.map leftEnvironment)) ∧
      leftInput = rightInput := by
  rw [procOneViewClassChild_left_view strategy leftEntry leftPast leftInput left,
    procOneViewClassChild_left_view strategy rightEntry rightPast rightInput
      right] at hview
  have hrecv := View.recv.inj hview
  refine ⟨hrecv.1, hrecv.2.2.1, ?_⟩
  apply Prod.ext
  · exact PSum.inl.inj hrecv.2.1
  · exact PSum.inr.inj hrecv.2.2.2

/-- Cross-state same-row consequence for process-two children. -/
theorem procTwoViewClassChildren_row_currentViews_eq_of_view_eq
    {I : Type i} {J : Type j}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (leftEntry : I → ProcOnePairedEntryRep strategy)
    (rightEntry : J → ProcOnePairedEntryRep strategy)
    (leftPast : List (In₂ × In₁)) (rightPast : List (In₂ × In₁))
    (leftInput rightInput : In₂ × In₁)
    (left : I × PairedEntryRow) (right : J × PairedEntryRow)
    (hview :
      currentView Proc.two
          (procTwoViewClassChild strategy leftEntry leftPast leftInput left
            ).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy rightEntry rightPast rightInput right
            ).rightHistory)
    (row : PairedEntryRow) :
    currentView Proc.one
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy leftEntry leftPast leftInput left)
            row) =
        currentView Proc.one
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy rightEntry rightPast rightInput right)
            row) ∧
      currentView Proc.two
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy leftEntry leftPast leftInput left)
            row) =
        currentView Proc.two
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy rightEntry rightPast rightInput right)
            row) := by
  have hpre := procTwoViewClassChildren_preReceiveData_eq_of_view_eq
    leftEntry rightEntry leftPast rightPast leftInput rightInput left right hview
  cases row with
  | first =>
      exact ⟨by
          simp only [procTwoPairedEntryRowHistory]
          rw [procTwoViewClassChild_opposite_right_view strategy leftEntry
              leftPast leftInput left,
            procTwoViewClassChild_opposite_right_view strategy rightEntry
              rightPast rightInput right,
            hpre.1, hpre.2.2],
        by simpa [procTwoPairedEntryRowHistory] using hview⟩
  | both =>
      exact ⟨by
          simp only [procTwoPairedEntryRowHistory]
          rw [procTwoViewClassChild_opposite_both_view strategy leftEntry
              leftPast leftInput left,
            procTwoViewClassChild_opposite_both_view strategy rightEntry
              rightPast rightInput right,
            hpre.1, hpre.2.1, hpre.2.2],
        by
          exact
            (procTwoViewClassChild strategy leftEntry leftPast leftInput left
              ).view_eq.symm.trans
              (hview.trans
                (procTwoViewClassChild strategy rightEntry rightPast rightInput
                  right).view_eq)⟩

/-- Cross-state same-row process-one mirror. -/
theorem procOneViewClassChildren_row_currentViews_eq_of_view_eq
    {I : Type i} {J : Type j}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (leftEntry : I → ProcTwoPairedEntryRep strategy)
    (rightEntry : J → ProcTwoPairedEntryRep strategy)
    (leftPast : List (In₁ × In₂)) (rightPast : List (In₁ × In₂))
    (leftInput rightInput : In₁ × In₂)
    (left : I × PairedEntryRow) (right : J × PairedEntryRow)
    (hview :
      currentView Proc.one
          (procOneViewClassChild strategy leftEntry leftPast leftInput left
            ).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy rightEntry rightPast rightInput right
            ).leftHistory)
    (row : PairedEntryRow) :
    currentView Proc.one
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy leftEntry leftPast leftInput left)
            row) =
        currentView Proc.one
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy rightEntry rightPast rightInput right)
            row) ∧
      currentView Proc.two
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy leftEntry leftPast leftInput left)
            row) =
        currentView Proc.two
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy rightEntry rightPast rightInput right)
            row) := by
  have hpre := procOneViewClassChildren_preReceiveData_eq_of_view_eq
    leftEntry rightEntry leftPast rightPast leftInput rightInput left right hview
  cases row with
  | first =>
      exact ⟨by simpa [procOnePairedEntryRowHistory] using hview,
        by
          simp only [procOnePairedEntryRowHistory]
          rw [procOneViewClassChild_opposite_left_view strategy leftEntry
              leftPast leftInput left,
            procOneViewClassChild_opposite_left_view strategy rightEntry
              rightPast rightInput right,
            hpre.2.1, hpre.2.2]⟩
  | both =>
      exact ⟨by
          exact
            (procOneViewClassChild strategy leftEntry leftPast leftInput left
              ).view_eq.symm.trans
              (hview.trans
                (procOneViewClassChild strategy rightEntry rightPast rightInput
                  right).view_eq),
        by
          simp only [procOnePairedEntryRowHistory]
          rw [procOneViewClassChild_opposite_both_view strategy leftEntry
              leftPast leftInput left,
            procOneViewClassChild_opposite_both_view strategy rightEntry
              rightPast rightInput right,
            hpre.2.1, hpre.1, hpre.2.2]⟩

/-- Equality of the receiving process-two views of two fresh right-to-left
children exposes equality of *both* local views immediately before the
closing receive.  This is the strong inversion hidden inside
`procTwoViewClassChild_view_eq_iff`: no common-family or blind-view premise is
needed for this direction. -/
theorem procTwoViewClassChild_preReceiveViews_eq_of_view_eq
    {I : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (left right : I × PairedEntryRow)
    (hview :
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input left).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input right).rightHistory) :
    currentView Proc.one
          (extendPrefix strategy (procOneViewClassRowHistory entry left)
            (past.map rightEnvironment)) =
        currentView Proc.one
          (extendPrefix strategy (procOneViewClassRowHistory entry right)
            (past.map rightEnvironment)) ∧
      currentView Proc.two
          (extendPrefix strategy (procOneViewClassRowHistory entry left)
            (past.map rightEnvironment)) =
        currentView Proc.two
          (extendPrefix strategy (procOneViewClassRowHistory entry right)
            (past.map rightEnvironment)) := by
  rw [procTwoViewClassChild_right_view strategy entry past input left,
    procTwoViewClassChild_right_view strategy entry past input right] at hview
  exact ⟨(View.recv.inj hview).2.2.1, (View.recv.inj hview).1⟩

/-- Left-to-right mirror of fresh-child receive inversion. -/
theorem procOneViewClassChild_preReceiveViews_eq_of_view_eq
    {I : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (left right : I × PairedEntryRow)
    (hview :
      currentView Proc.one
          (procOneViewClassChild strategy entry past input left).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input right).leftHistory) :
    currentView Proc.one
          (extendPrefix strategy (procTwoViewClassRowHistory entry left)
            (past.map leftEnvironment)) =
        currentView Proc.one
          (extendPrefix strategy (procTwoViewClassRowHistory entry right)
            (past.map leftEnvironment)) ∧
      currentView Proc.two
          (extendPrefix strategy (procTwoViewClassRowHistory entry left)
            (past.map leftEnvironment)) =
        currentView Proc.two
          (extendPrefix strategy (procTwoViewClassRowHistory entry right)
            (past.map leftEnvironment)) := by
  rw [procOneViewClassChild_left_view strategy entry past input left,
    procOneViewClassChild_left_view strategy entry past input right] at hview
  exact ⟨(View.recv.inj hview).1, (View.recv.inj hview).2.2.1⟩

/-- Two fresh process-two children in one receiving-view class have equal
views for both processes at either common physical row.  This is the exact
pair of hypotheses required by the initial process-one receiver table. -/
theorem procTwoViewClassChild_row_currentViews_eq_of_view_eq
    {I : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (left right : I × PairedEntryRow)
    (hview :
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input left).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input right).rightHistory)
    (row : PairedEntryRow) :
    currentView Proc.one
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy entry past input left) row) =
        currentView Proc.one
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy entry past input right) row) ∧
      currentView Proc.two
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy entry past input left) row) =
        currentView Proc.two
          (procTwoPairedEntryRowHistory
            (procTwoViewClassChild strategy entry past input right) row) := by
  have hpre := procTwoViewClassChild_preReceiveViews_eq_of_view_eq
    entry past input left right hview
  cases row with
  | first =>
      exact ⟨by
          simp only [procTwoPairedEntryRowHistory]
          rw [procTwoViewClassChild_opposite_right_view strategy entry past input left,
            procTwoViewClassChild_opposite_right_view strategy entry past input right,
            hpre.1],
        by simpa [procTwoPairedEntryRowHistory] using hview⟩
  | both =>
      exact ⟨by
          simp only [procTwoPairedEntryRowHistory]
          rw [procTwoViewClassChild_opposite_both_view strategy entry past input left,
            procTwoViewClassChild_opposite_both_view strategy entry past input right,
            hpre.1, hpre.2],
        by
          exact (procTwoViewClassChild strategy entry past input left).view_eq.symm.trans
            (hview.trans
              (procTwoViewClassChild strategy entry past input right).view_eq)⟩

/-- Process-one fresh-child mirror. -/
theorem procOneViewClassChild_row_currentViews_eq_of_view_eq
    {I : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (left right : I × PairedEntryRow)
    (hview :
      currentView Proc.one
          (procOneViewClassChild strategy entry past input left).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input right).leftHistory)
    (row : PairedEntryRow) :
    currentView Proc.one
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy entry past input left) row) =
        currentView Proc.one
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy entry past input right) row) ∧
      currentView Proc.two
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy entry past input left) row) =
        currentView Proc.two
          (procOnePairedEntryRowHistory
            (procOneViewClassChild strategy entry past input right) row) := by
  have hpre := procOneViewClassChild_preReceiveViews_eq_of_view_eq
    entry past input left right hview
  cases row with
  | first =>
      exact ⟨by simpa [procOnePairedEntryRowHistory] using hview,
        by
          simp only [procOnePairedEntryRowHistory]
          rw [procOneViewClassChild_opposite_left_view strategy entry past input left,
            procOneViewClassChild_opposite_left_view strategy entry past input right,
            hpre.2]⟩
  | both =>
      exact ⟨by
          exact (procOneViewClassChild strategy entry past input left).view_eq.symm.trans
            (hview.trans
              (procOneViewClassChild strategy entry past input right).view_eq),
        by
          simp only [procOnePairedEntryRowHistory]
          rw [procOneViewClassChild_opposite_both_view strategy entry past input left,
            procOneViewClassChild_opposite_both_view strategy entry past input right,
            hpre.2, hpre.1]⟩

end

/-! ## Blind-sender projections -/

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Equal process-one entry views give equal initial right-block sender
outputs.  This is the raw semantic source of the first component of
`ProfiledOpenIndexedProcessOneInitialOutputCoherent`. -/
theorem procOnePairedEntry_blindInitialOutput_eq_of_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : ProcOnePairedEntryRep strategy)
    (hview : currentView Proc.one left.leftHistory =
      currentView Proc.one right.leftHistory)
    (inputOne : In₁) :
    left.lambdaOfStrategy.blind [] inputOne =
      right.lambdaOfStrategy.blind [] inputOne := by
  change blockSenderOne strategy left.leftHistory [] inputOne =
    blockSenderOne strategy right.leftHistory [] inputOne
  rw [blockSenderOne_eq_of_view_eq strategy hview]

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process-two blind-sender mirror. -/
theorem procTwoPairedEntry_blindInitialOutput_eq_of_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : ProcTwoPairedEntryRep strategy)
    (hview : currentView Proc.two left.rightHistory =
      currentView Proc.two right.rightHistory)
    (inputTwo : In₂) :
    left.lambdaOfStrategy.blind [] inputTwo =
      right.lambdaOfStrategy.blind [] inputTwo := by
  change blockSenderTwo strategy left.rightHistory [] inputTwo =
    blockSenderTwo strategy right.rightHistory [] inputTwo
  rw [blockSenderTwo_eq_of_view_eq strategy hview]

/-! ## Informed-receiver projections -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The process-one receiver restriction is extensional in both current
views at the first left-block round. -/
theorem blockReceiverOne_initial_eq_of_currentViews_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hone : currentView Proc.one left = currentView Proc.one right)
    (htwo : currentView Proc.two left = currentView Proc.two right)
    (inputOne : In₁) (inputTwo : In₂) :
    blockReceiverOne strategy left [] (inputOne, inputTwo) =
      blockReceiverOne strategy right [] (inputOne, inputTwo) := by
  apply congrArg strategy.one
  have hone' : (viewPair left).1 = (viewPair right).1 := by
    simpa [currentView] using hone
  have htwo' : (viewPair left).2 = (viewPair right).2 := by
    simpa [currentView] using htwo
  simp [blockReceiverOne, nextView, advanceViewsWithEnvironment, hone', htwo']

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process-two receiver mirror. -/
theorem blockReceiverTwo_initial_eq_of_currentViews_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hone : currentView Proc.one left = currentView Proc.one right)
    (htwo : currentView Proc.two left = currentView Proc.two right)
    (inputOne : In₁) (inputTwo : In₂) :
    blockReceiverTwo strategy left [] (inputTwo, inputOne) =
      blockReceiverTwo strategy right [] (inputTwo, inputOne) := by
  apply congrArg strategy.two
  have hone' : (viewPair left).1 = (viewPair right).1 := by
    simpa [currentView] using hone
  have htwo' : (viewPair left).2 = (viewPair right).2 := by
    simpa [currentView] using htwo
  simp [blockReceiverTwo, nextView, advanceViewsWithEnvironment, hone', htwo']

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Equal pairs of pre-receive views give equal process-one output on the
same initial left-block move.  The row chooses the literal `right` or `both`
representative before the receive. -/
theorem procTwoPairedEntry_leftReceiveInitialOutput_eq_of_currentViews_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : ProcTwoPairedEntryRep strategy) (row : PairedEntryRow)
    (hone : currentView Proc.one (procTwoPairedEntryRowHistory left row) =
      currentView Proc.one (procTwoPairedEntryRowHistory right row))
    (htwo : currentView Proc.two (procTwoPairedEntryRowHistory left row) =
      currentView Proc.two (procTwoPairedEntryRowHistory right row))
    (inputOne : In₁) (inputTwo : In₂) :
    pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A left.code left.lambdaOfStrategy []
          (inputOne, inputTwo)).physical =
      pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A right.code right.lambdaOfStrategy []
          (inputOne, inputTwo)).physical := by
  cases row with
  | first =>
      change blockReceiverOne strategy left.rightHistory []
          (inputOne, inputTwo) =
        blockReceiverOne strategy right.rightHistory [] (inputOne, inputTwo)
      exact blockReceiverOne_initial_eq_of_currentViews_eq strategy
        left.rightHistory right.rightHistory
        (by simpa [procTwoPairedEntryRowHistory] using hone)
        (by simpa [procTwoPairedEntryRowHistory] using htwo) inputOne inputTwo
  | both =>
      change blockReceiverOne strategy left.bothHistory []
          (inputOne, inputTwo) =
        blockReceiverOne strategy right.bothHistory [] (inputOne, inputTwo)
      exact blockReceiverOne_initial_eq_of_currentViews_eq strategy
        left.bothHistory right.bothHistory
        (by simpa [procTwoPairedEntryRowHistory] using hone)
        (by simpa [procTwoPairedEntryRowHistory] using htwo) inputOne inputTwo

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process-two receive mirror on an initial right-block move. -/
theorem procOnePairedEntry_rightReceiveInitialOutput_eq_of_currentViews_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : ProcOnePairedEntryRep strategy) (row : PairedEntryRow)
    (hone : currentView Proc.one (procOnePairedEntryRowHistory left row) =
      currentView Proc.one (procOnePairedEntryRowHistory right row))
    (htwo : currentView Proc.two (procOnePairedEntryRowHistory left row) =
      currentView Proc.two (procOnePairedEntryRowHistory right row))
    (inputOne : In₁) (inputTwo : In₂) :
    pairedRightInformedForRow row
        (profiledRightReceiverStrategy A left.code left.lambdaOfStrategy []
          (inputTwo, inputOne)).physical =
      pairedRightInformedForRow row
        (profiledRightReceiverStrategy A right.code right.lambdaOfStrategy []
          (inputTwo, inputOne)).physical := by
  cases row with
  | first =>
      change blockReceiverTwo strategy left.leftHistory []
          (inputTwo, inputOne) =
        blockReceiverTwo strategy right.leftHistory [] (inputTwo, inputOne)
      exact blockReceiverTwo_initial_eq_of_currentViews_eq strategy
        left.leftHistory right.leftHistory
        (by simpa [procOnePairedEntryRowHistory] using hone)
        (by simpa [procOnePairedEntryRowHistory] using htwo) inputOne inputTwo
  | both =>
      change blockReceiverTwo strategy left.bothHistory []
          (inputTwo, inputOne) =
        blockReceiverTwo strategy right.bothHistory [] (inputTwo, inputOne)
      exact blockReceiverTwo_initial_eq_of_currentViews_eq strategy
        left.bothHistory right.bothHistory
        (by simpa [procOnePairedEntryRowHistory] using hone)
        (by simpa [procOnePairedEntryRowHistory] using htwo) inputOne inputTwo

/-! ## Direct fresh-class consequences -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₂] in
/-- One process-two child-view class already makes the raw process-one
receiver's initial left-block output constant on every common physical row.
This is the model equality that a root-pinned finite-family extraction must
preserve. -/
theorem procTwoViewClassChild_leftReceiveInitialOutput_eq_of_view_eq
    {I : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (left right : I × PairedEntryRow)
    (hview :
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input left).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input right).rightHistory)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A
          (procTwoViewClassChild strategy entry past input left).code
          (procTwoViewClassChild strategy entry past input left).lambdaOfStrategy
          [] (inputOne, inputTwo)).physical =
      pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A
          (procTwoViewClassChild strategy entry past input right).code
          (procTwoViewClassChild strategy entry past input right).lambdaOfStrategy
          [] (inputOne, inputTwo)).physical := by
  have hrows := procTwoViewClassChild_row_currentViews_eq_of_view_eq
    entry past input left right hview row
  exact procTwoPairedEntry_leftReceiveInitialOutput_eq_of_currentViews_eq A
    _ _ row hrows.1 hrows.2 inputOne inputTwo

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] in
/-- Process-two raw receiver mirror. -/
theorem procOneViewClassChild_rightReceiveInitialOutput_eq_of_view_eq
    {I : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (left right : I × PairedEntryRow)
    (hview :
      currentView Proc.one
          (procOneViewClassChild strategy entry past input left).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input right).leftHistory)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedRightInformedForRow row
        (profiledRightReceiverStrategy A
          (procOneViewClassChild strategy entry past input left).code
          (procOneViewClassChild strategy entry past input left).lambdaOfStrategy
          [] (inputTwo, inputOne)).physical =
      pairedRightInformedForRow row
        (profiledRightReceiverStrategy A
          (procOneViewClassChild strategy entry past input right).code
          (procOneViewClassChild strategy entry past input right).lambdaOfStrategy
          [] (inputTwo, inputOne)).physical := by
  have hrows := procOneViewClassChild_row_currentViews_eq_of_view_eq
    entry past input left right hview row
  exact procOnePairedEntry_rightReceiveInitialOutput_eq_of_currentViews_eq A
    _ _ row hrows.1 hrows.2 inputOne inputTwo

/-! ## Fresh-provenance adapters -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₂] in
/-- For arbitrary process-two entries, one blind-view equality is enough for
receiver coherence precisely when both entries retain their literal
fresh-child provenance. -/
theorem procTwoPairedEntry_leftReceiveInitialOutput_eq_of_fresh_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : ProcTwoPairedEntryRep strategy)
    (leftFresh : ProcTwoViewClassChildProvenance strategy left)
    (rightFresh : ProcTwoViewClassChildProvenance strategy right)
    (hview : currentView Proc.two left.rightHistory =
      currentView Proc.two right.rightHistory)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A left.code left.lambdaOfStrategy []
          (inputOne, inputTwo)).physical =
      pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A right.code right.lambdaOfStrategy []
          (inputOne, inputTwo)).physical := by
  rcases leftFresh with
    ⟨leftIndex, leftEntry, leftPast, leftInput, leftCandidate, hleft⟩
  rcases rightFresh with
    ⟨rightIndex, rightEntry, rightPast, rightInput, rightCandidate, hright⟩
  subst left
  subst right
  have hrows := procTwoViewClassChildren_row_currentViews_eq_of_view_eq
    leftEntry rightEntry leftPast rightPast leftInput rightInput leftCandidate
      rightCandidate hview row
  exact procTwoPairedEntry_leftReceiveInitialOutput_eq_of_currentViews_eq A
    _ _ row hrows.1 hrows.2 inputOne inputTwo

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] in
/-- Fresh-provenance process-two receiver mirror. -/
theorem procOnePairedEntry_rightReceiveInitialOutput_eq_of_fresh_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : ProcOnePairedEntryRep strategy)
    (leftFresh : ProcOneViewClassChildProvenance strategy left)
    (rightFresh : ProcOneViewClassChildProvenance strategy right)
    (hview : currentView Proc.one left.leftHistory =
      currentView Proc.one right.leftHistory)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedRightInformedForRow row
        (profiledRightReceiverStrategy A left.code left.lambdaOfStrategy []
          (inputTwo, inputOne)).physical =
      pairedRightInformedForRow row
        (profiledRightReceiverStrategy A right.code right.lambdaOfStrategy []
          (inputTwo, inputOne)).physical := by
  rcases leftFresh with
    ⟨leftIndex, leftEntry, leftPast, leftInput, leftCandidate, hleft⟩
  rcases rightFresh with
    ⟨rightIndex, rightEntry, rightPast, rightInput, rightCandidate, hright⟩
  subst left
  subst right
  have hrows := procOneViewClassChildren_row_currentViews_eq_of_view_eq
    leftEntry rightEntry leftPast rightPast leftInput rightInput leftCandidate
      rightCandidate hview row
  exact procOnePairedEntry_rightReceiveInitialOutput_eq_of_currentViews_eq A
    _ _ row hrows.1 hrows.2 inputOne inputTwo

/-! ## The minimal two local-fibre adapters -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Concrete raw-strategy adapter for a process-one staged move.

`rightEntry` is the blind right-sender representative selected at a global
descriptor.  `leftEntry` is the process-two semantic member decoded at one
persistent lineage.  Equality inside the process-one fibre must expose the
right sender's exact view and the left child's fresh receiving view.  The
conclusion is exactly the two raw initial-output laws later preserved by
root-pinned extraction. -/
theorem profiledOpenProcessOneRawFibreInitialOutputCoherent
    {Global OneClass Lineage : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (classOf : Global → OneClass)
    (rightEntry : Global → ProcOnePairedEntryRep strategy)
    (leftEntry : Global → Lineage → ProcTwoPairedEntryRep strategy)
    (leftFresh : ∀ descriptor lineage,
      ProcTwoViewClassChildProvenance strategy (leftEntry descriptor lineage))
    (hrightView : ∀ left right, classOf left = classOf right →
      currentView Proc.one (rightEntry left).leftHistory =
        currentView Proc.one (rightEntry right).leftHistory)
    (hleftView : ∀ left right, classOf left = classOf right →
      ∀ lineage,
        currentView Proc.two (leftEntry left lineage).rightHistory =
          currentView Proc.two (leftEntry right lineage).rightHistory)
    (left right : Global) (hclass : classOf left = classOf right) :
    (∀ inputOne,
      (rightEntry left).lambdaOfStrategy.blind [] inputOne =
        (rightEntry right).lambdaOfStrategy.blind [] inputOne) ∧
      (∀ lineage row inputOne inputTwo,
        pairedLeftInformedForRow row
            (profiledLeftReceiverStrategy A (leftEntry left lineage).code
              (leftEntry left lineage).lambdaOfStrategy []
              (inputOne, inputTwo)).physical =
          pairedLeftInformedForRow row
            (profiledLeftReceiverStrategy A (leftEntry right lineage).code
              (leftEntry right lineage).lambdaOfStrategy []
              (inputOne, inputTwo)).physical) := by
  constructor
  · intro inputOne
    exact procOnePairedEntry_blindInitialOutput_eq_of_view_eq
      (rightEntry left) (rightEntry right) (hrightView left right hclass)
      inputOne
  · intro lineage row inputOne inputTwo
    exact procTwoPairedEntry_leftReceiveInitialOutput_eq_of_fresh_view_eq A
      (leftEntry left lineage) (leftEntry right lineage)
      (leftFresh left lineage) (leftFresh right lineage)
      (hleftView left right hclass lineage) row inputOne inputTwo

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process-two local-fibre mirror.  Again the two semantic view equalities
are proof-side fibre invariants, not an orientation or leader observation. -/
theorem profiledOpenProcessTwoRawFibreInitialOutputCoherent
    {Global TwoClass Lineage : Type i}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (classOf : Global → TwoClass)
    (leftEntry : Global → ProcTwoPairedEntryRep strategy)
    (rightEntry : Global → Lineage → ProcOnePairedEntryRep strategy)
    (rightFresh : ∀ descriptor lineage,
      ProcOneViewClassChildProvenance strategy (rightEntry descriptor lineage))
    (hleftView : ∀ left right, classOf left = classOf right →
      currentView Proc.two (leftEntry left).rightHistory =
        currentView Proc.two (leftEntry right).rightHistory)
    (hrightView : ∀ left right, classOf left = classOf right →
      ∀ lineage,
        currentView Proc.one (rightEntry left lineage).leftHistory =
          currentView Proc.one (rightEntry right lineage).leftHistory)
    (left right : Global) (hclass : classOf left = classOf right) :
    (∀ inputTwo,
      (leftEntry left).lambdaOfStrategy.blind [] inputTwo =
        (leftEntry right).lambdaOfStrategy.blind [] inputTwo) ∧
      (∀ lineage row inputOne inputTwo,
        pairedRightInformedForRow row
            (profiledRightReceiverStrategy A (rightEntry left lineage).code
              (rightEntry left lineage).lambdaOfStrategy []
              (inputTwo, inputOne)).physical =
          pairedRightInformedForRow row
            (profiledRightReceiverStrategy A (rightEntry right lineage).code
              (rightEntry right lineage).lambdaOfStrategy []
              (inputTwo, inputOne)).physical) := by
  constructor
  · intro inputTwo
    exact procTwoPairedEntry_blindInitialOutput_eq_of_view_eq
      (leftEntry left) (leftEntry right) (hleftView left right hclass)
      inputTwo
  · intro lineage row inputOne inputTwo
    exact procOnePairedEntry_rightReceiveInitialOutput_eq_of_fresh_view_eq A
      (rightEntry left lineage) (rightEntry right lineage)
      (rightFresh left lineage) (rightFresh right lineage)
      (hrightView left right hclass lineage) row inputOne inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
