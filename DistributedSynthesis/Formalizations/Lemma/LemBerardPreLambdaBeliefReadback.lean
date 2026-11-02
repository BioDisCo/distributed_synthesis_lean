/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBerardDirectRationalTreeReadback

/-!
# Belief readback after input-free Bérard rationalization

This file isolates the honest extra condition needed when the input-free
global action tree is rationalized *before* local lambda actions are
installed.  A finite tree control may identify two different occurrences.
The ordinary local belief construction subsequently intersects sets of such
controls at a receive.  That intersection can contain a control represented
on the two sides by two different histories, without one history realizing
both delivered views.

`BeliefOccurrenceCoverage` rules out exactly this false-intersection effect:
every control retained in a local belief has one genuine tree occurrence with
the current exact local view.  Under this condition, the already proved
synchronous exact-view pair safety makes each reachable belief output-uniform.
Thus ordinary input-free parity rationalization and lambda installation are
cleanly separated; the only model mathematics left between them is the named
coverage condition below.  No executable definition receives a graph,
orientation, active side, or strict-leader signal.
-/

namespace DistributedSynthesis

universe u v x y s c

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂]
variable [Inhabited Out₁] [Inhabited Out₂]

namespace BerardGlobalActionTree

variable (tree : BerardGlobalActionTree
  (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

/-- Every state retained in a local belief is represented by one genuine
occurrence of the rational tree with the same exact local view.  The two
clauses are deliberately separate: no process is assumed to know which side
is currently informed. -/
def BeliefOccurrenceCoverage : Prop :=
  (∀ (rounds : List (EnvironmentRound In₁ In₂)) state,
      state ∈ (tree.roundMachine.beliefsAfter rounds).1 →
        ∃ shadow : List (EnvironmentRound In₁ In₂),
          shadow.length = rounds.length ∧
            (exactViewsAfterEnvironmentPrefix shadow).1 =
              (exactViewsAfterEnvironmentPrefix rounds).1 ∧
            tree.roundMachine.stateAfter shadow = state) ∧
    (∀ (rounds : List (EnvironmentRound In₁ In₂)) state,
      state ∈ (tree.roundMachine.beliefsAfter rounds).2 →
        ∃ shadow : List (EnvironmentRound In₁ In₂),
          shadow.length = rounds.length ∧
            (exactViewsAfterEnvironmentPrefix shadow).2 =
              (exactViewsAfterEnvironmentPrefix rounds).2 ∧
            tree.roundMachine.stateAfter shadow = state)

omit [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁]
    [Inhabited In₂] in
/-- The tree-control coordinate of the finite round machine follows the
corresponding finite tree occurrence. -/
theorem stateAfter_fst (rounds : List (EnvironmentRound In₁ In₂)) :
    (tree.roundMachine.stateAfter rounds).1.down = tree.controlAt rounds := by
  induction rounds using List.reverseRecOn with
  | nil => rfl
  | append_singleton rounds round ih =>
      simp only [FiniteGlobalRoundMachine.stateAfter, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      change tree.step
          (tree.roundMachine.stateAfter rounds).1.down round = _
      rw [ih]
      simp [TransitionRationalTree.controlAt, List.foldl_append]

omit [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁]
    [Inhabited In₂] in
/-- The post-round state at a finite occurrence stores precisely the action
selected at that occurrence. -/
theorem stateAfter_snoc_outputs
    (rounds : List (EnvironmentRound In₁ In₂))
    (round : EnvironmentRound In₁ In₂) :
    (tree.outputOne (tree.roundMachine.stateAfter (rounds ++ [round])),
      tree.outputTwo (tree.roundMachine.stateAfter (rounds ++ [round]))) =
      tree.labeledTree rounds round := by
  simp only [FiniteGlobalRoundMachine.stateAfter, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  change
    ((tree.labelOf (tree.roundMachine.stateAfter rounds).1.down round).1,
      (tree.labelOf (tree.roundMachine.stateAfter rounds).1.down round).2) = _
  rw [tree.stateAfter_fst rounds]
  rfl

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁]
    [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
/-- Synchronous pair safety compares outputs at any two equal-depth
occurrences whose updated process-one exact views agree. -/
theorem outputOne_eq_of_selfProductSafe_of_length_eq
    (hsafe : ExactViewGlobalSelfProductSafe
      (exactViewGlobalSelfProduct tree.labeledTree))
    (left right : List (EnvironmentRound In₁ In₂))
    (leftRound rightRound : EnvironmentRound In₁ In₂)
    (hlength : left.length = right.length)
    (hview : (exactNextViews left leftRound).1 =
      (exactNextViews right rightRound).1) :
    (tree.labeledTree left leftRound).1 =
      (tree.labeledTree right rightRound).1 := by
  classical
  let paired := left.zip right
  have hfst : paired.map Prod.fst = left := by
    exact List.map_fst_zip (Nat.le_of_eq hlength)
  have hsnd : paired.map Prod.snd = right := by
    exact List.map_snd_zip (Nat.le_of_eq hlength.symm)
  have hsafety := (hsafe paired leftRound rightRound).1
  have hequal :
      (pairedViewEqualityStep (pairedViewEqualityAfter paired)
        leftRound rightRound).1 = true := by
    rw [pairedViewEqualityAfter_eq_exact]
    rw [hfst, hsnd]
    rw [← pairedViewEquality_advanceViewsWithEnvironment]
    change (if (advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix left) leftRound).1 =
          (advanceViewsWithEnvironment
            (exactViewsAfterEnvironmentPrefix right) rightRound).1
      then true else false) = true
    change
      (advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix left) leftRound).1 =
      (advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix right) rightRound).1 at hview
    rw [if_pos hview]
  simpa only [exactViewGlobalSelfProduct, hfst, hsnd] using hsafety hequal

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁]
    [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
/-- Process-two mirror of
`outputOne_eq_of_selfProductSafe_of_length_eq`. -/
theorem outputTwo_eq_of_selfProductSafe_of_length_eq
    (hsafe : ExactViewGlobalSelfProductSafe
      (exactViewGlobalSelfProduct tree.labeledTree))
    (left right : List (EnvironmentRound In₁ In₂))
    (leftRound rightRound : EnvironmentRound In₁ In₂)
    (hlength : left.length = right.length)
    (hview : (exactNextViews left leftRound).2 =
      (exactNextViews right rightRound).2) :
    (tree.labeledTree left leftRound).2 =
      (tree.labeledTree right rightRound).2 := by
  classical
  let paired := left.zip right
  have hfst : paired.map Prod.fst = left := by
    exact List.map_fst_zip (Nat.le_of_eq hlength)
  have hsnd : paired.map Prod.snd = right := by
    exact List.map_snd_zip (Nat.le_of_eq hlength.symm)
  have hsafety := (hsafe paired leftRound rightRound).2
  have hequal :
      (pairedViewEqualityStep (pairedViewEqualityAfter paired)
        leftRound rightRound).2 = true := by
    rw [pairedViewEqualityAfter_eq_exact]
    rw [hfst, hsnd]
    rw [← pairedViewEquality_advanceViewsWithEnvironment]
    change (if (advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix left) leftRound).2 =
          (advanceViewsWithEnvironment
            (exactViewsAfterEnvironmentPrefix right) rightRound).2
      then true else false) = true
    change
      (advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix left) leftRound).2 =
      (advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix right) rightRound).2 at hview
    rw [if_pos hview]
  simpa only [exactViewGlobalSelfProduct, hfst, hsnd] using hsafety hequal

omit [Inhabited In₁] [Inhabited In₂] in
/-- The fail-fast positive adapter: a rational input-free tree with the
finite pair test and genuine occurrence coverage has output-uniform reachable
beliefs, so its lambda actions can be read back by the existing finite belief
summary. -/
theorem reachableBeliefsUniform_of_selfProductSafe_of_occurrenceCoverage
    (hsafe : ExactViewGlobalSelfProductSafe
      (exactViewGlobalSelfProduct tree.labeledTree))
    (hcoverage : BeliefOccurrenceCoverage tree) :
    tree.roundMachine.ReachableBeliefsUniform tree.outputOne tree.outputTwo := by
  intro rounds
  cases rounds using List.reverseRecOn with
  | nil =>
      constructor <;>
        intro left hleft right hright <;>
        simp [FiniteGlobalRoundMachine.beliefsAfter] at hleft hright <;>
        subst left <;> subst right <;> rfl
  | append_singleton rounds round =>
      constructor
      · intro left hleft right hright
        obtain ⟨leftRounds, hleftLength, hleftView, hleftState⟩ :=
          hcoverage.1 (rounds ++ [round]) left hleft
        obtain ⟨rightRounds, hrightLength, hrightView, hrightState⟩ :=
          hcoverage.1 (rounds ++ [round]) right hright
        have hleftNonempty : leftRounds ≠ [] := by
          intro hnil
          subst leftRounds
          simp at hleftLength
        have hrightNonempty : rightRounds ≠ [] := by
          intro hnil
          subst rightRounds
          simp at hrightLength
        let leftPrefix := leftRounds.dropLast
        let leftRound := leftRounds.getLast hleftNonempty
        let rightPrefix := rightRounds.dropLast
        let rightRound := rightRounds.getLast hrightNonempty
        have hleftSplit : leftPrefix ++ [leftRound] = leftRounds :=
          List.dropLast_append_getLast hleftNonempty
        have hrightSplit : rightPrefix ++ [rightRound] = rightRounds :=
          List.dropLast_append_getLast hrightNonempty
        have hprefixLength : leftPrefix.length = rightPrefix.length := by
          simp only [leftPrefix, rightPrefix, List.length_dropLast]
          omega
        have hnextView :
            (exactNextViews leftPrefix leftRound).1 =
              (exactNextViews rightPrefix rightRound).1 := by
          change
            (advanceViewsWithEnvironment
              (exactViewsAfterEnvironmentPrefix leftPrefix) leftRound).1 =
            (advanceViewsWithEnvironment
              (exactViewsAfterEnvironmentPrefix rightPrefix) rightRound).1
          rw [← exactViewsAfterEnvironmentPrefix_snoc,
            ← exactViewsAfterEnvironmentPrefix_snoc]
          rw [hleftSplit, hrightSplit, hleftView, hrightView]
        rw [← hleftState, ← hrightState, ← hleftSplit, ← hrightSplit]
        have houtputs := tree.outputOne_eq_of_selfProductSafe_of_length_eq
          hsafe leftPrefix rightPrefix leftRound rightRound hprefixLength hnextView
        have hleftOutput := congrArg Prod.fst
          (tree.stateAfter_snoc_outputs leftPrefix leftRound)
        have hrightOutput := congrArg Prod.fst
          (tree.stateAfter_snoc_outputs rightPrefix rightRound)
        exact hleftOutput.trans (houtputs.trans hrightOutput.symm)
      · intro left hleft right hright
        obtain ⟨leftRounds, hleftLength, hleftView, hleftState⟩ :=
          hcoverage.2 (rounds ++ [round]) left hleft
        obtain ⟨rightRounds, hrightLength, hrightView, hrightState⟩ :=
          hcoverage.2 (rounds ++ [round]) right hright
        have hleftNonempty : leftRounds ≠ [] := by
          intro hnil
          subst leftRounds
          simp at hleftLength
        have hrightNonempty : rightRounds ≠ [] := by
          intro hnil
          subst rightRounds
          simp at hrightLength
        let leftPrefix := leftRounds.dropLast
        let leftRound := leftRounds.getLast hleftNonempty
        let rightPrefix := rightRounds.dropLast
        let rightRound := rightRounds.getLast hrightNonempty
        have hleftSplit : leftPrefix ++ [leftRound] = leftRounds :=
          List.dropLast_append_getLast hleftNonempty
        have hrightSplit : rightPrefix ++ [rightRound] = rightRounds :=
          List.dropLast_append_getLast hrightNonempty
        have hprefixLength : leftPrefix.length = rightPrefix.length := by
          simp only [leftPrefix, rightPrefix, List.length_dropLast]
          omega
        have hnextView :
            (exactNextViews leftPrefix leftRound).2 =
              (exactNextViews rightPrefix rightRound).2 := by
          change
            (advanceViewsWithEnvironment
              (exactViewsAfterEnvironmentPrefix leftPrefix) leftRound).2 =
            (advanceViewsWithEnvironment
              (exactViewsAfterEnvironmentPrefix rightPrefix) rightRound).2
          rw [← exactViewsAfterEnvironmentPrefix_snoc,
            ← exactViewsAfterEnvironmentPrefix_snoc]
          rw [hleftSplit, hrightSplit, hleftView, hrightView]
        rw [← hleftState, ← hrightState, ← hleftSplit, ← hrightSplit]
        have houtputs := tree.outputTwo_eq_of_selfProductSafe_of_length_eq
          hsafe leftPrefix rightPrefix leftRound rightRound hprefixLength hnextView
        have hleftOutput := congrArg Prod.snd
          (tree.stateAfter_snoc_outputs leftPrefix leftRound)
        have hrightOutput := congrArg Prod.snd
          (tree.stateAfter_snoc_outputs rightPrefix rightRound)
        exact hleftOutput.trans (houtputs.trans hrightOutput.symm)

end BerardGlobalActionTree

/-- The clean Bérard-style extraction target for rationalizing before lambda
installation.  The first two fields are exactly the input-free global parity
and synchronous local-consistency tests.  `BeliefOccurrenceCoverage` is the
single extra source-correlation law needed to install finite local actions
afterward. -/
def BerardPreLambdaRationalTreeExtraction
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy environment)) →
      ∃ tree : TransitionRationalTree.{max u v, max u v x y, c}
          (EnvironmentRound In₁ In₂)
          (ExactViewGlobalActionTable
            (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
        ExactViewGlobalTreeWinning A tree.labeledTree ∧
          ExactViewGlobalSelfProductSafe
            (exactViewGlobalSelfProduct tree.labeledTree) ∧
          BerardGlobalActionTree.BeliefOccurrenceCoverage tree

omit [Inhabited In₁] [Inhabited In₂] in
/-- The pre-lambda rationalization target yields the finite global belief
machine directly; no separately supplied local presentation is necessary. -/
theorem perStrategyWinningFiniteGlobalBeliefMachine_of_berardPreLambda
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (fallback : LocalSummaryAutomaton.{u, v, max c x y} In₁ In₂)
    (hextract : BerardPreLambdaRationalTreeExtraction.{u, v, x, y, s, c} A) :
    PerStrategyWinningFiniteGlobalBeliefMachine A fallback := by
  unfold BerardPreLambdaRationalTreeExtraction at hextract
  intro strategy hstrategy
  obtain ⟨tree, hwins, hsafe, hcoverage⟩ := hextract strategy hstrategy
  refine ⟨BerardGlobalActionTree.roundMachine tree,
    BerardGlobalActionTree.outputOne tree,
    BerardGlobalActionTree.outputTwo tree, ?_, ?_⟩
  · exact
      BerardGlobalActionTree.reachableBeliefsUniform_of_selfProductSafe_of_occurrenceCoverage
        tree hsafe hcoverage
  · exact BerardGlobalActionTree.globalMachine_accepts tree A hwins

omit [Inhabited In₁] [Inhabited In₂] in
/-- Direct unconditional-theorem handoff for the independent Bérard route.
The sole mathematical extraction premise is
`BerardPreLambdaRationalTreeExtraction`. -/
theorem exists_readbackUpgrade_of_berardPreLambda
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (fallback : LocalSummaryAutomaton.{u, v, max c x y} In₁ In₂)
    (hextract : BerardPreLambdaRationalTreeExtraction.{u, v, x, y, s, c} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, max c x y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finiteGlobalBeliefMachine A fallback
    (perStrategyWinningFiniteGlobalBeliefMachine_of_berardPreLambda
      A fallback hextract)

end DetParityAutomaton

end DistributedSynthesis
