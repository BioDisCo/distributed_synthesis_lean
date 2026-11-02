/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSummaryreversalmeasurable
import DistributedSynthesis.Formalizations.Theorem.ThmReversalForgiving
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# Instantiating the summary-controlled fold with a real `LocalSummaryAutomaton`

The realizing θ̄-fold's plan family (`summaryPlanFamily`, `LemSummaryblockplan`) is parameterized
by an abstract summary *type* with `init`/`step`/output tables.  This file plugs in the concrete
summary automaton `M : LocalSummaryAutomaton` -- the journal summaries of the paper
(`prop:reversedblockmonitor`(v)): the block control on process `d` is `M.Summary d`, stepped by
the subordinate sender's `M.stepNoRecv` on its own input, exactly the state the readback maintains.

`summaryFold M …` is then a *control-changing* fold on plan families whose target control is the
finite summary triple `(M.Summary two, M.Summary one, M.Summary two ⊕ M.Summary one)`.  Its `hmeas`
is `summaryPlanFamily_reversalMeasurable` -- **unconditional** (all seven `ReversalMeasurable`
obligations by construction, after the reset-parity restriction).  Feeding it into
`reversalMeasurable_winner_of_fold_of_arenaSound` (`ThmReversalForgiving`) reduces the θ̄-measurable
winner over these concrete summary controls to the hypothesis `hsound`
(`prop:starsound`, the arena-acceptance sufficient statistic).  This verifies that the real
summary types satisfy every `Fintype`/`DecidableEq`/`Inhabited` and universe requirement of the
reduction machine; it does *not* close `hsound`, which is the genuine `prop:starcomplete` research
crux.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [DecidableEq A.State]

/-- The **summary-controlled fold** of a real summary automaton `M`.  The target control on
process `d` is the finite summary `M.Summary d`, stepped by the subordinate sender's `stepNoRecv`
on its own input; the block outputs are the given `θ̄`-tables (the winner-dependent commitment that
`prop:starcomplete` constructs).  The fold ignores its input plan family: the summary construction
is atom/boundary independent (`summaryPlanFamily`), so `hmeas` holds for it uniformly, and the
winner enters only through the tables and the arena-soundness obligation. -/
def summaryFold
    (M : LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂)
    (blindR : M.Summary Proc.one -> In₁ -> Out₁)
    (informedR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₂)
    (closeR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (blindL : M.Summary Proc.two -> In₂ -> Out₂)
    (informedL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₁)
    (closeL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₂)
    {C_L C_R C_V : Type max u v x y s}
    (_Q : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A (M.Summary Proc.two) (M.Summary Proc.one)
      (M.Summary Proc.two ⊕ M.Summary Proc.one) :=
  summaryPlanFamily (A := A) (M.Summary Proc.one) (M.Summary Proc.two)
    (M.initial Proc.one) (fun s i => M.stepNoRecv Proc.one s (PSum.inl i))
    blindR informedR closeR
    (M.initial Proc.two) (fun s i => M.stepNoRecv Proc.two s (PSum.inr i))
    blindL informedL closeL

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq A.State] in
/-- **`summaryFold`'s `hmeas` is unconditional.**  For every input plan family, the fold is
`ReversalMeasurable` by construction (`summaryPlanFamily_reversalMeasurable`), since it *is* a
summary plan family. -/
theorem summaryFold_reversalMeasurable
    (M : LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂)
    (blindR : M.Summary Proc.one -> In₁ -> Out₁)
    (informedR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₂)
    (closeR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (blindL : M.Summary Proc.two -> In₂ -> Out₂)
    (informedL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₁)
    (closeL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₂)
    {C_L C_R C_V : Type max u v x y s}
    (Q : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    ReversalMeasurable
      (summaryFold A M blindR informedR closeR blindL informedL closeL Q) :=
  summaryPlanFamily_reversalMeasurable (A := A) (M.Summary Proc.one) (M.Summary Proc.two)
    (M.initial Proc.one) (fun s i => M.stepNoRecv Proc.one s (PSum.inl i))
    blindR informedR closeR
    (M.initial Proc.two) (fun s i => M.stepNoRecv Proc.two s (PSum.inr i))
    blindL informedL closeL

/-- **The concrete-summary θ̄-measurable winner, modulo `hsound`.**  With the real journal-summary
automaton `M` installed as the fold's control, a boundary-game winner `τ` yields a `ReversalMeasurable`
winner over the finite summary controls -- conditional only on `hsound` (`prop:starsound`: `τ`'s
all-environment arena acceptance transfers to the summary fold).  Every `Fintype`/`DecidableEq`/
`Inhabited` and universe obligation of `reversalMeasurable_winner_of_fold_of_arenaSound` is
discharged by `M.finite`, the supplied `DecidableEq`, and `M.initial`; the `hmeas` half is
`summaryFold_reversalMeasurable`, unconditional. -/
theorem summaryFold_measurableWinner
    (M : LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂)
    [DecidableEq (M.Summary Proc.one)] [DecidableEq (M.Summary Proc.two)]
    [Inhabited (M.Summary Proc.one)] [Inhabited (M.Summary Proc.two)]
    (blindR : M.Summary Proc.one -> In₁ -> Out₁)
    (informedR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₂)
    (closeR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (blindL : M.Summary Proc.two -> In₂ -> Out₂)
    (informedL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₁)
    (closeL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₂)
    {C_L C_R C_V : Type max u v x y s}
    [Fintype C_L] [DecidableEq C_L] [Inhabited C_L]
    [Fintype C_R] [DecidableEq C_R] [Inhabited C_R]
    [Fintype C_V] [DecidableEq C_V] [Inhabited C_V]
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
        τ (Sum.inl (A.initial, A.initial)))
    (hsound :
      (∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (arenaWord (plansOf τ) env)) ->
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts
            (arenaWord
              (summaryFold A M blindR informedR closeR blindL informedL closeL
                (plansOf τ)) env)) :
    ∃ τ' :
        (DetParityAutomaton.boundaryGame A (M.Summary Proc.two) (M.Summary Proc.one)
            (M.Summary Proc.two ⊕ M.Summary Proc.one)).PositionalStrategy
          ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
          (G :=
            DetParityAutomaton.boundaryGame A (M.Summary Proc.two) (M.Summary Proc.one)
              (M.Summary Proc.two ⊕ M.Summary Proc.one))
          τ' (Sum.inl (A.initial, A.initial)) ∧
        ReversalMeasurable (plansOf τ') :=
  reversalMeasurable_winner_of_fold_of_arenaSound A
    (summaryFold A M blindR informedR closeR blindL informedL closeL)
    (summaryFold_reversalMeasurable A M blindR informedR closeR blindL informedL closeL)
    τ hτ hsound

/-- **The summary-fold route reaches a realizing distributed strategy, gated solely on `hsound`.**
Composing `summaryFold_measurableWinner` with the *control-polymorphic*
`accepts_execution_journalStrategy_of_winning_full`, the `ReversalMeasurable` winner over the
concrete summary controls reads back to a distributed strategy accepted on *every* environment
(direct reversals included).  This dissolves the control-unification concern: the readback
soundness lemma consumes a measurable winner over any control, so the summary controls need not
be transported to a common `ULift C`.  The whole full-model realization is thereby exposed as
resting on exactly `hsound` (`prop:starsound`/`prop:starcomplete`), with no residual interface
plumbing. -/
theorem summaryFold_realizes_of_arenaSound
    (M : LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂)
    [DecidableEq (M.Summary Proc.one)] [DecidableEq (M.Summary Proc.two)]
    [Inhabited (M.Summary Proc.one)] [Inhabited (M.Summary Proc.two)]
    (blindR : M.Summary Proc.one -> In₁ -> Out₁)
    (informedR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₂)
    (closeR : M.Summary Proc.one -> (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (blindL : M.Summary Proc.two -> In₂ -> Out₂)
    (informedL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₁)
    (closeL : M.Summary Proc.two -> (A.State × A.State) -> In₁ × In₂ -> Out₂)
    {C_L C_R C_V : Type max u v x y s}
    [Fintype C_L] [DecidableEq C_L] [Inhabited C_L]
    [Fintype C_R] [DecidableEq C_R] [Inhabited C_R]
    [Fintype C_V] [DecidableEq C_V] [Inhabited C_V]
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
        τ (Sum.inl (A.initial, A.initial)))
    (hsound :
      (∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (arenaWord (plansOf τ) env)) ->
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts
            (arenaWord
              (summaryFold A M blindR informedR closeR blindL informedL closeL
                (plansOf τ)) env)) :
    ∃ σ' : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ' env) := by
  obtain ⟨τ', hwin', hmeas'⟩ :=
    summaryFold_measurableWinner A M blindR informedR closeR blindL informedL closeL τ hτ hsound
  exact
    ⟨journalStrategy (plansOf τ'),
      fun env => accepts_execution_journalStrategy_of_winning_full τ' hwin' env hmeas'⟩

end DetParityAutomaton

end DistributedSynthesis
