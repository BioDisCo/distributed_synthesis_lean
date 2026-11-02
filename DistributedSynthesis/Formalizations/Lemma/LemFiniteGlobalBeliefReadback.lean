/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalBeliefSummary
import DistributedSynthesis.Formalizations.Lemma.LemReadbackUpgradeQuantifierAudit

/-!
# Readback correctness for finite global belief summaries

This file supplies the operational bridge for
`FiniteGlobalRoundMachine.beliefSummaryAutomaton`.  If each process's Moore
output is uniform on every reachable local belief, then the distributed
belief readback emits exactly the output of the real global-machine state.

The timing is explicit: round `n` first updates the global control with the
environment move `env n`, and the two outputs of round `n` are read from that
post-update state, namely `globalStateTrace G env (n + 1)`.

No definition or theorem below receives a leader, an orientation, a family
class, or a hidden bit.  The only model-dependent premise is the extensional
`ReachableBeliefsUniform` property.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

noncomputable section

/-! ## Direct global and belief traces -/

/-- The real global control after exactly `n` environment rounds. -/
def globalStateTrace (env : EnvironmentSequence In₁ In₂) : Nat → G.State
  | 0 => G.initial
  | n + 1 => G.step (globalStateTrace env n) (env n)

/-- The two finite local beliefs after exactly `n` environment rounds. -/
def globalBeliefTrace (env : EnvironmentSequence In₁ In₂) :
    Nat → Finset G.State × Finset G.State
  | 0 => ({G.initial}, {G.initial})
  | n + 1 => G.beliefAdvance (globalBeliefTrace env n) (env n)

omit [Fintype In₁] [Fintype In₂] in
@[simp] theorem globalStateTrace_zero (env : EnvironmentSequence In₁ In₂) :
    G.globalStateTrace env 0 = G.initial :=
  rfl

omit [Fintype In₁] [Fintype In₂] in
@[simp] theorem globalStateTrace_succ
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    G.globalStateTrace env (n + 1) =
      G.step (G.globalStateTrace env n) (env n) :=
  rfl

@[simp]
theorem globalBeliefTrace_zero (env : EnvironmentSequence In₁ In₂) :
    G.globalBeliefTrace env 0 = ({G.initial}, {G.initial}) :=
  rfl

@[simp]
theorem globalBeliefTrace_succ
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    G.globalBeliefTrace env (n + 1) =
      G.beliefAdvance (G.globalBeliefTrace env n) (env n) :=
  rfl

/-- A recursive list presentation of the first `n` environment rounds. -/
def globalRoundPrefix (env : EnvironmentSequence In₁ In₂) :
    Nat → List (EnvironmentRound In₁ In₂)
  | 0 => []
  | n + 1 => globalRoundPrefix env n ++ [env n]

section
omit [Fintype In₁] [Fintype In₂]

@[simp] theorem globalRoundPrefix_zero (env : EnvironmentSequence In₁ In₂) :
    globalRoundPrefix env 0 = [] :=
  rfl

@[simp] theorem globalRoundPrefix_succ
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    globalRoundPrefix env (n + 1) =
      globalRoundPrefix env n ++ [env n] :=
  rfl

/-- The recursive state trace agrees with the existing finite-list fold. -/
theorem globalStateTrace_eq_stateAfter_prefix
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    G.globalStateTrace env n =
      G.stateAfter (globalRoundPrefix env n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [globalStateTrace_succ, globalRoundPrefix_succ, stateAfter,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]
      rfl

end

/-- The recursive belief trace agrees with the reachable beliefs used by
`ReachableBeliefsUniform`. -/
theorem globalBeliefTrace_eq_beliefsAfter_prefix
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    G.globalBeliefTrace env n =
      G.beliefsAfter (globalRoundPrefix env n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [globalBeliefTrace_succ, globalRoundPrefix_succ, beliefsAfter,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]
      rfl

/-- The real control remains a member of both beliefs along the direct
round-by-round trace. -/
theorem globalStateTrace_mem_globalBeliefTrace
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    G.globalStateTrace env n ∈ (G.globalBeliefTrace env n).1 ∧
      G.globalStateTrace env n ∈ (G.globalBeliefTrace env n).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact G.step_mem_advance (G.globalBeliefTrace env n)
        (G.globalStateTrace env n) ih.1 ih.2 (env n)

/-! ## Distributed belief readback -/

variable {Out₁ : Type x} {Out₂ : Type y}
variable [Inhabited Out₁] [Inhabited Out₂]
variable (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)

/-- The distributed strategy that reads an arbitrary representative from
each local belief.  Uniformity will make that choice observationally unique
on reachable beliefs. -/
def beliefReadbackStrategy : StrategyPair In₁ In₂ Out₁ Out₂ :=
  G.beliefSummaryAutomaton.readbackStrategy
    (G.beliefOutput outputOne) (G.beliefOutput outputTwo)

/-- Folding the two execution views through the belief summary automaton is
exactly the direct finite belief trace. -/
theorem beliefReadback_readPair_executionPrefix
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    G.beliefSummaryAutomaton.readPair
        (viewPair (executionPrefix
          (G.beliefReadbackStrategy outputOne outputTwo) env n)) =
      G.globalBeliefTrace env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [executionPrefix_succ, viewPair_append]
      rw [G.beliefSummaryAutomaton.readPair_advanceViews]
      rw [ih]
      change
        G.beliefSummaryAutomaton.advance (G.globalBeliefTrace env n)
            (env n).graph (env n).inputOne (env n).inputTwo =
          G.globalBeliefTrace env (n + 1)
      rw [G.beliefSummaryAutomaton_advance]
      rfl

/-- Before using uniformity, the emitted outputs are the representative
outputs of the freshly updated beliefs.  This lemma records Moore timing at
the belief level. -/
theorem beliefReadback_execution_beliefOutputs
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((execution (G.beliefReadbackStrategy outputOne outputTwo) env n).outputOne,
      (execution (G.beliefReadbackStrategy outputOne outputTwo) env n).outputTwo) =
      (G.beliefOutput outputOne (G.globalBeliefTrace env (n + 1)).1,
        G.beliefOutput outputTwo (G.globalBeliefTrace env (n + 1)).2) := by
  rw [execution_apply]
  change
    ((G.beliefOutput outputOne
        (G.beliefSummaryAutomaton.read
          (nextView Proc.one
            (executionPrefix
              (G.beliefReadbackStrategy outputOne outputTwo) env n)
            (env n))),
      G.beliefOutput outputTwo
        (G.beliefSummaryAutomaton.read
          (nextView Proc.two
            (executionPrefix
              (G.beliefReadbackStrategy outputOne outputTwo) env n)
            (env n)))) = _)
  have hpair :=
    G.beliefSummaryAutomaton.readPair_advanceViewsWithEnvironment
      (viewPair (executionPrefix
        (G.beliefReadbackStrategy outputOne outputTwo) env n))
      (env n)
  rw [G.beliefReadback_readPair_executionPrefix outputOne outputTwo env n]
    at hpair
  rw [G.beliefSummaryAutomaton_advance] at hpair
  change
    G.beliefSummaryAutomaton.readPair
        (advanceViewsWithEnvironment
          (viewPair (executionPrefix
            (G.beliefReadbackStrategy outputOne outputTwo) env n))
          (env n)) =
      G.globalBeliefTrace env (n + 1) at hpair
  exact congrArg
    (fun pair =>
      (G.beliefOutput outputOne pair.1,
        G.beliefOutput outputTwo pair.2)) hpair

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Reachable-list uniformity specializes to every state of the direct
belief trace. -/
theorem reachableBeliefsUniform_globalBeliefTrace
    (huniform : G.ReachableBeliefsUniform outputOne outputTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    G.BeliefUniform outputOne (G.globalBeliefTrace env n).1 ∧
      G.BeliefUniform outputTwo (G.globalBeliefTrace env n).2 := by
  rw [G.globalBeliefTrace_eq_beliefsAfter_prefix env n]
  exact huniform (globalRoundPrefix env n)

/-- The key readback theorem.  The output emitted in round `n` equals the
global Moore output after the machine consumes round `n`; hence the state
index is `n + 1`, not `n`. -/
theorem beliefReadback_execution_outputs
    (huniform : G.ReachableBeliefsUniform outputOne outputTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((execution (G.beliefReadbackStrategy outputOne outputTwo) env n).outputOne,
      (execution (G.beliefReadbackStrategy outputOne outputTwo) env n).outputTwo) =
      (outputOne (G.globalStateTrace env (n + 1)),
        outputTwo (G.globalStateTrace env (n + 1))) := by
  rw [G.beliefReadback_execution_beliefOutputs outputOne outputTwo env n]
  have hmembers := G.globalStateTrace_mem_globalBeliefTrace env (n + 1)
  have htraceUniform :=
    G.reachableBeliefsUniform_globalBeliefTrace outputOne outputTwo huniform env
      (n + 1)
  apply Prod.ext
  · exact G.beliefOutput_eq_of_mem_of_uniform outputOne
      (G.globalBeliefTrace env (n + 1)).1 htraceUniform.1
      (G.globalStateTrace env (n + 1)) hmembers.1
  · exact G.beliefOutput_eq_of_mem_of_uniform outputTwo
      (G.globalBeliefTrace env (n + 1)).2 htraceUniform.2
      (G.globalStateTrace env (n + 1)) hmembers.2

/-! ## Whole-word equality and acceptance transfer -/

/-- The word produced by the global machine under Moore timing: environment
data are copied from round `n`, while outputs are read after its transition. -/
def globalMachineTraceWord
    (env : EnvironmentSequence In₁ In₂) :
    Nat → RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  fun n =>
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne := outputOne (G.globalStateTrace env (n + 1))
      outputTwo := outputTwo (G.globalStateTrace env (n + 1)) }

/-- The proof-side global machine follows the outputs of one fixed distributed
strategy on the actual environment history.  This condition speaks only about
the real global trace; it makes no claim that either process can see the
global state or any hidden bit carried by it. -/
def StrategyOutputAgreement
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) : Prop :=
  ∀ (env : EnvironmentSequence In₁ In₂) (n : Nat),
    outputOne (G.globalStateTrace env (n + 1)) =
        strategy.one
          (nextView Proc.one (executionPrefix strategy env n) (env n)) ∧
      outputTwo (G.globalStateTrace env (n + 1)) =
        strategy.two
          (nextView Proc.two (executionPrefix strategy env n) (env n))

omit [Fintype In₁] [Fintype In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Pointwise agreement with the original strategy identifies the complete
physical word, including its outputs.  This is the preferred acceptance
handoff for a strategy-derived finite controller: acceptance then comes
directly from the original winning hypothesis, rather than from a monitor over
some auxiliary candidate alphabet. -/
theorem globalMachineTraceWord_eq_execution_of_strategyOutputAgreement
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hagrees : G.StrategyOutputAgreement outputOne outputTwo strategy)
    (env : EnvironmentSequence In₁ In₂) :
    G.globalMachineTraceWord outputOne outputTwo env =
      execution strategy env := by
  funext n
  obtain ⟨hone, htwo⟩ := hagrees env n
  rw [execution_apply]
  simp only [globalMachineTraceWord, nextRound]
  rw [hone, htwo]

omit [Fintype In₁] [Fintype In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Any all-environment winning property of the source strategy transfers to
the finite global machine once their physical words agree. -/
theorem globalMachine_allEnvironment_of_strategyOutputAgreement
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hagrees : G.StrategyOutputAgreement outputOne outputTwo strategy)
    (predicate : (Nat → RoundRecord In₁ In₂ Graph Out₁ Out₂) → Prop)
    (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
      predicate (execution strategy env)) :
    ∀ env : EnvironmentSequence In₁ In₂,
      predicate (G.globalMachineTraceWord outputOne outputTwo env) := by
  intro env
  rw [G.globalMachineTraceWord_eq_execution_of_strategyOutputAgreement
    outputOne outputTwo strategy hagrees env]
  exact hstrategy env

/-- Under reachable-belief uniformity, the distributed readback execution is
pointwise equal to the actual finite-global-machine word. -/
theorem beliefReadback_execution_eq_globalMachineTraceWord
    (huniform : G.ReachableBeliefsUniform outputOne outputTwo)
    (env : EnvironmentSequence In₁ In₂) :
    execution (G.beliefReadbackStrategy outputOne outputTwo) env =
      G.globalMachineTraceWord outputOne outputTwo env := by
  funext n
  have houtputs :=
    G.beliefReadback_execution_outputs outputOne outputTwo huniform env n
  have hone := congrArg Prod.fst houtputs
  have htwo := congrArg Prod.snd houtputs
  rw [execution_apply] at hone htwo ⊢
  simp only [nextRound_outputOne] at hone
  simp only [nextRound_outputTwo] at htwo
  simp only [globalMachineTraceWord, nextRound]
  rw [hone, htwo]

/-- Any predicate on infinite recorded words is invariant under the belief
readback replacement.  This is the generic acceptance-transfer interface;
it applies in particular to DPA acceptance without mentioning automata here. -/
theorem beliefReadback_wordPredicate_iff
    (huniform : G.ReachableBeliefsUniform outputOne outputTwo)
    (predicate : (Nat → RoundRecord In₁ In₂ Graph Out₁ Out₂) → Prop)
    (env : EnvironmentSequence In₁ In₂) :
    predicate (execution (G.beliefReadbackStrategy outputOne outputTwo) env) ↔
      predicate (G.globalMachineTraceWord outputOne outputTwo env) := by
  rw [G.beliefReadback_execution_eq_globalMachineTraceWord
    outputOne outputTwo huniform env]

/-- All-environment acceptance transfers from the global-machine word to the
distributed readback execution, for an arbitrary word predicate. -/
theorem beliefReadback_allEnvironment_of_globalMachine
    (huniform : G.ReachableBeliefsUniform outputOne outputTwo)
    (predicate : (Nat → RoundRecord In₁ In₂ Graph Out₁ Out₂) → Prop)
    (hglobal : ∀ env : EnvironmentSequence In₁ In₂,
      predicate (G.globalMachineTraceWord outputOne outputTwo env)) :
    ∀ env : EnvironmentSequence In₁ In₂,
      predicate (execution (G.beliefReadbackStrategy outputOne outputTwo) env) := by
  intro env
  rw [G.beliefReadback_execution_eq_globalMachineTraceWord
    outputOne outputTwo huniform env]
  exact hglobal env

end

end FiniteGlobalRoundMachine

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable [Inhabited Out₁] [Inhabited Out₂]
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## Strategy-indexed extraction package -/

/-- The exact strategy-indexed input consumed by the generic belief
readback.  After seeing a winning distributed strategy, the construction may
choose a finite global machine and its Moore output maps.  It must prove both
reachable-belief output uniformity and acceptance of the machine's explicit
post-transition trace word against every environment.

The global state universe is the fixed summary universe `w`; its concrete
finite type may still depend on the supplied winning strategy. -/
def PerStrategyWinningFiniteGlobalBeliefMachine
    (_fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂) : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy environment)) →
      ∃ (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
        (outputOne : G.State → Out₁)
        (outputTwo : G.State → Out₂),
        G.ReachableBeliefsUniform outputOne outputTwo ∧
          ∀ environment : EnvironmentSequence In₁ In₂,
            A.Accepts
              (G.globalMachineTraceWord outputOne outputTwo environment)

/-- A strategy-indexed winning finite global belief machine already supplies
a complete strategy-indexed winning local readback.  The local automaton is
exactly `G.beliefSummaryAutomaton`; output choice is sound solely because of
`ReachableBeliefsUniform`. -/
theorem perStrategyWinningReadback_of_finiteGlobalBeliefMachine
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract : PerStrategyWinningFiniteGlobalBeliefMachine A fallback) :
    PerStrategyWinningReadback A fallback := by
  intro strategy hstrategy
  obtain ⟨G, outputOne, outputTwo, huniform, hglobal⟩ :=
    hextract strategy hstrategy
  refine
    ⟨G.beliefSummaryAutomaton,
      G.beliefOutput outputOne,
      G.beliefOutput outputTwo, ?_⟩
  intro environment
  exact
    (G.beliefReadback_wordPredicate_iff outputOne outputTwo huniform A.Accepts
      environment).mpr (hglobal environment)

/-- The outer-existential endpoint.  The existing quantifier audit selects
one already complete winning readback in the realizable branch, thereby
fixing its finite summary automaton before the `ReadbackUpgrade` binder. -/
theorem exists_readbackUpgrade_of_finiteGlobalBeliefMachine
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract : PerStrategyWinningFiniteGlobalBeliefMachine A fallback) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_perStrategyWinningReadback A fallback
    (perStrategyWinningReadback_of_finiteGlobalBeliefMachine A fallback
      hextract)

end DetParityAutomaton

end DistributedSynthesis
