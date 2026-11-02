/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledReceiptReadbackBoundary

/-!
# Finite operational semantics of the receipt carrier

The receipt-tagged family automaton is already an executable finite local
summary automaton.  This file removes recursive views from its remaining
correctness obligation.  For every environment, reading the two execution
views is exactly the finite pair obtained by iterating
`LocalSummaryAutomaton.advance`; the emitted execution word is therefore the
word obtained from that finite trace.

No definition below receives a graph-derived side, an orientation, a family
class, a leader flag, or a hidden bit.  The graph is used only by the ordinary
joint `advance` operation, while each process still runs the graph-blind local
tables of `endToEndFamilyReceiptSummaryAutomaton`.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)
variable (initialOne : EndToEndFamilyReceiptOneSummary A package)
variable (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
variable (receive : EndToEndFamilyReceiptReceivePairTable A package)

/-- The concrete receipt-tagged local summary automaton, with its parameters
kept implicit in the operational statements below. -/
abbrev endToEndFamilyReceiptM :=
  endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo receive

/-- The distributed finite-state strategy exposed by the receipt carrier. -/
def endToEndFamilyReceiptStrategy : StrategyPair In₁ In₂ Out₁ Out₂ :=
  (endToEndFamilyReceiptM A package initialOne initialTwo receive).readbackStrategy
    (endToEndFamilyReceiptOutputOne A package)
    (endToEndFamilyReceiptOutputTwo A package)

/-- The joint finite receipt state before round `n`. -/
def endToEndFamilyReceiptTrace
    (env : EnvironmentSequence In₁ In₂) : Nat →
      (endToEndFamilyReceiptM A package initialOne initialTwo receive).Pair
  | 0 => (initialOne, initialTwo)
  | n + 1 =>
      (endToEndFamilyReceiptM A package initialOne initialTwo receive).advance
        (endToEndFamilyReceiptTrace env n) (env n).graph
        (env n).inputOne (env n).inputTwo

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp]
theorem endToEndFamilyReceiptTrace_zero
    (env : EnvironmentSequence In₁ In₂) :
    endToEndFamilyReceiptTrace A package initialOne initialTwo receive env 0 =
      (initialOne, initialTwo) :=
  rfl

@[simp]
theorem endToEndFamilyReceiptTrace_succ
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    endToEndFamilyReceiptTrace A package initialOne initialTwo receive env (n + 1) =
      (endToEndFamilyReceiptM A package initialOne initialTwo receive).advance
        (endToEndFamilyReceiptTrace A package initialOne initialTwo receive env n)
        (env n).graph (env n).inputOne (env n).inputTwo :=
  rfl

/-- Reading the two recursive execution views yields exactly the direct finite
receipt trace. -/
theorem endToEndFamilyReceipt_readPair_executionPrefix
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (endToEndFamilyReceiptM A package initialOne initialTwo receive).readPair
        (viewPair (executionPrefix
          (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
          env n)) =
      endToEndFamilyReceiptTrace A package initialOne initialTwo receive env n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [executionPrefix_succ, viewPair_append]
      rw [(endToEndFamilyReceiptM A package initialOne initialTwo receive).readPair_advanceViews]
      rw [ih]
      rfl

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The outputs emitted in round `n` are precisely the Moore outputs stored in
the next joint receipt state. -/
theorem endToEndFamilyReceipt_execution_outputs
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((execution
        (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
        env n).outputOne,
      (execution
        (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
        env n).outputTwo) =
      ((endToEndFamilyReceiptTrace A package initialOne initialTwo receive env
          (n + 1)).1.1.2,
        (endToEndFamilyReceiptTrace A package initialOne initialTwo receive env
          (n + 1)).2.1.2) := by
  rw [execution_apply]
  change
    (((endToEndFamilyReceiptM A package initialOne initialTwo receive).read
        (nextView Proc.one
          (executionPrefix
            (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
            env n)
          (env n))).1.2,
      ((endToEndFamilyReceiptM A package initialOne initialTwo receive).read
        (nextView Proc.two
          (executionPrefix
            (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
            env n)
          (env n))).1.2) = _
  have hpair :=
    (endToEndFamilyReceiptM A package initialOne initialTwo receive).readPair_advanceViewsWithEnvironment
        (viewPair (executionPrefix
          (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
          env n))
        (env n)
  rw [endToEndFamilyReceipt_readPair_executionPrefix A package initialOne
    initialTwo receive env n] at hpair
  have htrace :
      endToEndFamilyReceiptTrace A package initialOne initialTwo receive env
          (n + 1) =
        (endToEndFamilyReceiptM A package initialOne initialTwo receive).advance
          (endToEndFamilyReceiptTrace A package initialOne initialTwo receive env n)
          (env n).graph (env n).inputOne (env n).inputTwo :=
    rfl
  rw [← htrace] at hpair
  exact congrArg
    (fun pair =>
      (endToEndFamilyReceiptOutputOne A package pair.1,
        endToEndFamilyReceiptOutputTwo A package pair.2)) hpair

/-- The finite-trace word: environment data are copied verbatim and the two
outputs are read from the next finite receipt state. -/
def endToEndFamilyReceiptTraceWord
    (env : EnvironmentSequence In₁ In₂) :
    Nat → RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  fun n =>
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne :=
        (endToEndFamilyReceiptTrace A package initialOne initialTwo receive env
          (n + 1)).1.1.2
      outputTwo :=
        (endToEndFamilyReceiptTrace A package initialOne initialTwo receive env
          (n + 1)).2.1.2 }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The distributed execution is definitionally represented by the finite
trace word.  This is the view-elimination theorem used by the final parity
argument. -/
theorem endToEndFamilyReceipt_execution_eq_traceWord
    (env : EnvironmentSequence In₁ In₂) :
    execution
        (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
        env =
      endToEndFamilyReceiptTraceWord A package initialOne initialTwo receive env := by
  funext n
  have houtputs := endToEndFamilyReceipt_execution_outputs A package initialOne
    initialTwo receive env n
  have hone :
      (execution
        (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
        env n).outputOne =
        (endToEndFamilyReceiptTrace A package initialOne initialTwo receive env
          (n + 1)).1.1.2 := by
    simpa only [Prod.fst] using congrArg Prod.fst houtputs
  have htwo :
      (execution
        (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
        env n).outputTwo =
        (endToEndFamilyReceiptTrace A package initialOne initialTwo receive env
          (n + 1)).2.1.2 := by
    simpa only [Prod.snd] using congrArg Prod.snd houtputs
  rw [execution_apply] at hone htwo
  simp only [nextRound_outputOne] at hone
  simp only [nextRound_outputTwo] at htwo
  rw [execution_apply]
  simp only [endToEndFamilyReceiptTraceWord, nextRound]
  rw [hone, htwo]

/-- Original-DPA acceptance of the recursive-view execution is equivalent to
acceptance of the explicit finite-trace word. -/
theorem endToEndFamilyReceipt_accepts_execution_iff_traceWord
    (env : EnvironmentSequence In₁ In₂) :
    A.Accepts
        (execution
          (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
          env) ↔
      A.Accepts
        (endToEndFamilyReceiptTraceWord A package initialOne initialTwo receive
          env) := by
  rw [endToEndFamilyReceipt_execution_eq_traceWord A package initialOne
    initialTwo receive env]

/-- Hence the remaining all-environment semantic obligation can be stated
entirely over the finite receipt transition trace.  No recursive view or
hidden classifier remains in this premise. -/
theorem endToEndFamilyReceipt_allEnvironment_accepts_iff_traceWord
    :
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (execution
          (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
          env)) ↔
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (endToEndFamilyReceiptTraceWord A package initialOne initialTwo receive
          env)) := by
  constructor <;> intro h env
  · exact
      (endToEndFamilyReceipt_accepts_execution_iff_traceWord A package initialOne
        initialTwo receive env).mp (h env)
  · exact
      (endToEndFamilyReceipt_accepts_execution_iff_traceWord A package initialOne
        initialTwo receive env).mpr (h env)

/-- Strategy-indexed endpoint stated only with the finite-trace invariant.
This is the direct adapter into `PerStrategyWinningReadback`: once the model
construction proves original-DPA acceptance of every finite receipt trace
word, no further operational or view-measurability argument is needed. -/
theorem perStrategyWinningReadback_of_endToEndFamilyReceiptTrace
    (fallback : LocalSummaryAutomaton.{u, v, max 1 u v x y s} In₁ In₂)
    (hextract :
      ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        (∀ environment : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy environment)) →
        ∃ (package : PairedInitialProfiledRationalPackage A)
          (initialOne : EndToEndFamilyReceiptOneSummary A package)
          (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
          (receive : EndToEndFamilyReceiptReceivePairTable A package),
          ∀ environment : EnvironmentSequence In₁ In₂,
            A.Accepts
              (endToEndFamilyReceiptTraceWord A package initialOne initialTwo
                receive environment)) :
    PerStrategyWinningReadback A fallback := by
  apply perStrategyWinningReadback_of_endToEndFamilyReceipt A fallback
  intro strategy hstrategy
  obtain ⟨package, initialOne, initialTwo, receive, htrace⟩ :=
    hextract strategy hstrategy
  refine ⟨package, initialOne, initialTwo, receive, ?_⟩
  intro environment
  exact
    (endToEndFamilyReceipt_accepts_execution_iff_traceWord A package initialOne
      initialTwo receive environment).mpr (htrace environment)

end

end

end DetParityAutomaton

end DistributedSynthesis
