/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterSoundness

/-!
# Soundness of the counter encoding

Manuscript source label: `lem:soundness`.

## Paper statement

Suppose that there exists $f$ that realizes $\phi(M_\single)$.
    Then $M_\single$ does not halt.

## Correspondence

The displayed run is the scalar run. OnlyFirst expresses one-counter syntax, discharged
for every scalar program by ofCode_onlyFirst. Row n is the paper's round n+1; positivity
and the logarithmic identity are conclusions.

## Reading the proof

`formula_logarithmic_run` identifies the control state and the counter value
represented by the row mass at every step. The scalar construction is
transported to the existing counter implementation; `run_embed` proves that
this preserves the run. `soundness` instantiates the equivalence for every
scalar program, discharging `OnlyFirst` internally.

See the [proof locations](PROOFS.md#soundness-of-the-counter-encoding) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.CounterSoundness

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.formula_logarithmic_run`. -/
theorem formula_logarithmic_run :
    ∀ {Q : Type u_1} [inst : DecidableEq Q] [inst_1 : Fintype Q]
      (M : CounterMachine.Machine Q),
      OnlyFirst M →
        ∀ (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
          (∀ (env : EnvironmentSequence Unit Unit),
              LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M)) →
            ∀ (n : ℕ),
              rowControl σ n = (run M n).1 ∧
                0 < rowMass M σ n ∧
                  -Real.logb 3 (↑(rowMass M σ n) / 3 ^ (n + 1)) =
                    ↑(run M n).2 :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.formula_logarithmic_run

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.formula_zero_exact`. -/
theorem formula_zero_exact :
    ∀ {Q : Type u_1} [DecidableEq Q] [inst : Fintype Q]
      (M : CounterMachine.Machine Q),
      OnlyFirst M →
        ∀ (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
          (∀ (env : EnvironmentSequence Unit Unit),
              LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M)) →
            ∀ (n : ℕ), rowZero σ n = true ↔ (run M n).2 = 0 :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.formula_zero_exact


/-- The paper's conclusion for every scalar program, with no extra syntax premise. -/
theorem soundness {Q : Type*} [DecidableEq Q] [Fintype Q]
    (initial : Q) (code : Q → Option (Q ⊕ (Q × Q)))
    (realizes : ∃ f : StrategyPair Unit Unit (Output Q) (Output Q),
      ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution f env)
        (formula (ofCode initial code))) :
    Nonhalting (ofCode initial code) :=
  (ofCode_realizable_iff initial code).mp realizes

end DistributedSynthesis.Paper.CounterSoundness
