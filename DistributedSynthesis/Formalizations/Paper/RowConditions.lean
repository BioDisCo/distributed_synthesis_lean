/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows

/-!
# The formula and the row conditions

Manuscript source label: `lem:conditions<=>realizability`.

## Paper statement

Algorithm $f$ realizes $\phi(M_\single)$ if and only if it satisfies conditions (C0)--(C5)
    and no halting state is output.

## Correspondence

GlobalRows contains the scalar conditions C0--C5; NoHaltingOutputs is the separate
nonhalting requirement. OnlyFirst expresses the one-counter syntax and is discharged by
ofCode_onlyFirst.

## Reading the proof

See the [proof locations](PROOFS.md#the-formula-and-the-row-conditions) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.RowConditions

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.global_rows_iff_formula`. -/
theorem global_rows_iff_formula :
    ∀ {Q : Type u_1} [DecidableEq Q] [inst : Fintype Q]
      (M : CounterMachine.Machine Q),
      OnlyFirst M →
        ∀ (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
          GlobalRows M σ ∧ NoHaltingOutputs M σ ↔
            ∀ (env : EnvironmentSequence Unit Unit),
              LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M) :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.global_rows_iff_formula

end DistributedSynthesis.Paper.RowConditions
