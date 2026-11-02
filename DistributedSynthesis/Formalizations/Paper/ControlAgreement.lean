/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows

/-!
# Agreement on the control state

Manuscript source label: `lem:pathagr`.

## Paper statement

Let $f$ realize $\pathagr$.
    The view complexes of $f$ satisfy (C1).

## Reading the proof

See the [proof locations](PROOFS.md#agreement-on-the-control-state) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.ControlAgreement

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.agreement_row_uniform`. -/
theorem agreement_row_uniform :
    ∀ {Q : Type u_1}
      (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
      (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ), Agreement (execution σ env n)) →
        ∀ (n : ℕ),
          ∃ (q : Q) (z : Bool),
            ∀ (h : List Graph),
              h.length = n + 1 →
                (σ.one (FullViewPath.evaluate h).one).control = q ∧
                  (σ.two (FullViewPath.evaluate h).two).control = q ∧
                    (σ.one (FullViewPath.evaluate h).one).zero = z ∧ (σ.two (FullViewPath.evaluate h).two).zero = z :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.agreement_row_uniform

end DistributedSynthesis.Paper.ControlAgreement
