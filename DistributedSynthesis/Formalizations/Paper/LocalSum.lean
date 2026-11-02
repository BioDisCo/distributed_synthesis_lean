/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows

/-!
# The local weight identity

Manuscript source label: `lem:local-sum`.

## Paper statement

Let $f$ realize $\localsum$ and $\posord$.
    The view complexes of $f$ satisfy (C2).

## Correspondence

OnlyFirst says that the machine uses its first counter only. It is a syntax restriction
expressing the paper's one-counter machine, not an assumption on its run. Every scalar
program has this property by ofCode_onlyFirst.

## Reading the proof

See the [proof locations](PROOFS.md#the-local-weight-identity) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.LocalSum

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.local_sum_on_view_edge`. -/
theorem local_sum_on_view_edge :
    ∀ {Q : Type u_1} [DecidableEq Q] (M : CounterMachine.Machine Q),
      OnlyFirst M →
        ∀ (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
          (∀ (env : EnvironmentSequence Unit Unit), Position (execution σ env)) →
            (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ), Balance M (execution σ env n)) →
              ∀ (h : List Graph),
                0 < h.length →
                  have l := rowOutput σ (FullViewPath.left (FullViewPath.evaluate h));
                  have r := rowOutput σ (FullViewPath.right (FullViewPath.evaluate h));
                  l.right.promised + ↑l.carry =
                    (op M l.control l.zero).factor * ↑l.right.weight + ↑r.carry :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.local_sum_on_view_edge

end DistributedSynthesis.Paper.LocalSum
