/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows

/-!
# Checking whether the counter is zero

Manuscript source label: `lem:zero-claim`.

## Paper statement

Let $f$ realize $\zeroclaim$, $\pathagr$ and $\posord$.
    The view complexes of $f$ satisfy (C3).

## Reading the proof

See the [proof locations](PROOFS.md#checking-whether-the-counter-is-zero) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.ZeroCheck

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.zero_claim_on_row`. -/
theorem zero_claim_on_row :
    ∀ {Q : Type u_1} [DecidableEq Q]
      (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
      (∀ (env : EnvironmentSequence Unit Unit), Position (execution σ env)) →
        (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ), Agreement (execution σ env n)) →
          (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ), ZeroWeight (execution σ env n)) →
            (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ),
                (∀ t ≤ n, (execution σ env t).graph = Graph.right) →
                  LeftBoundary (execution σ env n)) →
              (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ),
                  (∀ t ≤ n, (execution σ env t).graph = Graph.left) →
                    RightBoundary (execution σ env n)) →
                ∀ (n : ℕ),
                  have first := σ.one (FullViewPath.evaluate (List.replicate (n + 1) Graph.right)).one;
                  have last := σ.two (FullViewPath.evaluate (List.replicate (n + 1) Graph.left)).two;
                  first.carry.val = 0 ∧
                    last.carry.val = 0 ∧
                      (first.zero = true →
                          ∀ (h : List Graph),
                            h.length = n + 1 →
                              (rowOutput σ
                                        (FullViewPath.left (FullViewPath.evaluate h))).right.weight.val =
                                1) ∧
                        (first.zero = false → first.right.weight.val = 0) :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.zero_claim_on_row

end DistributedSynthesis.Paper.ZeroCheck
