/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows

/-!
# Checking the initial configuration

Manuscript source label: `lem:init-check`.

## Paper statement

Let $f$ realize $\initcheck$, $\zeroclaim$, $\pathagr$ and $\posord$.
    The view complexes of $f$ satisfy (C4).

## Reading the proof

See the [proof locations](PROOFS.md#checking-the-initial-configuration) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.InitialCheck

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.initial_check_on_row`. -/
theorem initial_check_on_row :
    ∀ {Q : Type u_1} [DecidableEq Q] (M : CounterMachine.Machine Q)
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
                (∀ (env : EnvironmentSequence Unit Unit), Initial M (execution σ env 0)) →
                  ∀ (h : List Graph),
                    h.length = 1 →
                      (σ.one (FullViewPath.evaluate h).one).control = M.initial ∧
                        (σ.two (FullViewPath.evaluate h).two).control = M.initial ∧
                          (rowOutput σ
                                    (FullViewPath.left (FullViewPath.evaluate h))).right.weight.val =
                            1 :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.initial_check_on_row

end DistributedSynthesis.Paper.InitialCheck
