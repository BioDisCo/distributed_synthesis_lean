/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows

/-!
# Checking a machine transition

Manuscript source label: `lem:prop-trans`.

## Paper statement

Let $f$ realize $\proptrans$ and $\posord$.
    The view complexes of $f$ satisfy (C5).

## Reading the proof

See the [proof locations](PROOFS.md#checking-a-machine-transition) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.ProperTransition

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.transition_child_weight`. -/
theorem transition_child_weight :
    ∀ {Q : Type u_1} [DecidableEq Q] (M : CounterMachine.Machine Q)
      (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
      (∀ (env : EnvironmentSequence Unit Unit), Position (execution σ env)) →
        (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ),
            Transition M (execution σ env n) (execution σ env (n + 1))) →
          ∀ (h : List Graph),
            0 < h.length →
              ∀ (g : Graph),
                (rowOutput σ
                        (FullViewPath.left (FullViewPath.evaluate (h ++ [g])))).right.weight =
                  (rowOutput σ (FullViewPath.left (FullViewPath.evaluate h))).right.child
                    (ScalingSafety.digit (FullViewPath.evaluate h).oneLeft g) :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.transition_child_weight

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.transition_leftmost_control`. -/
theorem transition_leftmost_control :
    ∀ {Q : Type u_1} (M : CounterMachine.Machine Q)
      (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
      (∀ (env : EnvironmentSequence Unit Unit) (n : ℕ),
          Transition M (execution σ env n) (execution σ env (n + 1))) →
        ∀ (n : ℕ),
          (σ.one (FullViewPath.evaluate (List.replicate (n + 2) Graph.right)).one).control =
            next M
              (σ.one (FullViewPath.evaluate (List.replicate (n + 1) Graph.right)).one).control
              (σ.one (FullViewPath.evaluate (List.replicate (n + 1) Graph.right)).one).zero :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.transition_leftmost_control

end DistributedSynthesis.Paper.ProperTransition
