/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusBound

/-!
# Computing a uniform consensus bound

Manuscript source label: `lem:computable-consensus-bound`.

## Paper statement

From $\mathcal A_\text{adv}$, one can compute a $D \geq 1$
  such that consensus is solvable within $D$ rounds under~$h^{-1}A$
  for every $h \in \Pref(A)$.

## Reading the proof

See the [proof locations](PROOFS.md#computing-a-uniform-consensus-bound) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ConsensusBound

/-- Reuses `Characterisation.ComponentGames.Consensus.computable_consensus_bound`. -/
theorem computable_consensus_bound :
    ∀ (M : DetParityAutomaton Graph) [inst : DecidableEq M.State]
      {V : Type} [Nonempty V] (A : Set (ℕ → Graph)),
      (∀ (word : ℕ → Graph), word ∈ A ↔ M.Accepts word) →
        IsNowhereDense (geometricMap '' A) →
          ∃ (promise : IsNowhereDense (geometricMap '' {word : ℕ → Graph | M.Accepts word})),
            0 < ComponentGames.Consensus.computedConsensusBound M promise ∧
              ∀ (h : List Graph),
                LivePrefix A h →
                  ∃ (σ : StrategyPair V V (Option V) (Option V)),
                    ComponentGames.Consensus.SolvesBy σ (Residual A h)
                      (ComponentGames.Consensus.computedConsensusBound M promise) :=
  @_root_.Characterisation.ComponentGames.Consensus.computable_consensus_bound

/-- Reuses `Characterisation.ComponentGames.Consensus.computedConsensusBound_correct`. -/
theorem computedConsensusBound_correct :
    ∀ (M : DetParityAutomaton Graph) [inst : DecidableEq M.State]
      {V : Type} [Nonempty V] (promise : IsNowhereDense (geometricMap '' {word : ℕ → Graph | M.Accepts word})),
      0 < ComponentGames.Consensus.computedConsensusBound M promise ∧
        ∀ (h : List Graph),
          LivePrefix {word : ℕ → Graph | M.Accepts word} h →
            ∃ (σ : StrategyPair V V (Option V) (Option V)),
              ComponentGames.Consensus.SolvesBy σ (Residual {word : ℕ → Graph | M.Accepts word} h)
                (ComponentGames.Consensus.computedConsensusBound M promise) :=
  @_root_.Characterisation.ComponentGames.Consensus.computedConsensusBound_correct

end DistributedSynthesis.Paper.ConsensusBound
