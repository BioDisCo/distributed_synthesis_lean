/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusBound
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusGap

/-!
# Repeated consensus and nowhere denseness

Manuscript source label: `lem:repeated_bounded_time_consensus`.

## Paper statement

Consensus is repeatedly solvable in bounded time under message adversary~$A$ if and only if~$\pi(A)$ is nowhere dense.
    In this case, if~$A$ is $\omega$-regular, consensus is repeatedly solvable in uniformly bounded time.

## Reading the proof

See the [proof locations](PROOFS.md#repeated-consensus-and-nowhere-denseness) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.RepeatedConsensus

/-- Reuses `Characterisation.ComponentGames.Consensus.repeated_bounded_iff_nowhere_dense`. -/
theorem repeated_bounded_iff_nowhere_dense :
    ∀ {V : Type} [Nontrivial V] (A : Set (ℕ → Graph)),
      (∀ (h : List Graph),
          LivePrefix A h →
            ∃ (R : ℕ) (σ : StrategyPair V V (Option V) (Option V)), ComponentGames.Consensus.SolvesBy σ (Residual A h) R) ↔
        IsNowhereDense (geometricMap '' A) :=
  @_root_.Characterisation.ComponentGames.Consensus.repeated_bounded_iff_nowhere_dense

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

end DistributedSynthesis.Paper.RepeatedConsensus
