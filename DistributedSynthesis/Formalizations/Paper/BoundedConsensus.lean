/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusGap

/-!
# Consensus in bounded time

Manuscript source label: `bounded:cons:char`.

## Paper statement

Consensus is solvable in bounded time under message adversary~$A$ if and only if $\pi(A)$ is not dense in~$[0,1]$.

## Reading the proof

See the [proof locations](PROOFS.md#consensus-in-bounded-time) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.BoundedConsensus

/-- Reuses `Characterisation.ComponentGames.Consensus.bounded_consensus_iff_not_dense`. -/
theorem bounded_consensus_iff_not_dense :
    ∀ {V : Type} [Nontrivial V] (A : Set (ℕ → Graph)),
      (∃ (R : ℕ) (σ : StrategyPair V V (Option V) (Option V)), ComponentGames.Consensus.SolvesBy σ A R) ↔
        ¬Dense (geometricMap '' A) :=
  @_root_.Characterisation.ComponentGames.Consensus.bounded_consensus_iff_not_dense

end DistributedSynthesis.Paper.BoundedConsensus
