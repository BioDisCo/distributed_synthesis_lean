/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusConnected

/-!
# Empty interior implies repeated consensus

Manuscript source label: `lem:empty-interior-repeated-consensus`.

## Paper statement

If $\pi(A)$ has empty interior, then consensus is repeatedly solvable under message adversary~$A$.

## Reading the proof

See the [proof locations](PROOFS.md#empty-interior-implies-repeated-consensus) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.EmptyInterior

/-- Reuses `Characterisation.ComponentGames.Consensus.repeated_consensus_of_empty_interior`. -/
theorem repeated_consensus_of_empty_interior :
    ∀ {V : Type} [Nonempty V] (A : Set (ℕ → Graph)),
      interior (geometricMap '' A) = ∅ →
        ∀ (h : List Graph), ∃ (σ : StrategyPair V V (Option V) (Option V)), ComponentGames.Consensus.Solves σ (Residual A h) :=
  @_root_.Characterisation.ComponentGames.Consensus.repeated_consensus_of_empty_interior

end DistributedSynthesis.Paper.EmptyInterior
