/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusConnected

/-!
# Consensus and the geometric image

Manuscript source label: `cons:char`.

## Paper statement

Consensus is solvable under message adversary~$A$ if and only if $\pi(A) \neq [0,1]$.

## Reading the proof

See the [proof locations](PROOFS.md#consensus-and-the-geometric-image-and-the-geometric-image-and-the-geometric-image) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.Consensus

/-- Reuses `Characterisation.ComponentGames.Consensus.consensus_iff_image_ne_univ`. -/
theorem consensus_iff_image_ne_univ :
    ∀ {V : Type} [Nontrivial V] (A : Set (ℕ → Graph)),
      (∃ (σ : StrategyPair V V (Option V) (Option V)), ComponentGames.Consensus.Solves σ A) ↔ geometricMap '' A ≠ Set.univ :=
  @_root_.Characterisation.ComponentGames.Consensus.consensus_iff_image_ne_univ

end DistributedSynthesis.Paper.Consensus
