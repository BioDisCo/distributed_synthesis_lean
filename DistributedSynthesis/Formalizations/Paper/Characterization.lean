/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Results.HolesCharacterization

/-!
# Nowhere denseness characterizes decidability

Manuscript source label: `thm:undecidability:adversary`.

## Paper statement

Let $A$ be an $\omega$-regular message adversary.
    The $\textsc{LL-Synthesis}(A)$ problem is decidable if and only if $\pi(A)$ is nowhere dense.

## Correspondence

The instance includes arbitrary finite nonempty private input and output alphabets. The
graph promise constrains communication only. The topology on the interval is relative.

## Reading the proof

See the [proof locations](PROOFS.md#nowhere-denseness-characterizes-decidability) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.Characterization

/-- Reuses `DistributedSynthesis.GraphAdversaries.realizable_computable_iff_nowhere_dense`. -/
theorem realizable_computable_iff_nowhere_dense :
    ∀ (A : Set (ℕ → Graph)),
      GraphAdversaries.OmegaRegular A →
        (ComputablePred (GraphAdversaries.Realizable A) ↔ IsNowhereDense (GraphAdversaries.geometricMap '' A)) :=
  @_root_.DistributedSynthesis.GraphAdversaries.realizable_computable_iff_nowhere_dense

end DistributedSynthesis.Paper.Characterization
