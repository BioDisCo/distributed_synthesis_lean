/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.Adversaries
import DistributedSynthesis.Library.Distributed.GraphAdversaries.SafetyClosure

/-!
# A dense residual adversary

Manuscript source label: `lem:not:nowhere:dense:is:dense:somewhere`.

## Paper statement

If $\pi(A)$ is not nowhere dense, then there exists a finite graph history $h\in\Gamma^*$ such that~$h^{-1}A$ is dense in~$\Gamma^\omega$.

## Reading the proof

See the [proof locations](PROOFS.md#a-dense-residual-adversary) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.DenseResidual

universe u_1

/-- Reuses `Characterisation.non_nowhere_dense_has_dense_residual`. -/
theorem non_nowhere_dense_has_dense_residual :
    ∀ [inst : TopologicalSpace Graph] [DiscreteTopology Graph]
      (A : Set (ℕ → Graph)), ¬IsNowhereDense (geometricMap '' A) → ∃ (h : List Graph), Dense (Residual A h) :=
  @_root_.Characterisation.non_nowhere_dense_has_dense_residual

/-- Reuses `Characterisation.prefixDense_iff_dense`. -/
theorem prefixDense_iff_dense :
    ∀ {α : Type u_1} [inst : TopologicalSpace α] [DiscreteTopology α] (A : Set (ℕ → α)),
      PrefixDense A ↔ Dense A :=
  @_root_.Characterisation.prefixDense_iff_dense

end DistributedSynthesis.Paper.DenseResidual
