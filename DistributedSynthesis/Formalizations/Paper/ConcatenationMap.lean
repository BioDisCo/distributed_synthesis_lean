/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryConcatenation

/-!
# Removing a prefix from the geometric image

Manuscript source label: `concat:pi`.

## Paper statement

$\displaystyle
    \pi(h^{-1}A) =
    \begin{cases}
        3^{\lvert h\rvert} \pi(A \cap h\cdot\Gamma^\omega) - j(h) & \text{if $j(h)$ is even}\\
        j(h) + 1 - 3^{\lvert h\rvert} \pi(A \cap h\cdot \Gamma^\omega) & \text{if $j(h)$ is odd}
    \end{cases}$

## Reading the proof

See the [proof locations](PROOFS.md#removing-a-prefix-from-the-geometric-image) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ConcatenationMap

/-- Reuses `Characterisation.coordinate_prepend`. -/
theorem coordinate_prepend :
    ∀ (h : List Graph) (word : ℕ → Graph),
      prefixRescale h (coordinate (prependGraphs h word)) = coordinate word :=
  @_root_.Characterisation.coordinate_prepend

/-- Reuses `Characterisation.coordinate_residual_image`. -/
theorem coordinate_residual_image :
    ∀ (A : Set (ℕ → Graph)) (h : List Graph),
      coordinate '' Residual A h = prefixRescale h '' coordinate '' (A ∩ {word : ℕ → Graph | graphPrefix word h.length = h}) :=
  @_root_.Characterisation.coordinate_residual_image

end DistributedSynthesis.Paper.ConcatenationMap
