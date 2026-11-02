/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryConcatenation

/-!
# Removing a prefix from an interval

Manuscript source label: `concat:interval`.

## Paper statement

$\displaystyle
    J(k) =
    \begin{cases}
        3^{\lvert h\rvert} J(h\cdot k) - j(h) & \text{if $j(h)$ is even}\\
        j(h) + 1 - 3^{\lvert h\rvert} J(h\cdot k) & \text{if $j(h)$ is odd}
    \end{cases}$

## Reading the proof

See the [proof locations](PROOFS.md#removing-a-prefix-from-an-interval) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ConcatenationCell

/-- Reuses `Characterisation.endpoints_concat`. -/
theorem endpoints_concat :
    ∀ (h u : List Graph),
      (pathIndex h % 2 = 0 →
          3 ^ h.length * leftEndpoint (h ++ u) - ↑(pathIndex h) = leftEndpoint u ∧
            3 ^ h.length * rightEndpoint (h ++ u) - ↑(pathIndex h) = rightEndpoint u) ∧
        (pathIndex h % 2 = 1 →
          ↑(pathIndex h) + 1 - 3 ^ h.length * rightEndpoint (h ++ u) = leftEndpoint u ∧
            ↑(pathIndex h) + 1 - 3 ^ h.length * leftEndpoint (h ++ u) = rightEndpoint u) :=
  @_root_.Characterisation.endpoints_concat

/-- Reuses `Characterisation.prefixRescale_cell`. -/
theorem prefixRescale_cell :
    ∀ (h u : List Graph),
      prefixRescale h '' Set.Icc (leftEndpoint (h ++ u)) (rightEndpoint (h ++ u)) =
        Set.Icc (leftEndpoint u) (rightEndpoint u) :=
  @_root_.Characterisation.prefixRescale_cell

end DistributedSynthesis.Paper.ConcatenationCell
