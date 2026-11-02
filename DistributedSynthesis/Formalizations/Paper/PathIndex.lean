/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentBounds
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryCoding

/-!
# The index of an edge

Manuscript source label: `lem:j`.

## Paper statement

For all $h\in\Gamma^*$ and $\graph\in\Gamma$, we have
\begin{equation}
    j(h\graph) = 3j(h) +
    \begin{cases}
        \delta(\graph) & \text{if $j(h)$ is even} \\
        2 - \delta(\graph) & \text{if $j(h)$ is odd}\enspace.
    \end{cases}
    \end{equation}

## Reading the proof

See the [proof locations](PROOFS.md#the-index-of-an-edge) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.PathIndex

/-- Reuses `Characterisation.pathIndex_append`. -/
theorem pathIndex_append :
    ∀ (h : List Graph) (g : Graph), pathIndex (h ++ [g]) = indexStep (pathIndex h) g :=
  @_root_.Characterisation.pathIndex_append

/-- Reuses `Characterisation.orientation_agrees`. -/
theorem orientation_agrees :
    ∀ (h : List Graph), (FullViewPath.evaluate h).oneLeft = decide (pathIndex h % 2 = 0) :=
  @_root_.Characterisation.orientation_agrees

/-- Reuses `Characterisation.actual_endpoint_indices`. -/
theorem actual_endpoint_indices :
    ∀ (h : List Graph),
      PaddingProjection.coordinate (FullViewPath.left (FullViewPath.evaluate h)) = pathIndex h ∧
        PaddingProjection.coordinate (FullViewPath.right (FullViewPath.evaluate h)) = pathIndex h + 1 :=
  @_root_.Characterisation.actual_endpoint_indices

end DistributedSynthesis.Paper.PathIndex
