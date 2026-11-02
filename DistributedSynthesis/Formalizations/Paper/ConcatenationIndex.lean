/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryConcatenation

/-!
# Removing a prefix from an edge index

Manuscript source label: `concat:pos`.

## Paper statement

$\displaystyle
    j(k) =
    \begin{cases}
        j(h\cdot k) - 3^{\lvert k\rvert} j(h) & \text{if $j(h)$ is even}\\
        3^{\lvert k\rvert}(j(h)+1) - j(h\cdot k) - 1 & \text{if $j(h)$ is odd}
    \end{cases}$

## Reading the proof

See the [proof locations](PROOFS.md#removing-a-prefix-from-an-edge-index) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ConcatenationIndex

/-- Reuses `Characterisation.pathIndex_concat`. -/
theorem pathIndex_concat :
    ∀ (h u : List Graph),
      (pathIndex h % 2 = 0 → pathIndex (h ++ u) = 3 ^ u.length * pathIndex h + pathIndex u) ∧
        (pathIndex h % 2 = 1 → pathIndex (h ++ u) + pathIndex u + 1 = 3 ^ u.length * (pathIndex h + 1)) :=
  @_root_.Characterisation.pathIndex_concat

/-- Reuses `Characterisation.pathIndex_suffix`. -/
theorem pathIndex_suffix :
    ∀ (h u : List Graph),
      pathIndex u =
        if pathIndex h % 2 = 0 then pathIndex (h ++ u) - 3 ^ u.length * pathIndex h
        else 3 ^ u.length * (pathIndex h + 1) - pathIndex (h ++ u) - 1 :=
  @_root_.Characterisation.pathIndex_suffix

end DistributedSynthesis.Paper.ConcatenationIndex
