/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ViewPathIsomorphism

/-!
# The inputless view complex is a path

Manuscript source label: `lem:complex:is:line`.

## Paper statement

The inputless round-$r$ view complex is a line of length~$3^r$.

## Correspondence

The equivalence enumerates all actual reachable vertices. The edge and adjacency
declarations exclude additional edges.

## Reading the proof

See the [proof locations](PROOFS.md#the-inputless-view-complex-is-a-path) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ViewPath

/-- Reuses `Characterisation.viewCoordinateEquiv`. -/
noncomputable abbrev viewCoordinateEquiv :
    (r : ℕ) → { v : FullViewPath.Vertex // PaddingProjection.Reachable r v } ≃ Fin (3 ^ r + 1) :=
  @_root_.Characterisation.viewCoordinateEquiv

/-- Reuses `Characterisation.view_edge_iff_consecutive`. -/
theorem view_edge_iff_consecutive :
    ∀ (r : ℕ) (u v : { v : FullViewPath.Vertex // PaddingProjection.Reachable r v }),
      (∃ (h : List Graph),
          h.length = r ∧
            ↑u = FullViewPath.left (FullViewPath.evaluate h) ∧ ↑v = FullViewPath.right (FullViewPath.evaluate h)) ↔
        ((viewCoordinateEquiv r) v).val = ((viewCoordinateEquiv r) u).val + 1 :=
  @_root_.Characterisation.view_edge_iff_consecutive

/-- Reuses `Characterisation.view_adjacent_iff_consecutive`. -/
theorem view_adjacent_iff_consecutive :
    ∀ (r : ℕ) (u v : { v : FullViewPath.Vertex // PaddingProjection.Reachable r v }),
      ((∃ (h : List Graph),
            h.length = r ∧
              ↑u = FullViewPath.left (FullViewPath.evaluate h) ∧ ↑v = FullViewPath.right (FullViewPath.evaluate h)) ∨
          ∃ (h : List Graph),
            h.length = r ∧
              ↑v = FullViewPath.left (FullViewPath.evaluate h) ∧ ↑u = FullViewPath.right (FullViewPath.evaluate h)) ↔
        ((viewCoordinateEquiv r) v).val = ((viewCoordinateEquiv r) u).val + 1 ∨
          ((viewCoordinateEquiv r) u).val = ((viewCoordinateEquiv r) v).val + 1 :=
  @_root_.Characterisation.view_adjacent_iff_consecutive

end DistributedSynthesis.Paper.ViewPath
