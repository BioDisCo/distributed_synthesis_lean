/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ViewPathIsomorphism

/-!
# The extreme vertices

Manuscript source label: `lem:extreme-vertex`.

## Paper statement

The view $v_p\big( (p \rightarrow \bar{p})^r \big)$ has a single adjacent view in the inputless round-$r$ view complex.

## Reading the proof

See the [proof locations](PROOFS.md#the-extreme-vertices) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ExtremeVertices

/-- Reuses `Characterisation.extreme_views_unique_neighbors`. -/
theorem extreme_views_unique_neighbors :
    ∀ (r : ℕ),
      (∃! v : View Unit Unit Proc.two,
          ∃ (h : List Graph),
            h.length = r ∧
              (FullViewPath.evaluate h).one = (FullViewPath.evaluate (List.replicate r Graph.right)).one ∧
                (FullViewPath.evaluate h).two = v) ∧
        ∃! v : View Unit Unit Proc.one,
          ∃ (h : List Graph),
            h.length = r ∧
              (FullViewPath.evaluate h).two = (FullViewPath.evaluate (List.replicate r Graph.left)).two ∧
                (FullViewPath.evaluate h).one = v :=
  @_root_.Characterisation.extreme_views_unique_neighbors

/-- Reuses `Characterisation.extreme_view_coordinates`. -/
theorem extreme_view_coordinates :
    ∀ (r : ℕ),
      PaddingProjection.coordinate (Sum.inl (FullViewPath.evaluate (List.replicate r Graph.right)).one) = 0 ∧
        PaddingProjection.coordinate (Sum.inr (FullViewPath.evaluate (List.replicate r Graph.left)).two) = 3 ^ r :=
  @_root_.Characterisation.extreme_view_coordinates

end DistributedSynthesis.Paper.ExtremeVertices
