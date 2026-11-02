/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentBounds

/-!
# Computing the position of a view

Manuscript source label: `lem:find_index`.

The position of an initial view is 0 for process 1 and 1 for process 2.
A nonreceiving view has position three times its previous position.
A receiving view has position own + 2 * other.

The library computes this as `PaddingProjection.project (fun _ => true)`.
The constant-true argument means every round is active. On tagged vertices,
this is precisely `PaddingProjection.coordinate`; `actual_endpoint_indices`
identifies it with the left and right positions of each actual view edge.
The universal process parameter covers both displayed rows in the paper.

## Reading the proof

See the [proof locations](PROOFS.md#computing-the-position-of-a-view) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

namespace DistributedSynthesis.Paper.FindIndex
open FullViewPath PaddingProjection

/-- The two initial vertices. -/
theorem initial_positions :
    project (fun _ => true) (.empty .one) = 0 ∧
      project (fun _ => true) (.empty .two) = 1 := ⟨rfl, rfl⟩

/-- Nonreception keeps only the process's own view. -/
theorem nonreceiving_position {p : Proc} (v : View Unit Unit p) (x : PSum Unit Unit) :
    project (fun _ => true) (.noRecv v x) = 3 * project (fun _ => true) v := rfl

/-- Reception adds twice the other process's position. -/
theorem receiving_position {p : Proc}
    (own : View Unit Unit p) (other : View Unit Unit p.other) (x y : PSum Unit Unit) :
    project (fun _ => true) (.recv own x other y) =
      project (fun _ => true) own + 2 * project (fun _ => true) other := rfl

/-- These are the actual ordered positions, not merely a recursively assigned label. -/
theorem actual_endpoint_indices (h : List Graph) :
    coordinate (left (evaluate h)) = Characterisation.pathIndex h ∧
      coordinate (right (evaluate h)) = Characterisation.pathIndex h + 1 :=
  Characterisation.actual_endpoint_indices h

end DistributedSynthesis.Paper.FindIndex
