/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Corollary.CorFiniteedgetypes
import DistributedSynthesis.Formalizations.Lemma.LemEndpointwindowpreimage

/-!
# Finite substitution update for edge types
-/

namespace DistributedSynthesis

universe u v w

/--
The summary contribution of a successor block, started from an existing
accumulator.
-/
def blockSummaryFrom
    {NewEdge : Type v}
    (S : PathSummarySemigroup.{v, w} NewEdge)
    (acc : S.Summary)
    (block : List NewEdge) :
    S.Summary :=
  block.foldl (fun current edge => S.multiply current (S.ofEdge edge)) acc

/-- Folding over an expanded path is the same as folding block-by-block. -/
theorem foldl_expandPath
    {OldEdge : Type u} {NewEdge : Type v}
    (S : PathSummarySemigroup.{v, w} NewEdge)
    (block : OldEdge -> List NewEdge)
    (path : TypedPath OldEdge)
    (acc : S.Summary) :
    (expandPath block path).foldl
        (fun current edge => S.multiply current (S.ofEdge edge)) acc =
      path.foldl (fun current edge => blockSummaryFrom S current (block edge)) acc := by
  induction path generalizing acc with
  | nil =>
      rfl
  | cons edge rest ih =>
      unfold expandPath
      simp [List.foldl_append, blockSummaryFrom]
      exact ih (List.foldl (fun current edge => S.multiply current (S.ofEdge edge)) acc (block edge))

/--
A path expansion summary is computed by replacing each old edge by the product
of the summaries of its successor block.
-/
theorem pathSummaryValue_expandPath
    {OldEdge : Type u} {NewEdge : Type v}
    (S : PathSummarySemigroup.{v, w} NewEdge)
    (block : OldEdge -> List NewEdge)
    (path : TypedPath OldEdge) :
    pathSummaryValue S (expandPath block path) =
      path.foldl (fun acc edge => blockSummaryFrom S acc (block edge)) S.empty := by
  exact foldl_expandPath S block path S.empty

/--
Corollary `cor:substitutionupdate`: if each old edge determines its successor
block, the finite semigroup summary of the expanded path is obtained by the
finite fold that substitutes each old factor by its block product.
-/
theorem finite_substitution_update_for_edge_types
    {OldEdge : Type u} {NewEdge : Type v}
    (S : PathSummarySemigroup.{v, w} NewEdge)
    (block : OldEdge -> List NewEdge)
    (path : TypedPath OldEdge) :
    pathSummaryValue S (expandPath block path) =
      path.foldl (fun acc edge => blockSummaryFrom S acc (block edge)) S.empty :=
  pathSummaryValue_expandPath S block path

end DistributedSynthesis
