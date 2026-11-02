/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemEndpointwindowpreimage

/-!
# Regular three-edge path expansion
-/

namespace DistributedSynthesis

universe u v

/-- The local order in which a one-round expansion reads a three-edge block. -/
inductive ExpansionDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-- The paper's graph-label block for an oriented old edge. -/
def orientedGraphExpansionBlock : ExpansionDirection -> List Graph
  | .leftToRight => [.right, .both, .left]
  | .rightToLeft => [.left, .both, .right]

@[simp]
theorem orientedGraphExpansionBlock_length (dir : ExpansionDirection) :
    (orientedGraphExpansionBlock dir).length = 3 := by
  cases dir <;> rfl

@[simp]
theorem orientedGraphExpansionBlock_reverse (dir : ExpansionDirection) :
    (orientedGraphExpansionBlock dir).reverse =
      orientedGraphExpansionBlock
        (match dir with
        | .leftToRight => .rightToLeft
        | .rightToLeft => .leftToRight) := by
  cases dir <;> rfl

/-- Corollary `cor:pathexpansion`: each old oriented edge contributes one three-edge block. -/
theorem regular_three_edge_path_expansion
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (path : TypedPath OldEdge) :
    (expandPath block path).length = 3 * path.length := by
  exact length_expandPath block hlen path

/-- The graph-label part of the expansion has exactly the two orientations stated in the paper. -/
theorem regular_three_edge_graph_block :
    orientedGraphExpansionBlock .leftToRight = [.right, .both, .left] ∧
      orientedGraphExpansionBlock .rightToLeft = [.left, .both, .right] := by
  exact ⟨rfl, rfl⟩

end DistributedSynthesis
