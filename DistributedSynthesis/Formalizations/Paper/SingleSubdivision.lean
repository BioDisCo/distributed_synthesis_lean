/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ViewPathIsomorphism

/-!
# One round subdivides an edge into three

Manuscript source label: `lem:complex:is:line:single`.

## Paper statement

Let $h\in\Gamma^r$.
Then the subgraph of the inputless round-$(r+1)$ view complex induced by the set of views $\{ v_p(h \graph) \mid p\in\mathcal{P} \wedge \graph \in \Gamma\}$ is a line of length~$3$.

## Correspondence

The equivalence enumerates the four actual child vertices; the second declaration
identifies exactly the three induced edges. Fin 4 here counts vertices, not position
residues.

## Reading the proof

See the [proof locations](PROOFS.md#one-round-subdivides-an-edge-into-three) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.SingleSubdivision

/-- Reuses `Characterisation.childCoordinateEquiv`. -/
noncomputable abbrev childCoordinateEquiv :
    (h : List Graph) →
      { v : FullViewPath.Vertex //
          ∃ (g : Graph),
            v = FullViewPath.left (FullViewPath.evaluate (h ++ [g])) ∨
              v = FullViewPath.right (FullViewPath.evaluate (h ++ [g])) } ≃
        Fin 4 :=
  @_root_.Characterisation.childCoordinateEquiv

/-- Reuses `Characterisation.induced_child_edge_iff`. -/
theorem induced_child_edge_iff :
    ∀ (h : List Graph)
      (u v :
        { v : FullViewPath.Vertex //
          ∃ (g : Graph),
            v = FullViewPath.left (FullViewPath.evaluate (h ++ [g])) ∨
              v = FullViewPath.right (FullViewPath.evaluate (h ++ [g])) }),
      (∃ (k : List Graph),
          k.length = h.length + 1 ∧
            ↑u = FullViewPath.left (FullViewPath.evaluate k) ∧ ↑v = FullViewPath.right (FullViewPath.evaluate k)) ↔
        ((childCoordinateEquiv h) v).val = ((childCoordinateEquiv h) u).val + 1 :=
  @_root_.Characterisation.induced_child_edge_iff

end DistributedSynthesis.Paper.SingleSubdivision
