/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Inputs
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometricBridge
import DistributedSynthesis.Library.Distributed.EncodedNoDirectComputable

/-! Exact compatibility with the existing no-direct-reversal synthesis model. -/
namespace Characterisation
open DistributedSynthesis
namespace WithInputs

def NoDirectGraphs : Set (Nat → Graph) :=
  {x | ∀ n, (x n = Graph.left → x (n+1) ≠ Graph.right) ∧
    (x n = Graph.right → x (n+1) ≠ Graph.left)}

/-- The new definition specializes exactly to the existing finite-input model. -/
theorem noDirect_realizable_iff (d : Instance) :
    Realizable NoDirectGraphs d ↔ EncodedNoDirect.Realizable d := Iff.rfl

theorem noDirect_realizable_computable : ComputablePred (Realizable NoDirectGraphs) :=
  EncodedNoDirectComputable.realizable_computable.of_eq
    (fun d => (noDirect_realizable_iff d).symm)

/-- The known decidable adversary has graph-only holes: append a forbidden
right-to-left reversal to any finite history. -/
theorem noDirect_geometric_holes : GeometricHoles NoDirectGraphs := by
  apply (geometric_holes_iff_prefix_holes _).mpr
  intro h _
  refine ⟨[Graph.right, Graph.left], ?_⟩
  rintro ⟨x, hx, hp⟩
  have atRight := congrArg (fun w => w.getD h.length Graph.both) hp
  have atLeft := congrArg (fun w => w.getD (h.length+1) Graph.both) hp
  have get (n i : Nat) (hi : i < n) : (graphPrefix x n).getD i Graph.both = x i := by
    simp [graphPrefix, hi]
  dsimp only at atRight atLeft
  erw [get _ _ (by simp)] at atRight
  erw [get _ _ (by simp)] at atLeft
  have hr : x h.length = Graph.right := by
    simpa [List.getD, List.getElem?_append] using atRight
  have hl : x (h.length+1) = Graph.left := by
    simpa [List.getD, List.getElem?_append] using atLeft
  exact (hx h.length).2 hr hl

end WithInputs
end Characterisation
