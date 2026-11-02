/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.CellBasis
import DistributedSynthesis.Library.Distributed.GraphAdversaries.UniformRowHoles
import Mathlib.Data.List.GetD

/-! The geometric/prefix bridge for arbitrary adversaries. Regularity is
needed only for the final uniform finite-row bound, not for this equivalence. -/

namespace Characterisation

open DistributedSynthesis Set

theorem graphPrefix_take (x : Nat → Graph) (m n : Nat) (hmn : m ≤ n) :
    (graphPrefix x n).take m = graphPrefix x m := by
  apply List.ext_getElem
  · simp [graphPrefix, hmn]
  · intro i hi hj
    simp [graphPrefix]

def extendGraphs (h : List Graph) : Nat → Graph := fun n => h.getD n Graph.both

theorem extendGraphs_prefix (h : List Graph) :
    graphPrefix (extendGraphs h) h.length = h := by
  apply List.ext_getElem
  · simp [graphPrefix]
  · intro i hi hj
    simp [graphPrefix, extendGraphs]

theorem livePrefix_closed (A : Set (Nat → Graph)) : PrefixClosed (LivePrefix A) := by
  rintro h u ⟨x, hx, hp⟩
  refine ⟨x, hx, ?_⟩
  have takeEq := congrArg (List.take h.length) hp
  rw [graphPrefix_take x h.length (h ++ u).length (by simp)] at takeEq
  simpa using takeEq

theorem coordinate_in_cell_of_prefix (x : Nat → Graph) (h : List Graph)
    (prefixEq : graphPrefix x h.length = h) :
    coordinate x ∈ Icc (leftEndpoint h) (rightEndpoint h) := by
  simpa only [prefixEq] using coordinate_in_prefix_cell x h.length

theorem prefix_holes_imply_geometric_holes (A : Set (Nat → Graph))
    (holes : HasPrefixHoles (LivePrefix A)) : GeometricHoles A := by
  intro U openU nonemptyU
  obtain ⟨h, _, insideU⟩ := exists_closed_cell_in_open U openU nonemptyU 0
  by_cases live : LivePrefix A h
  · obtain ⟨u, missing⟩ := holes h live
    refine ⟨cellInterior (h ++ u), cellInterior_open _, cellInterior_nonempty _, ?_,
      missing_prefix_gives_hole A _ missing⟩
    intro z hz
    have nested := endpoints_append h u
    exact insideU z ⟨nested.1.trans hz.1.le, hz.2.le.trans nested.2⟩
  · exact ⟨cellInterior h, cellInterior_open _, cellInterior_nonempty _,
      fun z hz => insideU z ⟨hz.1.le, hz.2.le⟩,
      missing_prefix_gives_hole A h live⟩

theorem geometric_holes_imply_prefix_holes (A : Set (Nat → Graph))
    (holes : GeometricHoles A) : HasPrefixHoles (LivePrefix A) := by
  apply (prefixHoles_iff_no_fullCone _).mpr
  rintro ⟨h, cone⟩
  obtain ⟨V, openV, nonemptyV, sub, disj⟩ :=
    holes (cellInterior h) (cellInterior_open h) (cellInterior_nonempty h)
  obtain ⟨w, deep, insideV⟩ := exists_closed_cell_in_open V openV nonemptyV h.length
  have extendInV : geometricMap (extendGraphs w) ∈ V :=
    insideV _ (coordinate_in_cell_of_prefix _ w (extendGraphs_prefix w))
  have parentPrefix : graphPrefix (extendGraphs w) h.length = h :=
    interior_cell_forces_prefix _ h (sub extendInV)
  have takeEq : w.take h.length = h := by
    rw [← extendGraphs_prefix w, graphPrefix_take _ _ _ deep, parentPrefix]
  have split : w = h ++ w.drop h.length := by
    have split := List.take_append_drop h.length w
    rw [takeEq] at split
    exact split.symm
  have liveW : LivePrefix A w := by rw [split]; exact cone _
  obtain ⟨x, hx, px⟩ := liveW
  have xInV : geometricMap x ∈ V := insideV _ (coordinate_in_cell_of_prefix x w px)
  exact Set.disjoint_left.mp disj xInV ⟨x, hx, rfl⟩

/-- Open holes at every geometric scale are exactly forbidden finite
continuations below every live prefix. No regularity assumption is needed. -/
theorem geometric_holes_iff_prefix_holes (A : Set (Nat → Graph)) :
    GeometricHoles A ↔ HasPrefixHoles (LivePrefix A) :=
  ⟨geometric_holes_imply_prefix_holes A, prefix_holes_imply_geometric_holes A⟩

theorem geometric_holes_iff_no_full_cone (A : Set (Nat → Graph)) :
    GeometricHoles A ↔ ¬ ∃ h, FullCone (LivePrefix A) h :=
  (geometric_holes_iff_prefix_holes A).trans (prefixHoles_iff_no_fullCone _)

/-- With an explicit finite-state recognizer of the live prefix language,
geometric holes yield a uniform bound on surviving finite-row intervals. -/
theorem geometric_holes_bound_rows (A : Set (Nat → Graph))
    {Q : Type*} [Fintype Q] (M : Recognizer Graph Q)
    (recognizes : ∀ w, LivePrefix A w ↔ M.eval w ∈ M.accept)
    (holes : GeometricHoles A) :
    ∃ K, ∀ t a b, a ≤ b → b ≤ 3 ^ t →
      (∀ j, a ≤ j → j < b → LiveIndex (LivePrefix A) t j) → b - a < K :=
  regular_prefix_holes_bound_rows M _ recognizes (livePrefix_closed A)
    ((geometric_holes_iff_prefix_holes A).mp holes)

end Characterisation
