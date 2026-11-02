/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometricBridge
import DistributedSynthesis.Library.Distributed.GraphAdversaries.SafetyClosure
import Mathlib.Analysis.SpecificLimits.Basic

/-! Topology of the manuscript's existing reflected ternary map.
No regularity assumption is imposed on adversaries. -/
namespace Characterisation
open DistributedSynthesis Set

/-- The exact width of J(h). -/
theorem cell_width (h : List Graph) :
    rightEndpoint h - leftEndpoint h = (1 / 3 : ℝ) ^ h.length := by
  simp only [rightEndpoint, leftEndpoint, one_div_pow]
  ring

theorem dist_le_cell_width (h : List Graph) {x y : ℝ}
    (hx : x ∈ Icc (leftEndpoint h) (rightEndpoint h))
    (hy : y ∈ Icc (leftEndpoint h) (rightEndpoint h)) :
    dist x y ≤ (1 / 3 : ℝ) ^ h.length := by
  rw [Real.dist_eq, ← cell_width]
  exact abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩

/-- The nested intervals defining pi have only one common point. -/
theorem coordinate_unique (word : Nat → Graph) (x : ℝ)
    (inside : ∀ n, x ∈ Icc (leftEndpoint (graphPrefix word n))
      (rightEndpoint (graphPrefix word n))) : coordinate word = x := by
  by_contra different
  have positive : 0 < dist (coordinate word) x := dist_pos.mpr different
  obtain ⟨n, small⟩ := exists_pow_lt_of_lt_one positive (by norm_num : (1 / 3 : ℝ) < 1)
  have bound := dist_le_cell_width _ (coordinate_in_prefix_cell word n) (inside n)
  simp only [graphPrefix_length] at bound
  exact (not_lt_of_ge bound) small

/-- Sharing a long prefix makes the two images close, as in `pi:cont`. -/
theorem coordinate_dist_of_prefix (x y : Nat → Graph) (n : Nat)
    (same : graphPrefix x n = graphPrefix y n) :
    dist (coordinate x) (coordinate y) ≤ (1 / 3 : ℝ) ^ n := by
  have hy := coordinate_in_prefix_cell y n
  rw [← same] at hy
  simpa only [graphPrefix_length] using
    dist_le_cell_width _ (coordinate_in_prefix_cell x n) hy

theorem continuous_coordinate [TopologicalSpace Graph] [DiscreteTopology Graph] :
    Continuous coordinate := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε positive
  obtain ⟨n, small⟩ := exists_pow_lt_of_lt_one positive (by norm_num : (1 / 3 : ℝ) < 1)
  filter_upwards [(isOpen_agreeBefore x n).mem_nhds (fun _ _ => rfl)] with y agree
  have same : graphPrefix y n = graphPrefix x n := by
    unfold graphPrefix
    congr 1
    funext i
    exact (agree i.val i.isLt).symm
  exact (coordinate_dist_of_prefix y x n same).trans_lt small

theorem continuous_geometricMap [TopologicalSpace Graph] [DiscreteTopology Graph] :
    Continuous geometricMap := continuous_coordinate.subtype_mk coordinate_bounds

/-- Every point of a cell belongs to one of its three children. -/
theorem exists_child_cell (h : List Graph) (x : ℝ)
    (inside : x ∈ Icc (leftEndpoint h) (rightEndpoint h)) :
    ∃ g : Graph, x ∈ Icc (leftEndpoint (h ++ [g])) (rightEndpoint (h ++ [g])) := by
  have pos : (0 : ℝ) < 3 ^ h.length := by positivity
  have lower : (pathIndex h : ℝ) ≤ x * 3 ^ h.length :=
    (div_le_iff₀ pos).mp inside.1
  have upper : x * 3 ^ h.length ≤ (pathIndex h : ℝ) + 1 :=
    (le_div_iff₀ pos).mp inside.2
  have digit : ∃ d : Nat, d < 3 ∧
      3 * pathIndex h + d ≤ x * (3 ^ h.length * 3) ∧
      x * (3 ^ h.length * 3) ≤ 3 * pathIndex h + d + 1 := by
    by_cases first : x * (3 ^ h.length * 3) ≤ 3 * pathIndex h + 1
    · exact ⟨0, by omega, by push_cast; nlinarith, by simpa using first⟩
    · by_cases second : x * (3 ^ h.length * 3) ≤ 3 * pathIndex h + 2
      · exact ⟨1, by omega, by push_cast; linarith, by push_cast; linarith⟩
      · exact ⟨2, by omega, by push_cast; linarith, by push_cast; nlinarith⟩
  obtain ⟨d, small, lo, hi⟩ := digit
  obtain ⟨g, eq⟩ := indexStep_surjective_digit (pathIndex h) d small
  refine ⟨g, ?_, ?_⟩
  · simp only [leftEndpoint, pathIndex_append, eq, List.length_append,
      List.length_singleton, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact (div_le_iff₀ (by positivity)).mpr lo
  · simp only [rightEndpoint, pathIndex_append, eq, List.length_append,
      List.length_singleton, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact (le_div_iff₀ (by positivity)).mpr hi

/-- Choose compatible prefixes containing x, following the English proof. -/
theorem geometricMap_surjective : Function.Surjective geometricMap := by
  classical
  intro x
  let CellAt := {h : List Graph // x.val ∈ Icc (leftEndpoint h) (rightEndpoint h)}
  let start : CellAt := ⟨[], by
    simpa only [leftEndpoint, rightEndpoint, pathIndex, List.foldl_nil, List.length_nil,
      Nat.cast_zero, pow_zero, zero_div, zero_add, div_one] using x.property⟩
  let pick (h : CellAt) : Graph := Classical.choose (exists_child_cell h.val x.val h.property)
  let next (h : CellAt) : CellAt :=
    ⟨h.val ++ [pick h], Classical.choose_spec (exists_child_cell h.val x.val h.property)⟩
  let cells (n : Nat) : CellAt := next^[n] start
  let word (n : Nat) : Graph := pick (cells n)
  have prefixes (n : Nat) : graphPrefix word n = (cells n).val := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [graphPrefix_succ, ih]
      change _ = (next^[n+1] start).val
      rw [Function.iterate_succ_apply']
  refine ⟨word, Subtype.ext ?_⟩
  apply coordinate_unique
  intro n
  rw [prefixes]
  exact (cells n).property

/-- `pi:closure`: continuous images of compact closed sets are closed. -/
theorem geometricMap_image_closure [TopologicalSpace Graph] [DiscreteTopology Graph]
    (A : Set (Nat → Graph)) : geometricMap '' closure A = closure (geometricMap '' A) := by
  exact (continuous_geometricMap.isClosedMap.closure_image_eq_of_continuous
    continuous_geometricMap A).symm

/-- `J:inclusion:iff:prefix`, with closed real intervals including endpoints. -/
theorem cell_subset_iff_prefix (h k : List Graph) :
    Icc (leftEndpoint k) (rightEndpoint k) ⊆ Icc (leftEndpoint h) (rightEndpoint h) ↔
      h.IsPrefix k := by
  constructor
  · intro subset
    have low := (subset (left_mem_Icc.mpr (endpoints_strict k).le)).1
    have high := (subset (right_mem_Icc.mpr (endpoints_strict k).le)).2
    have widths : (1 / 3 : ℝ) ^ k.length ≤ (1 / 3 : ℝ) ^ h.length := by
      rw [← cell_width, ← cell_width]
      linarith
    have powers : (3 : ℝ) ^ h.length ≤ 3 ^ k.length :=
      (one_div_le_one_div (by positivity) (by positivity)).mp
        (by simpa only [one_div_pow] using widths)
    have lengths : h.length ≤ k.length := by
      by_contra shorter
      have strict := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 3)
        (show k.length < h.length by omega)
      exact (not_le_of_gt strict) powers
    let mid := (leftEndpoint k + rightEndpoint k) / 2
    have middle : mid ∈ Ioo (leftEndpoint k) (rightEndpoint k) := by
      have := endpoints_strict k
      dsimp [mid]; constructor <;> linarith
    have unit : mid ∈ Icc (0 : ℝ) 1 :=
      ⟨(leftEndpoint_bounds k).1.trans middle.1.le,
       middle.2.le.trans (rightEndpoint_le_one k)⟩
    obtain ⟨word, eq⟩ := geometricMap_surjective ⟨mid, unit⟩
    have value : coordinate word = mid := congrArg Subtype.val eq
    have prefixK : graphPrefix word k.length = k :=
      interior_cell_forces_prefix word k (by simpa only [value] using middle)
    have prefixH : graphPrefix word h.length = h :=
      interior_cell_forces_prefix word h
        (by rw [value]; exact ⟨low.trans_lt middle.1, middle.2.trans_le high⟩)
    have take : k.take h.length = h := by
      rw [← prefixK, graphPrefix_take word _ _ lengths, prefixH]
    exact ⟨k.drop h.length, by simpa only [take] using List.take_append_drop h.length k⟩
  · rintro ⟨u, rfl⟩ x hx
    have bounds := endpoints_append h u
    exact ⟨bounds.1.trans hx.1, hx.2.trans bounds.2⟩

/-- The same finite-prefix cylinder is both open and closed. -/
theorem isClopen_agreeBefore {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    (x : Nat → α) (n : Nat) : IsClopen {y | AgreeBefore n x y} := by
  refine ⟨?_, isOpen_agreeBefore x n⟩
  have closed : IsClosed (⋂ k ∈ Finset.range n, {y : Nat → α | y k = x k}) :=
    isClosed_biInter fun k _ => isClosed_eq (continuous_apply k) continuous_const
  convert closed using 1
  ext y
  simp only [Set.mem_setOf_eq, AgreeBefore, Set.mem_iInter, Finset.mem_range]
  exact forall_congr' fun k => imp_congr_right fun _ => eq_comm

theorem graphPrefix_eq_iff_agreeBefore (x y : Nat → Graph) (n : Nat) :
    graphPrefix x n = graphPrefix y n ↔ AgreeBefore n x y := by
  constructor
  · intro same k hk
    exact congrFun (List.ofFn_injective same) ⟨k,hk⟩
  · intro agree
    unfold graphPrefix
    congr 1
    funext k
    exact agree k.val k.isLt

/-- `cones:are:clopen`, for the literal graph-prefix cylinder. -/
theorem isClopen_graphPrefix [TopologicalSpace Graph] [DiscreteTopology Graph]
    (h : List Graph) : IsClopen {word | graphPrefix word h.length = h} := by
  have eq : {word | graphPrefix word h.length = h} =
      {word | AgreeBefore h.length (extendGraphs h) word} := by
    ext word
    rw [mem_setOf_eq, mem_setOf_eq, ← graphPrefix_eq_iff_agreeBefore, extendGraphs_prefix]
    exact eq_comm
  rw [eq]
  exact isClopen_agreeBefore _ _

/-- `pi:inverse:J:interior`, including relative-interior points 0 and 1.
A sufficiently small cell around the image lies inside the open set, as in
 the manuscript's proof. -/
theorem relative_interior_cell_forces_prefix (word : Nat → Graph) (h : List Graph)
    (inside : geometricMap word ∈ interior
      {x : UnitInterval | x.val ∈ Icc (leftEndpoint h) (rightEndpoint h)}) :
    graphPrefix word h.length = h := by
  obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp isOpen_interior _ inside
  obtain ⟨n, small⟩ := exists_pow_lt_of_lt_one positive (by norm_num : (1 / 3 : ℝ) < 1)
  have subset : Icc (leftEndpoint (graphPrefix word n))
      (rightEndpoint (graphPrefix word n)) ⊆ Icc (leftEndpoint h) (rightEndpoint h) := by
    intro x hx
    have unit : x ∈ Icc (0 : ℝ) 1 :=
      ⟨(leftEndpoint_bounds _).1.trans hx.1, hx.2.trans (rightEndpoint_le_one _)⟩
    have near : (⟨x,unit⟩ : UnitInterval) ∈ Metric.ball (geometricMap word) ε := by
      rw [Metric.mem_ball, Subtype.dist_eq]
      exact (dist_le_cell_width _ hx (coordinate_in_prefix_cell word n)).trans_lt
        (by simpa only [graphPrefix_length] using small)
    have member := interior_subset (s := {x : UnitInterval |
      x.val ∈ Icc (leftEndpoint h) (rightEndpoint h)}) (ball near)
    exact member
  obtain ⟨u, eq⟩ := (cell_subset_iff_prefix h (graphPrefix word n)).mp subset
  have lengths : h.length ≤ n := by
    have := congrArg List.length eq
    simp only [List.length_append, graphPrefix_length] at this
    omega
  have take := graphPrefix_take word h.length n lengths
  rw [← eq, List.take_left] at take
  exact take.symm

end Characterisation
