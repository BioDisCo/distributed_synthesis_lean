/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentBounds

/-! Exact simple-path correspondence for the existing singleton-input views.
The vertex type is the existing reachable-view subtype, not a new view model. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

/-- All vertices of the inputless round-r view complex, in their path order. -/
noncomputable def viewCoordinateEquiv (r : Nat) :
    {v : Vertex // PaddingProjection.Reachable r v} ≃ Fin (3^r+1) :=
  Equiv.ofBijective (fun v => ⟨PaddingProjection.coordinate v.val,
    Nat.lt_succ_of_le (by simpa only [PaddingProjection.virtualDepth_all_active] using
      (PaddingProjection.project_le (active := fun _ => true) v.property))⟩) (by
    constructor
    · intro u v same
      apply Subtype.ext
      exact PaddingProjection.coordinate_injective u.property v.property (congrArg Fin.val same)
    · intro j
      obtain ⟨v, reachable, eq⟩ := PaddingProjection.project_surjective (fun _ => true) r j.val
        (by simpa only [PaddingProjection.virtualDepth_all_active] using Nat.le_of_lt_succ j.isLt)
      exact ⟨⟨v,reachable⟩, Fin.ext eq⟩)

@[simp] theorem viewCoordinateEquiv_val (r : Nat)
    (v : {v : Vertex // PaddingProjection.Reachable r v}) :
    (viewCoordinateEquiv r v).val = PaddingProjection.coordinate v.val := rfl

private theorem endpoints_reachable (h : List Graph) :
    PaddingProjection.Reachable h.length (left (evaluate h)) ∧
      PaddingProjection.Reachable h.length (right (evaluate h)) := by
  have visited := endpoints_visited ((mem_row_iff h.length (evaluate h)).mpr ⟨h,rfl,rfl⟩)
  exact ⟨PaddingProjection.visited_reachable visited.1, PaddingProjection.visited_reachable visited.2⟩

/-- Edges correspond exactly to consecutive coordinates. This proves both
that the row is simple and that it has no additional edges; `row_path`
alone would not establish either assertion. -/
theorem view_edge_iff_consecutive (r : Nat)
    (u v : {v : Vertex // PaddingProjection.Reachable r v}) :
    (∃ h : List Graph, h.length = r ∧ u.val = left (evaluate h) ∧ v.val = right (evaluate h)) ↔
      (viewCoordinateEquiv r v).val = (viewCoordinateEquiv r u).val + 1 := by
  simp only [viewCoordinateEquiv_val]
  constructor
  · rintro ⟨h, _, hu, hv⟩
    rw [hu, hv, (actual_endpoint_indices h).1, (actual_endpoint_indices h).2]
  · intro step
    have bound : PaddingProjection.coordinate u.val < 3^r := by
      have high := PaddingProjection.project_le (active := fun _ => true) v.property
      simp only [PaddingProjection.virtualDepth_all_active] at high
      change PaddingProjection.coordinate v.val ≤ 3^r at high
      omega
    obtain ⟨h, len, index⟩ := pathIndex_surjective r (PaddingProjection.coordinate u.val) bound
    have endpoints := endpoints_reachable h
    rw [len] at endpoints
    refine ⟨h, len, ?_, ?_⟩
    · apply PaddingProjection.coordinate_injective u.property endpoints.1
      rw [(actual_endpoint_indices h).1, index]
    · apply PaddingProjection.coordinate_injective v.property endpoints.2
      rw [(actual_endpoint_indices h).2, index, step]

/-- The undirected inputless view complex is isomorphic to the path on
3^r+1 vertices, hence has length 3^r (`lem:complex:is:line`). -/
theorem view_adjacent_iff_consecutive (r : Nat)
    (u v : {v : Vertex // PaddingProjection.Reachable r v}) :
    ((∃ h : List Graph, h.length = r ∧ u.val = left (evaluate h) ∧ v.val = right (evaluate h)) ∨
      (∃ h : List Graph, h.length = r ∧ v.val = left (evaluate h) ∧ u.val = right (evaluate h))) ↔
    ((viewCoordinateEquiv r v).val = (viewCoordinateEquiv r u).val + 1 ∨
      (viewCoordinateEquiv r u).val = (viewCoordinateEquiv r v).val + 1) := by
  rw [view_edge_iff_consecutive, view_edge_iff_consecutive]

/-- The permanently nonreceiving views are the two extreme coordinates. -/
theorem extreme_view_coordinates (r : Nat) :
    PaddingProjection.coordinate (.inl (evaluate (List.replicate r .right)).one) = 0 ∧
    PaddingProjection.coordinate (.inr (evaluate (List.replicate r .left)).two) = 3^r := by
  induction r with
  | zero => exact ⟨rfl,rfl⟩
  | succ r ih =>
    simp only [List.replicate_succ', at_append]
    change 3 * PaddingProjection.coordinate (.inl (evaluate (List.replicate r .right)).one) = 0 ∧
      3 * PaddingProjection.coordinate (.inr (evaluate (List.replicate r .left)).two) = 3^(r+1)
    rw [ih.1, ih.2]
    simp [pow_succ, Nat.mul_comm]

/-- There is only one history incident to the left extreme view. -/
theorem left_extreme_history_unique (r : Nat) (h : List Graph) (len : h.length = r)
    (same : (evaluate h).one = (evaluate (List.replicate r .right)).one) :
    h = List.replicate r .right := by
  have zero := (extreme_view_coordinates r).1
  have bound := (actual_process_index_bounds h).1.1
  have other := (actual_process_index_bounds (List.replicate r .right)).1.1
  change PaddingProjection.project (fun _ => true) (evaluate (List.replicate r .right)).one = 0 at zero
  rw [same, zero] at bound
  rw [zero] at other
  exact pathIndex_injective h _ (by simpa using len) (by omega)

/-- There is only one history incident to the right extreme view. -/
theorem right_extreme_history_unique (r : Nat) (h : List Graph) (len : h.length = r)
    (same : (evaluate h).two = (evaluate (List.replicate r .left)).two) :
    h = List.replicate r .left := by
  have high := (extreme_view_coordinates r).2
  have bound := (actual_process_index_bounds h).2.2
  have other := (actual_process_index_bounds (List.replicate r .left)).2.2
  change PaddingProjection.project (fun _ => true) (evaluate (List.replicate r .left)).two = 3^r at high
  rw [same, high] at bound
  rw [high] at other
  have small := pathIndex_lt h
  have smallOther := pathIndex_lt (List.replicate r .left)
  simp only [len, List.length_replicate] at small smallOther
  exact pathIndex_injective h _ (by simpa using len) (by omega)

/-- `lem:extreme-vertex`: the adjacent view is unique at both ends,
including round zero. -/
theorem extreme_views_unique_neighbors (r : Nat) :
    (∃! v : View Unit Unit .two, ∃ h : List Graph, h.length = r ∧
      (evaluate h).one = (evaluate (List.replicate r .right)).one ∧ (evaluate h).two = v) ∧
    (∃! v : View Unit Unit .one, ∃ h : List Graph, h.length = r ∧
      (evaluate h).two = (evaluate (List.replicate r .left)).two ∧ (evaluate h).one = v) := by
  constructor
  · refine ⟨(evaluate (List.replicate r .right)).two,
      ⟨List.replicate r .right, List.length_replicate .., rfl, rfl⟩, ?_⟩
    rintro v ⟨h, len, same, eq⟩
    rw [left_extreme_history_unique r h len same] at eq
    exact eq.symm
  · refine ⟨(evaluate (List.replicate r .left)).one,
      ⟨List.replicate r .left, List.length_replicate .., rfl, rfl⟩, ?_⟩
    rintro v ⟨h, len, same, eq⟩
    rw [right_extreme_history_unique r h len same] at eq
    exact eq.symm

/-- The vertices created below one history are exactly four consecutive
vertices of the next row. Together with `view_edge_iff_consecutive`, this
identifies the induced subgraph as a line of length three. -/
theorem child_vertices_iff_coordinate_interval (h : List Graph) (v : Vertex)
    (reachable : PaddingProjection.Reachable (h.length+1) v) :
    (∃ g : Graph, v = left (evaluate (h++[g])) ∨ v = right (evaluate (h++[g]))) ↔
      3 * pathIndex h ≤ PaddingProjection.coordinate v ∧
      PaddingProjection.coordinate v ≤ 3 * pathIndex h + 3 := by
  constructor
  · rintro ⟨g, rfl | rfl⟩
    · rw [(actual_endpoint_indices _).1, pathIndex_append]
      have bound := indexStep_bounds (pathIndex h) g
      omega
    · rw [(actual_endpoint_indices _).2, pathIndex_append]
      have bound := indexStep_bounds (pathIndex h) g
      omega
  · intro bound
    let d := PaddingProjection.coordinate v - 3 * pathIndex h
    have offset : PaddingProjection.coordinate v = 3 * pathIndex h + d := by dsimp [d]; omega
    by_cases before : d < 3
    · obtain ⟨g, index⟩ := indexStep_surjective_digit (pathIndex h) d before
      refine ⟨g, Or.inl ?_⟩
      apply PaddingProjection.coordinate_injective reachable
        (by simpa only [List.length_append, List.length_singleton] using (endpoints_reachable (h++[g])).1)
      rw [(actual_endpoint_indices _).1, pathIndex_append, index, offset]
    · have last : d = 3 := by dsimp [d] at *; omega
      obtain ⟨g, index⟩ := indexStep_surjective_digit (pathIndex h) 2 (by omega)
      refine ⟨g, Or.inr ?_⟩
      apply PaddingProjection.coordinate_injective reachable
        (by simpa only [List.length_append, List.length_singleton] using (endpoints_reachable (h++[g])).2)
      rw [(actual_endpoint_indices _).2, pathIndex_append, index, offset, last]

/-- All four coordinates in the induced child subgraph are realized. -/
theorem child_vertex_at_offset (h : List Graph) (d : Fin 4) :
    ∃ v : Vertex, PaddingProjection.Reachable (h.length+1) v ∧
      (∃ g : Graph, v = left (evaluate (h++[g])) ∨ v = right (evaluate (h++[g]))) ∧
      PaddingProjection.coordinate v = 3 * pathIndex h + d.val := by
  have small := pathIndex_lt h
  have bound : 3 * pathIndex h + d.val ≤ 3^(h.length+1) := by
    rw [pow_succ]
    have := d.isLt
    omega
  obtain ⟨v, reachable, eq⟩ := PaddingProjection.project_surjective (fun _ => true)
    (h.length+1) (3 * pathIndex h + d.val)
    (by simpa only [PaddingProjection.virtualDepth_all_active] using bound)
  refine ⟨v, reachable, (child_vertices_iff_coordinate_interval h v reachable).mpr ?_, eq⟩
  change PaddingProjection.coordinate v = _ at eq
  rw [eq]
  have := d.isLt
  omega

private theorem child_reachable (h : List Graph) (v : Vertex)
    (member : ∃ g : Graph, v = left (evaluate (h++[g])) ∨ v = right (evaluate (h++[g]))) :
    PaddingProjection.Reachable (h.length+1) v := by
  obtain ⟨g, rfl | rfl⟩ := member
  · simpa only [List.length_append, List.length_singleton] using (endpoints_reachable (h++[g])).1
  · simpa only [List.length_append, List.length_singleton] using (endpoints_reachable (h++[g])).2

/-- The four distinct vertices of the induced child subgraph, in order. -/
noncomputable def childCoordinateEquiv (h : List Graph) :
    {v : Vertex // ∃ g : Graph, v = left (evaluate (h++[g])) ∨ v = right (evaluate (h++[g]))} ≃ Fin 4 :=
  Equiv.ofBijective (fun v => ⟨PaddingProjection.coordinate v.val - 3 * pathIndex h, by
    have bound := (child_vertices_iff_coordinate_interval h v.val (child_reachable h v.val v.property)).mp v.property
    omega⟩) (by
    constructor
    · intro u v same
      apply Subtype.ext
      have bu := (child_vertices_iff_coordinate_interval h u.val (child_reachable h u.val u.property)).mp u.property
      have bv := (child_vertices_iff_coordinate_interval h v.val (child_reachable h v.val v.property)).mp v.property
      have eq := congrArg Fin.val same
      apply PaddingProjection.coordinate_injective (child_reachable h u.val u.property)
        (child_reachable h v.val v.property)
      change PaddingProjection.coordinate u.val - 3 * pathIndex h =
        PaddingProjection.coordinate v.val - 3 * pathIndex h at eq
      omega
    · intro d
      obtain ⟨v, _, member, eq⟩ := child_vertex_at_offset h d
      refine ⟨⟨v,member⟩, Fin.ext ?_⟩
      change PaddingProjection.coordinate v - 3 * pathIndex h = d.val
      rw [eq]
      omega)

/-- `lem:complex:is:line:single`: within these four vertices, the induced
edges of the full next-round complex are exactly the three path edges. -/
theorem induced_child_edge_iff (h : List Graph)
    (u v : {v : Vertex // ∃ g : Graph, v = left (evaluate (h++[g])) ∨ v = right (evaluate (h++[g]))}) :
    (∃ k : List Graph, k.length = h.length+1 ∧ u.val = left (evaluate k) ∧ v.val = right (evaluate k)) ↔
      (childCoordinateEquiv h v).val = (childCoordinateEquiv h u).val + 1 := by
  have hu := child_reachable h u.val u.property
  have hv := child_reachable h v.val v.property
  have bu := (child_vertices_iff_coordinate_interval h u.val hu).mp u.property
  have bv := (child_vertices_iff_coordinate_interval h v.val hv).mp v.property
  have edges := view_edge_iff_consecutive (h.length+1) ⟨u.val,hu⟩ ⟨v.val,hv⟩
  simp only [viewCoordinateEquiv_val] at edges
  rw [edges]
  change PaddingProjection.coordinate v.val = PaddingProjection.coordinate u.val + 1 ↔
    PaddingProjection.coordinate v.val - 3 * pathIndex h =
      PaddingProjection.coordinate u.val - 3 * pathIndex h + 1
  omega

end Characterisation
