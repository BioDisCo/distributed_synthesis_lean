/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.ViewPaths

/-! # Local projection through communication padding

`active t` specifies whether round `t + 1` is simulated or padding. No process
is given a graph oracle: `project` reads only its own existing full view.
The two projected endpoints of a history are adjacent until the first one-way
padding round; thereafter they coincide. Since the whole depth row is a path
and the projection is nondecreasing, equality on those histories forces every
output to be constant on each projection fiber.

This file proves that information-preservation fact for every schedule and
every depth. It does not yet assert an LTL serialization reduction.
-/

namespace DistributedSynthesis.PaddingProjection
open FullViewPath ScalingRow

/-- The virtual path coordinate computed from a single physical local view.
In padding rounds a receiver follows the sender's prior projection. -/
def project (active : Nat → Bool) : {p : Proc} → View Unit Unit p → Nat
  | _, .empty .one => 0
  | _, .empty .two => 1
  | _, .noRecv v _ =>
      if active (depth v) then 3 * project active v else project active v
  | _, .recv v _ u _ =>
      if active (depth v) then project active v + 2 * project active u
      else project active u

def vertexProject (active : Nat → Bool) : Vertex → Nat :=
  Sum.elim (project active) (project active)

private def coreReverse (active : Nat → Bool) : List Graph → Bool
  | [] => true
  | g :: h => coreReverse active h && (active h.length || decide (g = .both))

/-- All padding graphs in the finite history are bidirectional. This is a
proof-side predicate, not an observation supplied to the processes. -/
def core (active : Nat → Bool) (h : List Graph) : Bool := coreReverse active h.reverse

@[simp] theorem core_nil (active : Nat → Bool) : core active [] = true := rfl
@[simp] theorem core_append (active : Nat → Bool) (h : List Graph) (g : Graph) :
    core active (h ++ [g]) = (core active h &&
      (active h.length || decide (g = .both))) := by
  simp [core, List.reverse_append, coreReverse]

/-- Exact contraction invariant on actual graph histories: an unspoiled edge
has length one, and an edge with a one-way padding round has length zero. -/
theorem projected_gap (active : Nat → Bool) (h : List Graph) :
    vertexProject active (right (evaluate h)) =
      vertexProject active (left (evaluate h)) + if core active h then 1 else 0 := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g ih =>
    have hd := at_depth h
    rw [at_append, core_append]
    cases ht : (evaluate h).oneLeft <;>
      cases ha : active h.length <;> cases hc : core active h <;> cases g <;>
      simp [vertexProject, left, right, ht, advance, advanceViews, project,
        Proc.other, hd.1, hd.2, ha, hc] at ih ⊢ <;> omega

theorem projected_mono (active : Nat → Bool) (h : List Graph) :
    vertexProject active (left (evaluate h)) ≤
      vertexProject active (right (evaluate h)) := by
  rw [projected_gap]
  exact Nat.le_add_right _ _

theorem collapsed_iff (active : Nat → Bool) (h : List Graph) :
    vertexProject active (left (evaluate h)) =
      vertexProject active (right (evaluate h)) ↔ core active h = false := by
  rw [projected_gap]
  cases core active h <;> simp

theorem fault_persists (active : Nat → Bool) (h tail : List Graph)
    (hh : core active h = false) : core active (h ++ tail) = false := by
  induction tail using List.reverseRecOn with
  | nil => simpa using hh
  | append_singleton tail g ih => simp [← List.append_assoc, ih]

/-- The finite-history condition in `fiber_agreement` is exactly the presence
of an earlier one-way padding round, not an additional environment restriction. -/
theorem core_false_iff (active : Nat → Bool) (h : List Graph) :
    core active h = false ↔ ∃ before g after,
      h = before ++ [g] ++ after ∧ active before.length = false ∧ g ≠ .both := by
  constructor
  · induction h using List.reverseRecOn with
    | nil => simp
    | append_singleton h g ih =>
      intro hc
      rw [core_append, Bool.and_eq_false_iff] at hc
      rcases hc with hc | hc
      · obtain ⟨before, f, after, he, ha, hf⟩ := ih hc
        exact ⟨before, f, after ++ [g], by simp [he, List.append_assoc], ha, hf⟩
      · have hb : active h.length = false ∧ g ≠ .both := by simpa using hc
        exact ⟨h, g, [], by simp, hb⟩
  · rintro ⟨before, g, after, rfl, ha, hg⟩
    apply fault_persists
    simp [ha, hg]

/-- Reachability retains the process tag; equality between two numbers does
not identify the underlying physical local views. -/
def Reachable (t : Nat) (v : Vertex) : Prop :=
  ∃ h : List Graph, h.length = t ∧
    (v = .inl (evaluate h).one ∨ v = .inr (evaluate h).two)

theorem reachable_visited {t : Nat} {v : Vertex} (hv : Reachable t v) :
    Path.Visits right (blind^[t] (left root)) (row t) v := by
  obtain ⟨h, ht, hv⟩ := hv
  have hm := (mem_row_iff t (evaluate h)).mpr ⟨h, ht, rfl⟩
  have he := endpoints_visited hm
  cases ho : (evaluate h).oneLeft <;>
    simp only [left, right, ho, Bool.false_eq_true, ↓reduceIte] at he
  all_goals rcases hv with rfl | rfl <;> first | exact he.1 | exact he.2

/-- The central soundness lemma. An arbitrary labeling that agrees after a
one-way padding round descends to the virtual coordinate, even though the
physical strategies retain every communication received during padding. -/
theorem fiber_agreement {Output : Type*} (active : Nat → Bool) (t : Nat)
    (label : Vertex → Output)
    (echo : ∀ h : List Graph, h.length = t → core active h = false →
      label (.inl (evaluate h).one) = label (.inr (evaluate h).two))
    {u v : Vertex} (hu : Reachable t u) (hv : Reachable t v)
    (hp : vertexProject active u = vertexProject active v) : label u = label v := by
  apply (row_path t).fiber_uniform (vertexProject active) label
    ?_ ?_ (reachable_visited hu) (reachable_visited hv) hp
  · intro s hs
    obtain ⟨h, _, rfl⟩ := (mem_row_iff t s).mp hs
    exact projected_mono active h
  · intro s hs hc
    obtain ⟨h, ht, rfl⟩ := (mem_row_iff t s).mp hs
    have he := echo h ht ((collapsed_iff active h).mp hc)
    cases ho : (evaluate h).oneLeft <;>
      simp only [left, right, ho, Bool.false_eq_true, ↓reduceIte]
    · exact he.symm
    · exact he

/-- The conclusion packaged as an actual factorization on reachable views.
No effectiveness of the arbitrary input labeling is assumed or claimed. -/
theorem factors_through_projection {Output : Type*} [Nonempty Output]
    (active : Nat → Bool) (t : Nat) (label : Vertex → Output)
    (echo : ∀ h : List Graph, h.length = t → core active h = false →
      label (.inl (evaluate h).one) = label (.inr (evaluate h).two)) :
    ∃ decoded : Nat → Output, ∀ v, Reachable t v →
      label v = decoded (vertexProject active v) := by
  classical
  let decoded : Nat → Output := fun k ↦
    if h : ∃ v, Reachable t v ∧ vertexProject active v = k then
      label h.choose else Classical.choice inferInstance
  refine ⟨decoded, ?_⟩
  intro v hv
  have hex : ∃ u, Reachable t u ∧ vertexProject active u = vertexProject active v :=
    ⟨v, hv, rfl⟩
  simp only [decoded, dif_pos hex]
  exact fiber_agreement active t label echo hv hex.choose_spec.1 hex.choose_spec.2.symm

/-- With no padding, every finite history is unspoiled. -/
@[simp] theorem core_all_active (h : List Graph) : core (fun _ ↦ true) h = true := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g ih => simp [ih]

/-- The ordinary coordinate is the projection with every round active. -/
def coordinate : Vertex → Nat := vertexProject (fun _ ↦ true)

/-- Exactness, including the owner tag: two reachable views of the same depth
have the same coordinate if and only if they are the very same tagged view. -/
theorem coordinate_injective {t : Nat} {u v : Vertex}
    (hu : Reachable t u) (hv : Reachable t v) (hp : coordinate u = coordinate v) : u = v := by
  exact fiber_agreement (fun _ ↦ true) t id
    (by intro h _ hc; simp at hc) hu hv hp

def virtualDepth (active : Nat → Bool) : Nat → Nat
  | 0 => 0
  | t+1 => virtualDepth active t + if active t then 1 else 0

def vertexDepth : Vertex → Nat := Sum.elim depth depth

@[simp] theorem vertexDepth_blind (v : Vertex) :
    vertexDepth (blind v) = vertexDepth v + 1 := by
  cases v <;> rfl

theorem vertexProject_blind (active : Nat → Bool) (v : Vertex) :
    vertexProject active (blind v) =
      if active (vertexDepth v) then 3 * vertexProject active v else vertexProject active v := by
  cases v <;> rfl

theorem boundary_depth (t : Nat) :
    vertexDepth (blind^[t] (left root)) = t ∧
    vertexDepth (blind^[t] (right root)) = t := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih => simp only [Function.iterate_succ_apply', vertexDepth_blind, ih.1, ih.2,
      and_self, implies_true]

theorem boundary_projection (active : Nat → Bool) (t : Nat) :
    vertexProject active (blind^[t] (left root)) = 0 ∧
    vertexProject active (blind^[t] (right root)) = 3 ^ virtualDepth active t := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    simp only [Function.iterate_succ_apply', vertexProject_blind,
      (boundary_depth t).1, (boundary_depth t).2, ih.1, ih.2, virtualDepth]
    cases active t <;> simp [pow_succ, Nat.mul_comm]

theorem visited_reachable {t : Nat} {v : Vertex}
    (hv : Path.Visits right (blind^[t] (left root)) (row t) v) : Reachable t v := by
  have hn : row t ≠ [] := by
    have hm := (mem_row_iff t (evaluate (List.replicate t .both))).mpr
      ⟨List.replicate t .both, by simp, rfl⟩
    intro he
    simp [he] at hm
  obtain ⟨s, hs, hv⟩ := (row_path t).visited_endpoint hn hv
  obtain ⟨h, ht, rfl⟩ := (mem_row_iff t s).mp hs
  refine ⟨h, ht, ?_⟩
  cases ho : (evaluate h).oneLeft <;>
    simp only [left, right, ho, Bool.false_eq_true, ↓reduceIte] at hv
  · exact hv.elim Or.inr Or.inl
  · exact hv

theorem project_le {active : Nat → Bool} {t : Nat} {v : Vertex}
    (hv : Reachable t v) : vertexProject active v ≤ 3 ^ virtualDepth active t := by
  have hb := (row_path t).projection_bounds (vertexProject active)
    (by
      intro s hs
      obtain ⟨h, _, rfl⟩ := (mem_row_iff t s).mp hs
      exact projected_mono active h) (reachable_visited hv)
  simpa only [(boundary_projection active t).2] using hb.2

/-- No virtual coordinate is lost by the padding contraction. -/
theorem project_surjective (active : Nat → Bool) (t k : Nat)
    (hk : k ≤ 3 ^ virtualDepth active t) :
    ∃ v, Reachable t v ∧ vertexProject active v = k := by
  obtain ⟨v, hv, hp⟩ := (row_path t).intermediate (vertexProject active)
    (by
      intro s hs
      obtain ⟨h, _, rfl⟩ := (mem_row_iff t s).mp hs
      rw [projected_gap]
      cases core active h <;> simp)
    k (by simp only [(boundary_projection active t).1]; omega)
    (by simpa only [(boundary_projection active t).2] using hk)
  exact ⟨v, visited_reachable hv, hp⟩

@[simp] theorem virtualDepth_all_active (t : Nat) : virtualDepth (fun _ ↦ true) t = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [virtualDepth, ih]

/-- Every physical view projects to exactly one reachable original tagged
view at the number of simulated rounds. This is an existence-and-uniqueness
theorem, with no injectivity or surjectivity premise left to the caller. -/
theorem unique_virtual_view (active : Nat → Bool) {t : Nat} {v : Vertex}
    (hv : Reachable t v) :
    ∃! u, Reachable (virtualDepth active t) u ∧ coordinate u = vertexProject active v := by
  obtain ⟨u, hu, hp⟩ := project_surjective (fun _ ↦ true) (virtualDepth active t)
    (vertexProject active v) (by simpa using (project_le (active := active) hv))
  refine ⟨u, ⟨hu, hp⟩, ?_⟩
  rintro w ⟨hw, he⟩
  exact coordinate_injective hw hu (he.trans hp.symm)

end DistributedSynthesis.PaddingProjection
