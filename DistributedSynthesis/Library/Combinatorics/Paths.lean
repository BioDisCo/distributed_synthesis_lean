/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Tactic

/-! # Shared endpoints, uniform labels, and exact telescoping along a row -/

namespace DistributedSynthesis.ScalingRow

universe u v
variable {Vertex : Type u} {Edge : Type v}

inductive Path (left right : Edge → Vertex) : Vertex → List Edge → Vertex → Prop
  | nil (a) : Path left right a [] a
  | cons (e : Edge) {es : List Edge} {b : Vertex} :
      Path left right (right e) es b → Path left right (left e) (e::es) b

namespace Path
variable {left right : Edge → Vertex} {a b c : Vertex} {xs ys : List Edge}

theorem append (h : Path left right a xs b) (h' : Path left right b ys c) :
    Path left right a (xs ++ ys) c := by
  induction h with
  | nil => exact h'
  | cons e h ih => exact .cons e (ih h')

theorem refine (h : Path left right a xs b) (subdivide : Edge → List Edge)
    (blind : Vertex → Vertex)
    (hsub : ∀ e, Path left right (blind (left e)) (subdivide e) (blind (right e))) :
    Path left right (blind a) (xs.flatMap subdivide) (blind b) := by
  induction h with
  | nil => exact .nil _
  | cons e h ih => exact (hsub e).append ih

theorem uniform (h : Path left right a xs b) (value : Vertex → Nat)
    (heq : ∀ e ∈ xs, value (left e) = value (right e)) :
    value b = value a ∧ ∀ e ∈ xs, value (left e) = value a := by
  induction h with
  | nil => simp
  | cons e h ih =>
    have hfirst := heq e (by simp)
    obtain ⟨hlast,hrest⟩ := ih (fun f hf ↦ heq f (by simp [hf]))
    refine ⟨hlast.trans hfirst.symm, ?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · rfl
    · exact (hrest f hf).trans hfirst.symm

/-- Carries at shared internal vertices cancel. This is an equality of
natural-number sums, so no hidden signed-error estimate is required. -/
theorem balance (h : Path left right a xs b)
    (carry : Vertex → Nat) (weight promised : Edge → Nat) (m : Nat)
    (heq : ∀ e ∈ xs, promised e + carry (left e) = m * weight e + carry (right e)) :
    (xs.map promised).sum + carry a = m * (xs.map weight).sum + carry b := by
  induction h with
  | nil => simp
  | cons e h ih =>
    have hfirst := heq e (by simp)
    have hrest := ih (fun f hf ↦ heq f (by simp [hf]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

end Path

namespace Path

/-- The vertices visited by a path, including its final endpoint. -/
def Visits (right : Edge → Vertex) (a : Vertex) (xs : List Edge) (v : Vertex) : Prop :=
  v = a ∨ ∃ e ∈ xs, v = right e

theorem visits_cons {left right : Edge → Vertex} {e : Edge} {xs : List Edge}
    {b v : Vertex} (h : Path left right (right e) xs b) :
    Visits right (left e) (e :: xs) v ↔
      v = left e ∨ Visits right (right e) xs v := by
  simp only [Visits, List.mem_cons]
  aesop

/-- A nondecreasing projection bounds the image of every visited vertex. -/
theorem projection_bounds {left right : Edge → Vertex} {a b v : Vertex}
    {xs : List Edge} (h : Path left right a xs b) (π : Vertex → Nat)
    (hm : ∀ e ∈ xs, π (left e) ≤ π (right e))
    (hv : Visits right a xs v) : π a ≤ π v ∧ π v ≤ π b := by
  induction h generalizing v with
  | nil a =>
    have : v = a := by simpa [Visits] using hv
    subst v
    exact ⟨le_rfl, le_rfl⟩
  | cons e h ih =>
    have he := hm e (by simp)
    have ht := fun f hf ↦ hm f (List.mem_cons_of_mem e hf)
    rcases (visits_cons h).mp hv with rfl | hv
    · have hb := (ih ht (Or.inl rfl)).2
      exact ⟨le_rfl, he.trans hb⟩
    · obtain ⟨hl, hr⟩ := ih ht hv
      exact ⟨he.trans hl, hr⟩

/-- Edge agreement on the collapsed edges of a nondecreasing projection
forces agreement on every fiber. The output type is arbitrary. -/
theorem fiber_uniform {Output : Type*} {left right : Edge → Vertex}
    {a b u v : Vertex} {xs : List Edge} (h : Path left right a xs b)
    (π : Vertex → Nat) (label : Vertex → Output)
    (hm : ∀ e ∈ xs, π (left e) ≤ π (right e))
    (heq : ∀ e ∈ xs, π (left e) = π (right e) → label (left e) = label (right e))
    (hu : Visits right a xs u) (hv : Visits right a xs v)
    (hp : π u = π v) : label u = label v := by
  induction h generalizing u v with
  | nil a =>
    have hu' : u = a := by simpa [Visits] using hu
    have hv' : v = a := by simpa [Visits] using hv
    rw [hu', hv']
  | cons e h ih =>
    have hm' := fun f hf ↦ hm f (List.mem_cons_of_mem e hf)
    have heq' := fun f hf ↦ heq f (List.mem_cons_of_mem e hf)
    rcases (visits_cons h).mp hu with rfl | hu
    · rcases (visits_cons h).mp hv with rfl | hv
      · rfl
      · have hb := h.projection_bounds π hm' hv
        have hc : π (left e) = π (right e) := by
          have := hm e (by simp)
          omega
        exact (heq e (by simp) hc).trans
          (ih hm' heq' (Or.inl rfl) hv (hc.symm.trans hp))
    · rcases (visits_cons h).mp hv with rfl | hv
      · have hb := h.projection_bounds π hm' hu
        have hc : π (left e) = π (right e) := by
          have := hm e (by simp)
          omega
        exact (ih hm' heq' hu (Or.inl rfl) (hp.trans hc)).trans
          (heq e (by simp) hc).symm
      · exact ih hm' heq' hu hv hp

/-- An integer-valued path with steps at most one visits every intermediate
integer. Combined with `fiber_uniform`, this gives a quotient onto an interval. -/
theorem intermediate {left right : Edge → Vertex} {a b : Vertex}
    {xs : List Edge} (h : Path left right a xs b) (π : Vertex → Nat)
    (hs : ∀ e ∈ xs, π (right e) ≤ π (left e) + 1)
    (k : Nat) (ha : π a ≤ k) (hb : k ≤ π b) :
    ∃ v, Visits right a xs v ∧ π v = k := by
  induction h with
  | nil a => exact ⟨a, Or.inl rfl, by omega⟩
  | cons e h ih =>
    by_cases he : π (left e) = k
    · exact ⟨left e, Or.inl rfl, he⟩
    · have hr : π (right e) ≤ k := by
        have := hs e (by simp)
        omega
      obtain ⟨v, hv, hp⟩ := ih (fun f hf ↦ hs f (List.mem_cons_of_mem e hf)) hr hb
      exact ⟨v, (visits_cons h).mpr (Or.inr hv), hp⟩

theorem visited_endpoint {left right : Edge → Vertex} {a b v : Vertex}
    {xs : List Edge} (h : Path left right a xs b) (hn : xs ≠ [])
    (hv : Visits right a xs v) : ∃ e ∈ xs, v = left e ∨ v = right e := by
  cases h with
  | nil => exact (hn rfl).elim
  | cons e h =>
    rcases hv with rfl | ⟨f, hf, rfl⟩
    · exact ⟨e, by simp, Or.inl rfl⟩
    · exact ⟨f, hf, Or.inr rfl⟩

end Path

theorem sum_bounds (xs : List Edge) (w : Edge → Nat)
    (h : ∀ e ∈ xs, 2 ≤ w e ∧ w e ≤ 4) :
    2 * xs.length ≤ (xs.map w).sum ∧ (xs.map w).sum ≤ 4 * xs.length := by
  induction xs with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun f hf ↦ h f (by simp [hf]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

end DistributedSynthesis.ScalingRow
