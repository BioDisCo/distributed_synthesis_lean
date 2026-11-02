/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Topology.OpenHoles
import DistributedSynthesis.Library.Distributed.ViewPaths

/-! Reflected ternary coordinates of graph histories. The reflection is
essential: ordinary lexicographic ternary coding is not the view-path order.
The infinite coordinate is the supremum of finite left endpoints. -/

namespace Characterisation

open DistributedSynthesis Set

def graphDigit : Graph → Nat
  | .right => 0
  | .both => 1
  | .left => 2

def indexStep (j : Nat) (g : Graph) : Nat :=
  3 * j + if j % 2 = 0 then graphDigit g else 2 - graphDigit g

def pathIndex (h : List Graph) : Nat := h.foldl indexStep 0

@[simp] theorem pathIndex_nil : pathIndex [] = 0 := rfl

@[simp] theorem pathIndex_append (h : List Graph) (g : Graph) :
    pathIndex (h ++ [g]) = indexStep (pathIndex h) g := by
  simp [pathIndex, List.foldl_append]

theorem indexStep_bounds (j : Nat) (g : Graph) :
    3 * j ≤ indexStep j g ∧ indexStep j g < 3 * j + 3 := by
  unfold indexStep
  split <;> cases g <;> simp [graphDigit]

@[simp] theorem indexStep_div (j : Nat) (g : Graph) : indexStep j g / 3 = j := by
  have hb := indexStep_bounds j g
  omega

theorem indexStep_injective (j : Nat) : Function.Injective (indexStep j) := by
  intro g z eqIndex
  by_cases hp : j % 2 = 0 <;> cases g <;> cases z <;>
    simp_all [indexStep, graphDigit]

theorem indexStep_surjective_digit (j d : Nat) (hd : d < 3) :
    ∃ g, indexStep j g = 3 * j + d := by
  interval_cases d
  · by_cases hp : j % 2 = 0
    · exact ⟨Graph.right, by simp [indexStep, graphDigit, hp]⟩
    · exact ⟨Graph.left, by simp [indexStep, graphDigit, hp]⟩
  · exact ⟨Graph.both, by simp [indexStep, graphDigit]⟩
  · by_cases hp : j % 2 = 0
    · exact ⟨Graph.left, by simp [indexStep, graphDigit, hp]⟩
    · exact ⟨Graph.right, by simp [indexStep, graphDigit, hp]⟩

theorem pathIndex_injective (h k : List Graph)
    (sameLength : h.length = k.length) (sameIndex : pathIndex h = pathIndex k) : h = k := by
  induction h using List.reverseRecOn generalizing k with
  | nil =>
    have hk : k = [] := List.length_eq_zero_iff.mp sameLength.symm
    exact hk.symm
  | append_singleton h g ih =>
    induction k using List.reverseRecOn with
    | nil => simp at sameLength
    | append_singleton k z _ =>
      have parentLength : h.length = k.length := by simpa using sameLength
      have parentIndex : pathIndex h = pathIndex k := by
        have hi := congrArg (fun j => j / 3) sameIndex
        simpa only [pathIndex_append, indexStep_div] using hi
      have parentEq := ih k parentLength parentIndex
      subst k
      have graphEq : g = z := indexStep_injective (pathIndex h)
        (by simpa only [pathIndex_append] using sameIndex)
      rw [graphEq]

theorem pathIndex_surjective (n j : Nat) (hj : j < 3 ^ n) :
    ∃ h : List Graph, h.length = n ∧ pathIndex h = j := by
  induction n generalizing j with
  | zero =>
    have hj0 : j = 0 := by simpa using hj
    exact ⟨[], rfl, by simp [hj0]⟩
  | succ n ih =>
    have hq : j / 3 < 3 ^ n := by rw [pow_succ] at hj; omega
    obtain ⟨h, hlen, hindex⟩ := ih (j / 3) hq
    obtain ⟨g, hg⟩ := indexStep_surjective_digit (j / 3) (j % 3) (Nat.mod_lt j (by omega))
    refine ⟨h ++ [g], by simp [hlen], ?_⟩
    rw [pathIndex_append, hindex, hg]
    omega

theorem pathIndex_lt (h : List Graph) : pathIndex h < 3 ^ h.length := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h g ih =>
    rw [pathIndex_append]
    have hb := (indexStep_bounds (pathIndex h) g).2
    simp only [List.length_append, List.length_singleton, pow_succ]
    omega

/-- All k-round descendants lie in their parent's aligned block of 3^k
edge positions. -/
theorem pathIndex_refinement (h u : List Graph) :
    3 ^ u.length * pathIndex h ≤ pathIndex (h ++ u) ∧
      pathIndex (h ++ u) < 3 ^ u.length * (pathIndex h + 1) := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u g ih =>
    rw [← List.append_assoc, pathIndex_append]
    have bounds := indexStep_bounds (pathIndex (h ++ u)) g
    simp only [List.length_append, List.length_singleton, pow_succ]
    constructor <;> nlinarith

def graphPrefix (x : Nat → Graph) (n : Nat) : List Graph :=
  List.ofFn (fun i : Fin n => x i)

noncomputable def leftEndpoint (h : List Graph) : ℝ :=
  (pathIndex h : ℝ) / (3 : ℝ) ^ h.length

/-- The reflected digit order uses precisely the orientation in the existing
full-view path construction. -/
theorem orientation_agrees (h : List Graph) :
    (FullViewPath.evaluate h).oneLeft = decide (pathIndex h % 2 = 0) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g ih =>
    rw [FullViewPath.at_append, pathIndex_append]
    have parity : pathIndex h % 2 = 0 ∨ pathIndex h % 2 = 1 := by omega
    rcases parity with hp | hp <;> cases g <;>
      simp [FullViewPath.advance, ih, indexStep, graphDigit, hp,
        Nat.add_mod, Nat.mul_mod]

theorem leftEndpoint_append_mono (h : List Graph) (g : Graph) :
    leftEndpoint h ≤ leftEndpoint (h ++ [g]) := by
  have positive : (0 : ℝ) < 3 ^ h.length := by positivity
  have hb : (3 : ℝ) * pathIndex h ≤ indexStep (pathIndex h) g := by
    exact_mod_cast (indexStep_bounds (pathIndex h) g).1
  simp only [leftEndpoint, pathIndex_append, List.length_append,
    List.length_singleton, pow_succ]
  apply (div_le_div_iff₀ positive (by positivity)).mpr
  nlinarith

theorem leftEndpoint_bounds (h : List Graph) :
    0 ≤ leftEndpoint h ∧ leftEndpoint h ≤ 1 := by
  have positive : (0 : ℝ) < 3 ^ h.length := by positivity
  refine ⟨by unfold leftEndpoint; positivity, ?_⟩
  apply (div_le_one positive).mpr
  exact_mod_cast (Nat.le_of_lt (pathIndex_lt h))

noncomputable def coordinate (x : Nat → Graph) : ℝ :=
  sSup (Set.range (fun n => leftEndpoint (graphPrefix x n)))

theorem coordinate_bounds (x : Nat → Graph) :
    0 ≤ coordinate x ∧ coordinate x ≤ 1 := by
  have bounded : BddAbove (Set.range (fun n => leftEndpoint (graphPrefix x n))) :=
    ⟨1, by rintro y ⟨n, rfl⟩; exact (leftEndpoint_bounds _).2⟩
  constructor
  · have h := le_csSup bounded (Set.mem_range_self 0)
    have zero : leftEndpoint (graphPrefix x 0) = 0 := by
      simp [leftEndpoint, graphPrefix]
    change 0 ≤ sSup (Set.range (fun n => leftEndpoint (graphPrefix x n)))
    simpa only [zero] using h
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨n, rfl⟩
    exact (leftEndpoint_bounds _).2

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

noncomputable def geometricMap (x : Nat → Graph) : UnitInterval :=
  ⟨coordinate x, coordinate_bounds x⟩

def GeometricHoles (A : Set (Nat → Graph)) : Prop :=
  HasOpenHoles (geometricMap '' A)

theorem geometricHoles_iff (A : Set (Nat → Graph)) :
    GeometricHoles A ↔ interior (closure (geometricMap '' A)) = ∅ :=
  openHoles_iff_interior_closure_empty _

end Characterisation
