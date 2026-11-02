/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.RegularPrefixes

/-! A completed geometric/combinatorial iff: for omega-regular adversaries,
open holes at every scale are equivalent to uniformly bounded surviving
intervals in the finite reflected view-path order. This is not yet synthesis. -/

namespace Characterisation

open DistributedSynthesis

theorem descendant_index_surjective (h : List Graph) (n j : Nat) (hj : j < 3 ^ n) :
    ∃ u : List Graph, u.length = n ∧
      pathIndex (h ++ u) = 3 ^ n * pathIndex h + j := by
  induction n generalizing j with
  | zero =>
    have jzero : j = 0 := by simpa using hj
    exact ⟨[], rfl, by simp [jzero]⟩
  | succ n ih =>
    have jq : j / 3 < 3 ^ n := by rw [pow_succ] at hj; omega
    obtain ⟨u, ulen, uindex⟩ := ih (j / 3) jq
    obtain ⟨g, hg⟩ := indexStep_surjective_digit (pathIndex (h ++ u))
      (j % 3) (Nat.mod_lt j (by omega))
    refine ⟨u ++ [g], by simp [ulen], ?_⟩
    rw [← List.append_assoc, pathIndex_append, hg, uindex, pow_succ]
    have divmod := Nat.mod_add_div j 3
    nlinarith

def BoundedRowIntervals (P : List Graph → Prop) : Prop :=
  ∃ K, ∀ t a b, a ≤ b → b ≤ 3 ^ t →
    (∀ j, a ≤ j → j < b → LiveIndex P t j) → b - a < K

theorem bounded_rows_exclude_full_cones (P : List Graph → Prop)
    (bounded : BoundedRowIntervals P) : ¬ ∃ h, FullCone P h := by
  obtain ⟨K, bound⟩ := bounded
  rintro ⟨h, cone⟩
  have sizes : ∀ n : Nat, n ≤ 3 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have positive : 0 < 3 ^ n := by positivity
      omega
  have size := sizes K
  let B := 3 ^ K
  let a := B * pathIndex h
  let b := B * (pathIndex h + 1)
  have positive : 0 < B := by dsimp [B]; positivity
  have hab : a ≤ b := by dsimp [a, b]; nlinarith
  have bBound : b ≤ 3 ^ (h.length + K) := by
    rw [pow_add]
    have hp := pathIndex_lt h
    dsimp [b, B]
    nlinarith
  have allLive : ∀ j, a ≤ j → j < b → LiveIndex P (h.length + K) j := by
    intro j lo hi
    have digitBound : j - a < 3 ^ K := by
      dsimp [a, b, B] at *
      simp only [Nat.mul_add, Nat.mul_one] at hi
      omega
    obtain ⟨u, ulen, uindex⟩ := descendant_index_surjective h K (j - a) digitBound
    refine ⟨h ++ u, by simp [ulen], ?_, cone u⟩
    rw [uindex]
    change a + (j - a) = j
    omega
  have contradiction := bound (h.length + K) a b hab bBound allLive
  have width : b - a = B := by simp [a, b, Nat.mul_add]
  rw [width] at contradiction
  exact (Nat.not_lt_of_ge size) contradiction

theorem bounded_rows_imply_geometric_holes (A : Set (Nat → Graph))
    (bounded : BoundedRowIntervals (LivePrefix A)) : GeometricHoles A :=
  (geometric_holes_iff_no_full_cone A).mpr (bounded_rows_exclude_full_cones _ bounded)

/-- The holes/finite-row characterization, with the exact regularity and
geometry used in the synthesis conjecture. -/
theorem omegaRegular_holes_iff_bounded_rows (A : Set (Nat → Graph))
    (regular : OmegaRegular A) :
    GeometricHoles A ↔ BoundedRowIntervals (LivePrefix A) :=
  ⟨omegaRegular_geometric_holes_bound_rows A regular,
    bounded_rows_imply_geometric_holes A⟩

end Characterisation
