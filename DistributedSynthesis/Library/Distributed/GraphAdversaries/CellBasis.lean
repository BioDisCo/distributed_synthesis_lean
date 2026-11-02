/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Cells
import Mathlib.Topology.Order.DenselyOrdered

/-! Arbitrarily fine closed subdivision cells inside every relatively open
set of the unit interval. This avoids assuming injectivity at endpoints. -/

namespace Characterisation

open DistributedSynthesis Set

private theorem le_three_pow (n : Nat) : n ≤ 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have positive : 0 < 3 ^ n := by positivity
    omega

theorem exists_cell_between (a b : ℝ) (nonneg : 0 ≤ a) (atMostOne : b ≤ 1)
    (strict : a < b) (minDepth : Nat) :
    ∃ h : List Graph, minDepth ≤ h.length ∧
      a < leftEndpoint h ∧ rightEndpoint h < b := by
  obtain ⟨r, hr⟩ := exists_nat_gt (3 / (b - a))
  let n := r + minDepth
  have positive : (0 : ℝ) < 3 ^ n := by positivity
  have castBound : (r : ℝ) ≤ (3 : ℝ) ^ n := by
    exact_mod_cast (show r ≤ 3 ^ n from (Nat.le_add_right r minDepth).trans (le_three_pow n))
  have wide : 3 < (3 : ℝ) ^ n * (b - a) :=
    (div_lt_iff₀ (by linarith : 0 < b - a)).mp (hr.trans_le castBound)
  let j : Nat := Nat.floor (a * (3 : ℝ) ^ n) + 1
  have low : a * (3 : ℝ) ^ n < (j : ℝ) := by
    simpa [j] using Nat.lt_floor_add_one (a * (3 : ℝ) ^ n)
  have high : (j : ℝ) + 1 < b * (3 : ℝ) ^ n := by
    have floorBound := Nat.floor_le (mul_nonneg nonneg positive.le)
    dsimp [j]
    push_cast
    nlinarith
  have indexBound : j < 3 ^ n := by
    have : (j : ℝ) < (3 : ℝ) ^ n := by nlinarith
    exact_mod_cast this
  obtain ⟨h, hlen, hindex⟩ := pathIndex_surjective n j indexBound
  refine ⟨h, by omega, ?_, ?_⟩
  · simp only [leftEndpoint, hlen, hindex]
    exact (lt_div_iff₀ positive).mpr low
  · simp only [rightEndpoint, hlen, hindex]
    exact (div_lt_iff₀ positive).mpr high

/-- A relatively open nonempty set contains an ordinary real interval
strictly inside [0,1]. -/
theorem relative_open_contains_interval (U : Set UnitInterval)
    (openU : IsOpen U) (nonemptyU : U.Nonempty) :
    ∃ a b : ℝ, 0 ≤ a ∧ b ≤ 1 ∧ a < b ∧
      ∀ z : UnitInterval, z.val ∈ Ioo a b → z ∈ U := by
  obtain ⟨V, openV, preimage⟩ := isOpen_induced_iff.mp openU
  obtain ⟨z, hz⟩ := nonemptyU
  have zV : z.val ∈ V := by rw [← preimage] at hz; exact hz
  have zClosure : z.val ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact z.property
  obtain ⟨p, pV, pInterior⟩ := mem_closure_iff.mp zClosure V openV zV
  have openInner : IsOpen (V ∩ Ioo (0 : ℝ) 1) := openV.inter isOpen_Ioo
  obtain ⟨a, b, hab, sub⟩ := openInner.exists_Ioo_subset ⟨p, pV, pInterior⟩
  have aNonneg : 0 ≤ a := by
    by_contra ha
    have alt : a < min b 0 := lt_min hab (by linarith)
    obtain ⟨c, ac, cb⟩ := exists_between alt
    have hc := (sub ⟨ac, cb.trans_le (min_le_left _ _)⟩).2.1
    have := cb.trans_le (min_le_right b 0)
    linarith
  have bLe : b ≤ 1 := by
    by_contra hb
    have alt : max a 1 < b := max_lt hab (by linarith)
    obtain ⟨c, ac, cb⟩ := exists_between alt
    have hc := (sub ⟨(le_max_left a 1).trans_lt ac, cb⟩).2.2
    have := (le_max_right a 1).trans_lt ac
    linarith
  refine ⟨a, b, aNonneg, bLe, hab, fun z hz => ?_⟩
  rw [← preimage]
  exact (sub hz).1

theorem exists_closed_cell_in_open (U : Set UnitInterval)
    (openU : IsOpen U) (nonemptyU : U.Nonempty) (minDepth : Nat) :
    ∃ h : List Graph, minDepth ≤ h.length ∧
      ∀ z : UnitInterval,
        z.val ∈ Icc (leftEndpoint h) (rightEndpoint h) → z ∈ U := by
  obtain ⟨a, b, ha, hb, hab, sub⟩ := relative_open_contains_interval U openU nonemptyU
  obtain ⟨h, hdepth, hleft, hright⟩ := exists_cell_between a b ha hb hab minDepth
  exact ⟨h, hdepth, fun z hz => sub z ⟨hleft.trans_le hz.1, hz.2.trans_lt hright⟩⟩

end Characterisation
