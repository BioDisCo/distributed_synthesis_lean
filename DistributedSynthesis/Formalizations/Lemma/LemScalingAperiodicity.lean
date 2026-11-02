/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Bounded ternary density excludes periodic binary scaling

These arithmetic results support SCALING-COUNTEREXAMPLE.md. They do not
assume or assert the still-to-be-formalized distributed row correspondence.
-/

namespace DistributedSynthesis.ScalingAperiodicity

def multiplier (width mass : Nat) : Nat := if 3 * width ≤ mass then 2 else 4

def mass : Nat → Nat
  | 0 => 3
  | n + 1 => multiplier (3 ^ n) (mass n) * mass n

theorem multiplier_cases (width mass : Nat) :
    multiplier width mass = 2 ∨ multiplier width mass = 4 := by
  unfold multiplier
  split <;> simp

theorem mass_bounds (n : Nat) : 2 * 3 ^ n ≤ mass n ∧ mass n ≤ 4 * 3 ^ n := by
  induction n with
  | zero => norm_num [mass]
  | succ n ih =>
    rw [mass, pow_succ]
    unfold multiplier
    split <;> omega

/-- A geometric progression bounded above and away from zero has ratio one. -/
theorem bounded_powers_eq_one (r lo hi : ℝ) (hr : 0 < r) (hlo : 0 < lo)
    (h : ∀ n : Nat, lo ≤ r ^ n ∧ r ^ n ≤ hi) : r = 1 := by
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · have hinv : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt lo⁻¹ hinv
    have hupper : (r⁻¹) ^ n ≤ lo⁻¹ := by
      rw [inv_pow]
      exact (inv_le_inv₀ (pow_pos hr n) hlo).mpr (h n).1
    exact False.elim (not_lt_of_ge hupper hn)
  · exact heq
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt hi hgt
    exact False.elim (not_lt_of_ge (h n).2 hn)

/-- Uniform row-density bounds force a repeating block's mass multiplier
to be exactly the corresponding power of three. -/
theorem block_multiplier_eq (W M : ℝ) (N p : Nat) (hW : 0 < W) (hM : 0 < M)
    (hbounds : ∀ k : Nat,
      2 * (3 : ℝ) ^ (N + k * p) ≤ M ^ k * W ∧
        M ^ k * W ≤ 4 * (3 : ℝ) ^ (N + k * p)) :
    M = (3 : ℝ) ^ p := by
  have hthree : 0 < (3 : ℝ) ^ N := by positivity
  have hp : 0 < (3 : ℝ) ^ p := by positivity
  have heq := bounded_powers_eq_one (M / 3 ^ p)
    (2 * 3 ^ N / W) (4 * 3 ^ N / W) (div_pos hM hp) (by positivity) ?_
  · exact (div_eq_one_iff_eq (ne_of_gt hp)).mp heq
  · intro k
    have hk : 0 < ((3 : ℝ) ^ p) ^ k := by positivity
    have h := hbounds k
    rw [pow_add, Nat.mul_comm k p, pow_mul] at h
    rw [div_pow]
    constructor
    · apply (div_le_div_iff₀ hW hk).mpr
      nlinarith [h.1]
    · apply (div_le_div_iff₀ hk hW).mpr
      nlinarith [h.2]

theorem two_pow_ne_three_pow (k p : Nat) (hp : 0 < p) :
    2 ^ k ≠ (3 : Nat) ^ p := by
  intro heq
  have hdiv : 3 ∣ (2 : Nat) ^ k := by
    rw [heq]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt hp)
  have : (3 : Nat) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdiv
  norm_num at this

/-- No positive-period block consisting of powers of two can repeat while
the number of edges grows by a factor of three per round. -/
theorem no_binary_block (W : ℝ) (N p k : Nat) (hp : 0 < p) (hW : 0 < W) :
    ¬ (∀ t : Nat,
      2 * (3 : ℝ) ^ (N + t * p) ≤ ((2 : ℝ) ^ k) ^ t * W ∧
        ((2 : ℝ) ^ k) ^ t * W ≤ 4 * (3 : ℝ) ^ (N + t * p)) := by
  intro hbounds
  have heq := block_multiplier_eq W (2 ^ k) N p hW (by positivity) hbounds
  have hnat : (2 : Nat) ^ k = 3 ^ p := by exact_mod_cast heq
  exact two_pow_ne_three_pow k p hp hnat

def blockProduct (m : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 1
  | p + 1 => m (start + p) * blockProduct m start p

theorem mass_add (W m : Nat → Nat) (hstep : ∀ n, W (n + 1) = m n * W n)
    (start p : Nat) : W (start + p) = blockProduct m start p * W start := by
  induction p with
  | zero => simp [blockProduct]
  | succ p ih => rw [Nat.add_succ, hstep, ih, blockProduct, Nat.mul_assoc]

theorem blockProduct_power_two (m : Nat → Nat) (hm : ∀ n, m n = 2 ∨ m n = 4)
    (start p : Nat) : ∃ k, blockProduct m start p = 2 ^ k := by
  induction p with
  | zero => exact ⟨0, rfl⟩
  | succ p ih =>
    obtain ⟨k, hk⟩ := ih
    rcases hm (start + p) with htwo | hfour
    · refine ⟨k + 1, ?_⟩
      rw [blockProduct, htwo, hk, pow_succ, Nat.mul_comm]
    · refine ⟨k + 2, ?_⟩
      rw [blockProduct, hfour, hk, pow_add]
      ring

/-- The forced row recurrence, not just the particular constructed source,
excludes every eventually periodic multiplier word. The offset allows the
first monitored row to be depth one rather than depth zero. -/
theorem no_eventually_periodic_scaling (W m : Nat → Nat) (offset : Nat)
    (hstep : ∀ n, W (n + 1) = m n * W n)
    (hm : ∀ n, m n = 2 ∨ m n = 4)
    (hbounds : ∀ n, 2 * 3 ^ (offset + n) ≤ W n ∧ W n ≤ 4 * 3 ^ (offset + n)) :
    ¬ (∃ N p, 0 < p ∧ ∀ n, N ≤ n → m (n + p) = m n) := by
  rintro ⟨N, p, hp, hrepeat⟩
  have hshift : ∀ t i, m (N + t * p + i) = m (N + i) := by
    intro t i
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show N + (t + 1) * p + i = (N + t * p + i) + p by ring,
        hrepeat _ (by omega), ih]
  have hprod : ∀ t k, blockProduct m (N + t * p) k = blockProduct m N k := by
    intro t k
    induction k with
    | zero => rfl
    | succ k ih => rw [blockProduct, blockProduct, hshift, ih]
  have hblocks : ∀ t, W (N + t * p) = (blockProduct m N p) ^ t * W N := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show N + (t + 1) * p = (N + t * p) + p by ring,
        mass_add W m hstep, hprod, ih, pow_succ]
      ring
  obtain ⟨k, hk⟩ := blockProduct_power_two m hm N p
  have hpositive : (0 : ℝ) < W N := by
    have := (hbounds N).1
    have : 0 < W N := lt_of_lt_of_le (by positivity) this
    exact_mod_cast this
  apply no_binary_block (W N) (offset + N) p k hp hpositive
  intro t
  have hb := hbounds (N + t * p)
  rw [hblocks, hk, ← Nat.add_assoc] at hb
  exact_mod_cast hb

/-- The basic carry is bounded independently of depth and coordinate. -/
theorem carry_bound (a b m : Nat) (hb : 0 < b) (hm : 0 < m) :
    m * a / b - m * (a / b) < m := by
  have hsplit : m * a / b = m * (a / b) + m * (a % b) / b := by
    have heq : m * a = m * (a % b) + (m * (a / b)) * b := by
      nlinarith [Nat.mod_add_div a b]
    rw [heq, Nat.add_mul_div_right _ _ hb]
    omega
  rw [hsplit, Nat.add_sub_cancel_left]
  exact (Nat.div_lt_iff_lt_mul hb).mpr (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt a hb) hm)

end DistributedSynthesis.ScalingAperiodicity
