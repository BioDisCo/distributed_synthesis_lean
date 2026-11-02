/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemScalingAperiodicity
import DistributedSynthesis.Formalizations.Lemma.LemScalingSafetyObjective

/-! # Exact finite source labels and their conservation law -/

namespace DistributedSynthesis.ScalingSafety.Source
open ScalingAperiodicity

def width (n : Nat) : Nat := 3 ^ n
def mode (n : Nat) : Nat := multiplier (width n) (mass n)
def prefixMass (n j : Nat) : Nat := j * mass n / width n
def weight (n j : Nat) : Nat := prefixMass n (j+1) - prefixMass n j
def carry (n j : Nat) : Nat := mode n * (j * mass n) / width n - mode n * prefixMass n j

theorem width_pos (n : Nat) : 0 < width n := by exact pow_pos (by decide) n

theorem prefix_mono (n : Nat) {i j : Nat} (h : i ≤ j) : prefixMass n i ≤ prefixMass n j :=
  Nat.div_le_div_right (Nat.mul_le_mul_right (mass n) h)

theorem weight_bounds (n j : Nat) : 2 ≤ weight n j ∧ weight n j ≤ 4 := by
  have h := mass_bounds n
  have hlo := Nat.div_le_div_right (Nat.add_le_add_left h.1 (j * mass n))
    (c := width n)
  have hhi := Nat.div_le_div_right (Nat.add_le_add_left h.2 (j * mass n))
    (c := width n)
  change (j * mass n + 2 * width n) / width n ≤
    (j * mass n + mass n) / width n at hlo
  change (j * mass n + mass n) / width n ≤
    (j * mass n + 4 * width n) / width n at hhi
  rw [Nat.add_mul_div_right _ _ (width_pos n)] at hlo hhi
  unfold weight prefixMass
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem mode_cases (n : Nat) : mode n = 2 ∨ mode n = 4 := multiplier_cases _ _

theorem carry_split (n j : Nat) :
    mode n * (j * mass n) / width n = mode n * prefixMass n j + carry n j := by
  have heq : mode n * (j * mass n) =
      mode n * ((j * mass n) % width n) + (mode n * prefixMass n j) * width n := by
    have h := Nat.mod_add_div (j * mass n) (width n)
    dsimp only [prefixMass]
    nlinarith
  have hlo : mode n * prefixMass n j ≤ mode n * (j * mass n) / width n := by
    rw [heq, Nat.add_mul_div_right _ _ (width_pos n)]
    exact Nat.le_add_left _ _
  exact (Nat.add_sub_of_le hlo).symm

theorem carry_lt (n j : Nat) : carry n j < 4 := by
  have hm := mode_cases n
  have h := carry_bound (j * mass n) (width n) (mode n) (width_pos n) (by omega)
  change carry n j < mode n at h
  omega

theorem carry_left (n : Nat) : carry n 0 = 0 := by simp [carry, prefixMass]

theorem carry_right (n : Nat) : carry n (width n) = 0 := by
  unfold carry prefixMass
  rw [show mode n * (width n * mass n) = width n * (mode n * mass n) by ring]
  simp [Nat.ne_of_gt (width_pos n)]

theorem prefix_child (n j : Nat) :
    prefixMass (n+1) (3*j) = mode n * (j * mass n) / width n := by
  unfold prefixMass
  rw [show width (n+1) = 3 * width n by simp [width, pow_succ, Nat.mul_comm]]
  change (3*j) * (mode n * mass n) / (3 * width n) = _
  have heq : (3*j) * (mode n * mass n) = 3 * (mode n * (j * mass n)) := by ring
  rw [heq, Nat.mul_div_mul_left _ _ (by decide : 0 < 3)]

theorem conservation (n j : Nat) :
    weight (n+1) (3*j) + weight (n+1) (3*j+1) + weight (n+1) (3*j+2) + carry n j =
      mode n * weight n j + carry n (j+1) := by
  have h0 := prefix_mono (n+1) (show 3*j ≤ 3*j+1 by omega)
  have h1 := prefix_mono (n+1) (show 3*j+1 ≤ 3*j+2 by omega)
  have h2 := prefix_mono (n+1) (show 3*j+2 ≤ 3*j+3 by omega)
  have hp := prefix_mono n (show j ≤ j+1 by omega)
  have hc0 := carry_split n j
  have hc1 := carry_split n (j+1)
  have hpc0 := prefix_child n j
  have hpc1 := prefix_child n (j+1)
  rw [show 3*(j+1) = 3*j+3 by ring] at hpc1
  have htel : weight (n+1) (3*j) + weight (n+1) (3*j+1) + weight (n+1) (3*j+2) +
      prefixMass (n+1) (3*j) = prefixMass (n+1) (3*j+3) := by
    unfold weight
    simp only [show 3*j+1+1 = 3*j+2 by omega, show 3*j+2+1 = 3*j+3 by omega]
    omega
  have hmul : mode n * weight n j + mode n * prefixMass n j = mode n * prefixMass n (j+1) := by
    rw [← Nat.mul_add, weight, Nat.sub_add_cancel hp]
  omega

def edgePlan (n j : Nat) : Plan where
  weight := ⟨weight n j - 2, by have := weight_bounds n j; omega⟩
  child := fun d ↦ ⟨weight (n+1) (3*j+d.val) - 2,
    by have := weight_bounds (n+1) (3*j+d.val); omega⟩

theorem edgePlan_value (n j : Nat) : (edgePlan n j).value = weight n j := by
  have := weight_bounds n j
  simp only [Plan.value, edgePlan]
  omega

theorem edgePlan_child (n j : Nat) (d : Fin 3) :
    (edgePlan n j).childValue d = weight (n+1) (3*j+d.val) := by
  have := weight_bounds (n+1) (3*j+d.val)
  simp only [Plan.childValue, edgePlan]
  omega

/-- Outside-facing plans can be arbitrary. Using the same total formula
also outside the interval avoids a partial source definition. -/
def label (n j : Nat) : Label where
  up := decide (mode n = 4)
  carry := ⟨carry n j, carry_lt n j⟩
  left := edgePlan n (j-1)
  right := edgePlan n j

theorem label_mode (n j : Nat) : (label n j).multiplier = mode n := by
  rcases mode_cases n with h | h <;> simp [label, Label.multiplier, h]

theorem label_matching (n j : Nat) : (label n j).right = (label n (j+1)).left := by
  simp [label]

theorem label_conservation (n j : Nat) :
    (label n j).right.childValue 0 + (label n j).right.childValue 1 +
      (label n j).right.childValue 2 + (label n j).carry.val =
        (label n j).multiplier * (label n j).right.value + (label n (j+1)).carry.val := by
  rw [label_mode]
  change (edgePlan n j).childValue 0 + (edgePlan n j).childValue 1 +
    (edgePlan n j).childValue 2 + carry n j = mode n * (edgePlan n j).value + carry n (j+1)
  simpa only [edgePlan_child, edgePlan_value, Nat.add_zero] using conservation n j

end DistributedSynthesis.ScalingSafety.Source
