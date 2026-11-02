/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemScalingAperiodicity

/-!
# Exact counters in ternary row masses

These are the arithmetic soundness lemmas of the computation-encoding test.
They do not yet assert an end-to-end distributed undecidability theorem.
Binary row weights and a boundary test make the zero flags exact. Conservation
with multipliers 1, 3, and 9 then simulates increment, idle, and decrement.
-/

namespace DistributedSynthesis.TernaryCounter

def rowMass (xs : List (Fin 2)) : Nat := (xs.map Fin.val).sum

theorem rowMass_le_length (xs : List (Fin 2)) : rowMass xs ≤ xs.length := by
  induction xs with
  | nil => simp [rowMass]
  | cons x xs ih =>
    have hx := x.isLt
    simp only [rowMass,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem rowMass_all_one (xs : List (Fin 2)) (h : ∀ x ∈ xs, x.val = 1) :
    rowMass xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy ↦ h y (by simp [hy]))
    simp only [rowMass,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

/-- A zero claim is checked throughout the row. A nonzero claim is checked
at its leftmost edge, not against an unobservable global sum. -/
def Guard (z : Bool) (xs : List (Fin 2)) : Prop :=
  (z = true → ∀ x ∈ xs, x.val = 1) ∧
  (z = false → ∃ tail, xs = (0 : Fin 2) :: tail)

theorem guard_exact {z : Bool} {xs : List (Fin 2)} (h : Guard z xs) :
    z = true ↔ rowMass xs = xs.length := by
  constructor
  · exact fun hz ↦ rowMass_all_one xs (h.1 hz)
  · intro hm
    cases hz : z
    · obtain ⟨tail,rfl⟩ := h.2 hz
      have ht := rowMass_le_length tail
      simp only [rowMass,List.map_cons,List.sum_cons,List.length_cons,Fin.val_zero,
        Nat.zero_add] at hm ht
      omega
    · rfl

theorem encoded_zero (W c n : Nat) (h : W * 3 ^ c = 3 ^ n) :
    W = 3 ^ n ↔ c = 0 := by
  constructor
  · intro hW
    rw [hW] at h
    cases c with
    | zero => rfl
    | succ c =>
      rw [pow_succ] at h
      have hn : 0 < 3 ^ n := pow_pos (by decide) n
      have hc : 0 < 3 ^ c := pow_pos (by decide) c
      nlinarith
  · intro hc
    simpa [hc] using h

inductive Operation where
  | increment | idle | decrement
deriving DecidableEq

def Operation.factor : Operation → Nat
  | .increment => 1
  | .idle => 3
  | .decrement => 9

def Operation.applyCount : Operation → Nat → Nat
  | .increment,c => c+1
  | .idle,c => c
  | .decrement,c => c-1

theorem encoded_step (op : Operation) (W c n : Nat)
    (h : W * 3 ^ c = 3 ^ n) (hd : op = .decrement → 0 < c) :
    (op.factor * W) * 3 ^ (op.applyCount c) = 3 ^ (n+1) := by
  cases op with
  | increment =>
    simp only [Operation.factor,Operation.applyCount,Nat.one_mul,pow_succ]
    nlinarith [h]
  | idle =>
    simp only [Operation.factor,Operation.applyCount,pow_succ]
    nlinarith [h]
  | decrement =>
    obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hd rfl))
    simp only [Operation.factor,Operation.applyCount,Nat.succ_sub_one,pow_succ] at *
    nlinarith [h]

def count (ops : Nat → Operation) : Nat → Nat
  | 0 => 0
  | n+1 => (ops n).applyCount (count ops n)

/-- Every certified sequence has the exact integer counter semantics.
In particular, no alternative fractional interpretation or false zero branch
can satisfy these hypotheses. Here index n denotes physical depth n+1. -/
theorem forced_counts (W : Nat → Nat) (z : Nat → Bool) (ops : Nat → Operation)
    (hinit : W 0 = 3)
    (hguard : ∀ n, z n = true ↔ W n = 3 ^ (n+1))
    (hdec : ∀ n, ops n = .decrement → z n = false)
    (hstep : ∀ n, W (n+1) = (ops n).factor * W n) :
    ∀ n, W n * 3 ^ (count ops n) = 3 ^ (n+1) ∧
      (z n = true ↔ count ops n = 0) := by
  intro n
  induction n with
  | zero =>
    have hi : W 0 * 3 ^ (count ops 0) = 3 ^ (0+1) := by simp [count,hinit]
    exact ⟨hi,(hguard 0).trans (encoded_zero _ _ _ hi)⟩
  | succ n ih =>
    have hd : ops n = .decrement → 0 < count ops n := by
      intro hop
      have hz := hdec n hop
      have hc : count ops n ≠ 0 := by
        intro hc
        have := ih.2.mpr hc
        simp [hz] at this
      omega
    have hi : W (n+1) * 3 ^ (count ops (n+1)) = 3 ^ (n+1+1) := by
      rw [hstep,count]
      exact encoded_step _ _ _ _ ih.1 hd
    exact ⟨hi,(hguard (n+1)).trans (encoded_zero _ _ _ hi)⟩

theorem count_le_time (ops : Nat → Operation) (n : Nat) : count ops n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases h : ops n <;> simp only [count,h,Operation.applyCount] <;> omega

/-- The realizing row has density 1/(3^c). Its first bit distinguishes
zero from every positive counter, however large. -/
def weight (c j : Nat) : Nat := (j+1) / 3 ^ c - j / 3 ^ c

theorem weight_bound (c j : Nat) : weight c j ≤ 1 := by
  have hd : 0 < 3 ^ c := pow_pos (by decide) c
  have h := Nat.div_le_div_right (show j+1 ≤ j+3^c by omega) (c := 3^c)
  rw [Nat.add_div_right _ hd] at h
  unfold weight
  omega

theorem weight_zero_counter (j : Nat) : weight 0 j = 1 := by simp [weight]

theorem weight_left_positive (c : Nat) (h : 0 < c) : weight c 0 = 0 := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  have hp : 0 < 3 ^ c := pow_pos (by decide) c
  unfold weight
  simp only [Nat.zero_add,Nat.zero_div,Nat.sub_zero,pow_succ]
  exact Nat.div_eq_of_lt (by nlinarith)

def carry (c m j : Nat) : Nat := (m*j) / 3^c - m * (j / 3^c)

theorem carry_bound (c m j : Nat) (hm : 0 < m) (hmax : m ≤ 9) :
    carry c m j < 9 := by
  have h := ScalingAperiodicity.carry_bound j (3^c) m (pow_pos (by decide) c) hm
  change carry c m j < m at h
  omega

theorem carry_split (c m j : Nat) :
    (m*j) / 3^c = m * (j / 3^c) + carry c m j := by
  have hd : 0 < 3^c := pow_pos (by decide) c
  have heq : m*j = m*(j % 3^c) + (m*(j/3^c))*3^c := by
    have h := Nat.mod_add_div j (3^c)
    nlinarith
  have hlo : m*(j/3^c) ≤ (m*j)/3^c := by
    rw [heq,Nat.add_mul_div_right _ _ hd]
    exact Nat.le_add_left _ _
  exact (Nat.add_sub_of_le hlo).symm

theorem prefix_child (op : Operation) (c j : Nat)
    (hd : op = .decrement → 0 < c) :
    (3*j) / 3^(op.applyCount c) = (op.factor*j) / 3^c := by
  cases op with
  | increment =>
    simp only [Operation.applyCount,Operation.factor,Nat.one_mul,pow_succ]
    rw [Nat.mul_comm (3^c) 3,Nat.mul_div_mul_left _ _ (by decide : 0 < 3)]
  | idle => rfl
  | decrement =>
    obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hd rfl))
    simp only [Operation.applyCount,Operation.factor,Nat.succ_sub_one,pow_succ]
    rw [show 9*j = 3*(3*j) by omega,Nat.mul_comm (3^c) 3,
      Nat.mul_div_mul_left _ _ (by decide : 0 < 3)]

/-- The explicit finite source carries realize every valid counter
operation on all three children, at every coordinate. -/
theorem conservation (op : Operation) (c j : Nat)
    (hd : op = .decrement → 0 < c) :
    weight (op.applyCount c) (3*j) + weight (op.applyCount c) (3*j+1) +
      weight (op.applyCount c) (3*j+2) + carry c op.factor j =
        op.factor * weight c j + carry c op.factor (j+1) := by
  let D := 3^(op.applyCount c)
  have h0 := Nat.div_le_div_right (show 3*j ≤ 3*j+1 by omega) (c := D)
  have h1 := Nat.div_le_div_right (show 3*j+1 ≤ 3*j+2 by omega) (c := D)
  have h2 := Nat.div_le_div_right (show 3*j+2 ≤ 3*j+3 by omega) (c := D)
  have hp := Nat.div_le_div_right (show j ≤ j+1 by omega) (c := 3^c)
  have hc0 := carry_split c op.factor j
  have hc1 := carry_split c op.factor (j+1)
  have hpc0 := prefix_child op c j hd
  have hpc1 := prefix_child op c (j+1) hd
  rw [show 3*(j+1) = 3*j+3 by omega] at hpc1
  have htel : weight (op.applyCount c) (3*j) + weight (op.applyCount c) (3*j+1) +
      weight (op.applyCount c) (3*j+2) + (3*j)/D = (3*j+3)/D := by
    unfold weight
    change (3*j+1)/D-(3*j)/D + ((3*j+2)/D-(3*j+1)/D) +
      ((3*j+3)/D-(3*j+2)/D) + (3*j)/D = (3*j+3)/D
    omega
  have hmul : op.factor * weight c j + op.factor*(j/3^c) = op.factor*((j+1)/3^c) := by
    rw [← Nat.mul_add,weight,Nat.sub_add_cancel hp]
  change (3*j)/D = _ at hpc0
  change (3*j+3)/D = _ at hpc1
  omega

theorem carry_at_multiple (c m k : Nat) : carry c m (3^c*k) = 0 := by
  unfold carry
  rw [show m*(3^c*k) = 3^c*(m*k) by ring]
  simp

theorem sum_weights (c L : Nat) :
    ((List.range L).map (weight c)).sum = L / 3^c := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hm := Nat.div_le_div_right (show L ≤ L+1 by omega) (c := 3^c)
    rw [List.range_succ,List.map_append,List.sum_append,ih]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,weight]
    omega

end DistributedSynthesis.TernaryCounter
