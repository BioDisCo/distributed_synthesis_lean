/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineMonitor
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Arithmetic correspondence with the soundness and completeness proofs in
the manuscript. Physical round `n+1` encodes machine step `n`. -/
namespace DistributedSynthesis.TernaryCounter

/-- Taking logarithms of the normalized mass recurrence. This identity
requires positivity, but no integrality assumption on the decoded value. -/
theorem logarithmic_mass_step (W m : ℝ) (r : Nat) (hW : 0 < W) (hm : 0 < m) :
    -Real.logb 3 ((m * W) / 3 ^ (r+1)) =
      -Real.logb 3 (W / 3 ^ r) + (1 - Real.logb 3 m) := by
  rw [Real.logb_div (ne_of_gt (mul_pos hm hW)) (by positivity),
    Real.logb_div (ne_of_gt hW) (by positivity),
    Real.logb_mul (ne_of_gt hm) (ne_of_gt hW),
    Real.logb_pow,Real.logb_pow]
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]
  ring


/-- The three multiplier cases in the manuscript: increment, no change,
and a permitted decrement change the decoded counter by 1, 0, and -1. -/
theorem operation_logarithmic_change (op : Operation) :
    1 - Real.logb 3 (op.factor : ℝ) =
      match op with
      | .increment => (1 : ℝ)
      | .idle => 0
      | .decrement => -1 := by
  cases op with
  | increment => norm_num [Operation.factor]
  | idle => norm_num [Operation.factor,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]
  | decrement =>
    change 1 - Real.logb 3 (9 : ℝ) = -1
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num,Real.logb_pow]
    norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]


/-- The integer invariant makes the manuscript's real logarithm meaningful
and identifies it with the natural counter, without assuming integrality. -/
theorem encoded_density (W c r : Nat) (h : W * 3 ^ c = 3 ^ r) :
    (W : ℝ) / 3 ^ r = (3 ^ c : ℝ)⁻¹ := by
  have hreal : (W : ℝ) * 3 ^ c = 3 ^ r := by exact_mod_cast h
  apply (div_eq_iff (by positivity : (3 : ℝ)^r ≠ 0)).mpr
  rw [← hreal]
  field_simp

theorem encoded_log_counter (W c r : Nat) (h : W * 3 ^ c = 3 ^ r) :
    -Real.logb 3 ((W : ℝ) / 3 ^ r) = (c : ℝ) := by
  rw [encoded_density W c r h, Real.logb_inv, Real.logb_pow]
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]

/-- Reuses the existing induction on operations, and derives positivity,
exact logarithmic decoding, and zero detection for every round. The premises
are the aggregate consequences of C1--C5, not an end-to-end strategy theorem. -/
theorem forced_log_counters (W : Nat → Nat) (z : Nat → Bool) (ops : Nat → Operation)
    (hinit : W 0 = 3)
    (hguard : ∀ n, z n = true ↔ W n = 3 ^ (n+1))
    (hdec : ∀ n, ops n = .decrement → z n = false)
    (hstep : ∀ n, W (n+1) = (ops n).factor * W n) (n : Nat) :
    0 < W n ∧ -Real.logb 3 ((W n : ℝ) / 3 ^ (n+1)) = (count ops n : ℝ) ∧
      (z n = true ↔ count ops n = 0) := by
  obtain ⟨encoded,zero⟩ := forced_counts W z ops hinit hguard hdec hstep n
  refine ⟨?_, encoded_log_counter _ _ _ encoded, zero⟩
  have positive : 0 < W n * 3 ^ count ops n := by rw [encoded]; positivity
  exact pos_of_mul_pos_left positive (Nat.zero_le _)

/-- The manuscript's displayed inclusive sum counts the rightmost vertex's
unused right-edge output. At counter zero it has one extra unit of mass. -/
theorem inclusive_zero_mass (r : Nat) :
    ((List.range (3 ^ r + 1)).map (weight 0)).sum = 3 ^ r + 1 := by
  simpa using sum_weights 0 (3 ^ r + 1)

theorem edge_zero_mass (r : Nat) :
    ((List.range (3 ^ r)).map (weight 0)).sum = 3 ^ r := by
  simpa using sum_weights 0 (3 ^ r)

/-- A concrete counterexample to the inclusive endpoint in the printed
soundness proof, using exactly the printed completeness algorithm's weights. -/
example : ((List.range (3 ^ 1 + 1)).map (weight 0)).sum = 4 ∧
    ((List.range (3 ^ 1)).map (weight 0)).sum = 3 := by decide

end DistributedSynthesis.TernaryCounter

namespace DistributedSynthesis.CounterMachine
open TernaryCounter

/-- Arithmetic part of the two-counter soundness proof, after deriving the
row equations from C1--C5. No left-plan output or agreement is assumed.
This helper still requires those row equations; the current paper's strategy
to row correspondence is a separate obligation. -/
theorem nonhalting_of_row_masses {Q : Type*} (M : Machine Q)
    (q : Nat → Q) (z : Nat → Fin 2 → Bool) (W : Nat → Fin 2 → Nat)
    (initialControl : q 0 = M.initial)
    (initialMass : ∀ k, W 0 k = 3)
    (guard : ∀ n k, z n k = true ↔ W n k = 3 ^ (n+1))
    (nextControl : ∀ n, q (n+1) = M.next (q n) (z n))
    (nextMass : ∀ n k, W (n+1) k = (M.op (q n) (z n) k).factor * W n k)
    (live : ∀ n, M.code (q n) ≠ none) : M.Nonhalting := by
  let ops : Fin 2 → Nat → Operation := fun k n => M.op (q n) (z n) k
  let counters : Nat → Fin 2 → Nat := fun n k => count (ops k) n
  have invariant (n : Nat) (k : Fin 2) :
      W n k * 3 ^ (counters n k) = 3 ^ (n+1) ∧
        (z n k = true ↔ counters n k = 0) :=
    forced_counts (fun n => W n k) (fun n => z n k) (ops k) (initialMass k)
      (fun n => guard n k) (fun n hop => M.op_decrement _ _ k hop)
      (fun n => nextMass n k) n
  have zeroFlags (n : Nat) : flags (counters n) = z n := by
    funext k
    have hz := (invariant n k).2
    cases h : z n k <;> simp_all [flags]
  have run_eq (n : Nat) : (q n,counters n) = M.run n := by
    induction n with
    | zero => exact Prod.ext initialControl rfl
    | succ n ih =>
      rw [Machine.run,← ih]
      apply Prod.ext
      · simpa only [Machine.advance,zeroFlags n] using nextControl n
      · funext k
        change (ops k n).applyCount (counters n k) = _
        simp only [Machine.advance,zeroFlags n,ops]
  intro n
  rw [← run_eq n]
  exact live n

end DistributedSynthesis.CounterMachine
