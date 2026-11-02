/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Undecidability.CounterArithmetic
import DistributedSynthesis.Formalizations.Undecidability.FormulaCorrespondence

/-! The logarithmic soundness argument applied to the actual rows of an
arbitrary realizing strategy. All row hypotheses are derived from the paper's
formula checks. The sum is over edges, excluding the unused rightmost plan.
Physical round `n+1` represents machine step `n`. -/
namespace DistributedSynthesis.CounterMachine.Paper
open ResidueLTL
variable {Q : Type*} [DecidableEq Q] [Fintype Q]
variable (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q))

/-- Forgetting the position residue gives a winning monitor strategy; it
does not introduce a separate certificate or restrict the given strategy. -/
theorem checks_project_winning
    (checks : ∀ env, Checks M (execution σ env)) : Rows.Winning M (projectStrategy σ) := by
  intro env
  rw [project_execution]
  exact ((conditions_iff_accepts M _).mp ((conditions_iff_checks M _).mpr (checks env))).2

/-- Positivity, zero detection, and the mass recurrence used in the English
soundness proof, now derived from the actual strategy's formula checks. -/
theorem checks_row_masses
    (checks : ∀ env, Checks M (execution σ env)) (n : Nat) (k : Fin 2) :
    0 < Rows.rowMass M (projectStrategy σ) n k ∧
      (Rows.rowZero (projectStrategy σ) n k = true ↔
        Rows.rowMass M (projectStrategy σ) n k = 3 ^ (n+1)) ∧
      Rows.rowMass M (projectStrategy σ) (n+1) k =
        (M.op (Rows.rowControl (projectStrategy σ) n)
          (Rows.rowZero (projectStrategy σ) n) k).factor *
          Rows.rowMass M (projectStrategy σ) n k := by
  have winning := checks_project_winning M σ checks
  have positive (r : Nat) : 0 < Rows.rowMass M (projectStrategy σ) r k := by
    induction r with
    | zero => rw [Rows.row_initial_mass M (projectStrategy σ) winning k]; decide
    | succ r ih =>
      rw [Rows.row_recurrence M (projectStrategy σ) winning r k]
      apply Nat.mul_pos _ ih
      cases M.op (Rows.rowControl (projectStrategy σ) r)
        (Rows.rowZero (projectStrategy σ) r) k <;> decide
  exact ⟨positive n,
    Rows.row_zero_exact M (projectStrategy σ) winning n k,
    Rows.row_recurrence M (projectStrategy σ) winning n k⟩

/-- The displayed logarithmic transition in the English proof, using only
the derived positive row masses and carry-cancellation recurrence. -/
theorem checks_logarithmic_transition
    (checks : ∀ env, Checks M (execution σ env)) (n : Nat) (k : Fin 2) :
    -Real.logb 3 ((Rows.rowMass M (projectStrategy σ) (n+1) k : ℝ) / 3 ^ (n+2)) =
      -Real.logb 3 ((Rows.rowMass M (projectStrategy σ) n k : ℝ) / 3 ^ (n+1)) +
        (1 - Real.logb 3 ((M.op (Rows.rowControl (projectStrategy σ) n)
          (Rows.rowZero (projectStrategy σ) n) k).factor : ℝ)) := by
  obtain ⟨positive,_,recurrence⟩ := checks_row_masses M σ checks n k
  rw [recurrence,Nat.cast_mul]
  apply TernaryCounter.logarithmic_mass_step
  · exact_mod_cast positive
  · cases M.op (Rows.rowControl (projectStrategy σ) n)
      (Rows.rowZero (projectStrategy σ) n) k <;> norm_num [TernaryCounter.Operation.factor]

/-- The control and logarithm decoded from the realizing strategy are the
machine's actual configuration. Integrality is a conclusion, not a premise. -/
theorem checks_logarithmic_run
    (checks : ∀ env, Checks M (execution σ env)) (n : Nat) :
    Rows.rowControl (projectStrategy σ) n = (M.run n).1 ∧
      ∀ k : Fin 2,
        -Real.logb 3 ((Rows.rowMass M (projectStrategy σ) n k : ℝ) / 3 ^ (n+1)) =
          ((M.run n).2 k : ℝ) := by
  have winning := checks_project_winning M σ checks
  have run_eq := Rows.extracted_eq_run M (projectStrategy σ) winning n
  refine ⟨congrArg Prod.fst run_eq,?_⟩
  intro k
  have encoded := (Rows.forced_counters M (projectStrategy σ) winning n k).1
  rw [TernaryCounter.encoded_log_counter _ _ _ encoded]
  exact congrArg (fun config : Q × (Fin 2 → Nat) => (config.2 k : ℝ)) run_eq

/-- The zero indicator is precisely the zero test of the logarithmic value. -/
theorem checks_zero_iff_logarithm_zero
    (checks : ∀ env, Checks M (execution σ env)) (n : Nat) (k : Fin 2) :
    Rows.rowZero (projectStrategy σ) n k = true ↔
      -Real.logb 3 ((Rows.rowMass M (projectStrategy σ) n k : ℝ) / 3 ^ (n+1)) = 0 := by
  have winning := checks_project_winning M σ checks
  obtain ⟨encoded,zero⟩ := Rows.forced_counters M (projectStrategy σ) winning n k
  rw [TernaryCounter.encoded_log_counter _ _ _ encoded]
  simpa only [Nat.cast_eq_zero] using zero

/-- The same decoding result with realization of the literal compiled LTL
formula as the only behavioral assumption. There is no assumed mass invariant,
zero-test certificate, or natural-number decoding hypothesis. -/
theorem formula_logarithmic_run
    (realizes : ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M))
    (n : Nat) :
    Rows.rowControl (projectStrategy σ) n = (M.run n).1 ∧
      ∀ k : Fin 2, 0 < Rows.rowMass M (projectStrategy σ) n k ∧
        -Real.logb 3 ((Rows.rowMass M (projectStrategy σ) n k : ℝ) / 3 ^ (n+1)) =
          ((M.run n).2 k : ℝ) := by
  have checks (env) : Checks M (execution σ env) :=
    (conditions_iff_checks M _).mp ((satisfies_iff M _).mp (realizes env))
  obtain ⟨control,counters⟩ := checks_logarithmic_run M σ checks n
  exact ⟨control,fun k => ⟨(checks_row_masses M σ checks n k).1,counters k⟩⟩

end DistributedSynthesis.CounterMachine.Paper
