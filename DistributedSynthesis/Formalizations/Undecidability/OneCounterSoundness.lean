/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows
import DistributedSynthesis.Formalizations.Undecidability.SoundnessCorrespondence

namespace DistributedSynthesis.CounterMachine.OneCounter
open Characterisation
variable {Q : Type*} [DecidableEq Q] [Fintype Q]

/-- Reuse the checked row sum on the active counter of the embedding.
The second counter contributes no weight to this sum. -/
abbrev rowMass (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q)) (n : Nat) :=
  Rows.rowMass M (ResidueLTL.projectStrategy (mapStrategy embed embed σ)) n 0
abbrev rowControl (σ : StrategyPair Unit Unit (Output Q) (Output Q)) (n : Nat) :=
  Rows.rowControl (ResidueLTL.projectStrategy (mapStrategy embed embed σ)) n
abbrev rowZero (σ : StrategyPair Unit Unit (Output Q) (Output Q)) (n : Nat) :=
  Rows.rowZero (ResidueLTL.projectStrategy (mapStrategy embed embed σ)) n 0

theorem formula_logarithmic_run (M : Machine Q) (single : OnlyFirst M)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (realizes : ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M))
    (n : Nat) :
    rowControl σ n = (run M n).1 ∧ 0 < rowMass M σ n ∧
      -Real.logb 3 ((rowMass M σ n : ℝ) / 3^(n+1)) = ((run M n).2 : ℝ) := by
  have checks : ∀ env, Paper.Checks M (execution (mapStrategy embed embed σ) env) := by
    intro env
    rw [map_execution]
    exact Checks.embed M single _ ((satisfies_iff M _).mp (realizes env))
  obtain ⟨control,mass⟩ := Paper.checks_logarithmic_run M (mapStrategy embed embed σ) checks n
  rw [run_embed M single] at control mass
  exact ⟨control,(Paper.checks_row_masses M (mapStrategy embed embed σ) checks n 0).1,mass 0⟩

theorem formula_zero_exact (M : Machine Q) (single : OnlyFirst M)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (realizes : ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M))
    (n : Nat) : rowZero σ n = true ↔ (run M n).2 = 0 := by
  have checks : ∀ env, Paper.Checks M (execution (mapStrategy embed embed σ) env) := by
    intro env
    rw [map_execution]
    exact Checks.embed M single _ ((satisfies_iff M _).mp (realizes env))
  have zero := Paper.checks_zero_iff_logarithm_zero M (mapStrategy embed embed σ) checks n 0
  rw [(formula_logarithmic_run M single σ realizes n).2.2] at zero
  simpa only [Nat.cast_eq_zero] using zero

/-- The manuscript's existing right-plan strategy, projected to its
one-counter output tuple; no new strategy construction is substituted. -/
def sourceStrategy (M : Machine Q) : StrategyPair Unit Unit (Output Q) (Output Q) :=
  mapStrategy project project (ResidueLTL.liftStrategy (Source.strategy M))

theorem source_realizes (M : Machine Q) (single : OnlyFirst M) (nonhalting : Nonhalting M)
    (env : EnvironmentSequence Unit Unit) :
    LTL.Satisfies FiniteLetterLTL.interp (execution (sourceStrategy M) env) (formula M) := by
  apply (satisfies_iff M _).mpr
  unfold sourceStrategy
  rw [map_execution]
  exact Checks.project M single _ (Paper.source_checks M ((nonhalting_iff M single).mpr nonhalting) env)

end DistributedSynthesis.CounterMachine.OneCounter
