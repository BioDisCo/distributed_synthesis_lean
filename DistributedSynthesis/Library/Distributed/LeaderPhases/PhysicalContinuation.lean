/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointPhaseObjective

/-! Discharge residual winning from one actual globally winning strategy.
All roots retain that same strategy and its exact full-history monitor state;
no separate winning continuation is selected for a target slot. -/
namespace Characterisation
open DistributedSynthesis

def recordContinuationLetter {I₁ I₂ O₁ O₂ : Type}
    (r : RoundRecord I₁ I₂ Graph O₁ O₂) : ContinuationLetter I₁ I₂ O₁ O₂ :=
  ((r.inputOne, r.inputTwo, r.graph), (r.outputOne, r.outputTwo))

theorem emptyContinuation_trace_execution {I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂) :
    continuationTrace (strategyContinuationPolicy σ (fun _ : Unit => [])) ()
      (fun n => EnvironmentRound.toProd (env n)) =
      fun n => recordContinuationLetter (execution σ env n) := by
  let history n := closingLayerHistory (fun _ : Unit => []) n
    (continuationScenario () (fun i => EnvironmentRound.toProd (env i)) n)
  have views : ∀ n, viewPair (executionPrefix σ env n) = viewPair (history n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [executionPrefix_succ, viewPair_append]
      change advanceViews _ _ = viewPair (History.append (history n)
        ⟨(env n).inputOne, (env n).inputTwo, (env n).graph, (), ()⟩)
      rw [viewPair_append, ih]
      cases g : (env n).graph <;> simp only [advanceViews, nextRound, g]
  funext n
  have one := congrArg Prod.fst (views (n+1))
  have two := congrArg Prod.snd (views (n+1))
  change currentView .one (executionPrefix σ env (n+1)) = currentView .one (history (n+1)) at one
  change currentView .two (executionPrefix σ env (n+1)) = currentView .two (history (n+1)) at two
  rw [currentView_executionPrefix_succ] at one two
  rw [execution_apply]
  exact Prod.ext rfl (Prod.ext (congrArg σ.one one.symm) (congrArg σ.two two.symm))

theorem rootContinuation_wins_of_execution {I₁ I₂ O₁ O₂ : Type}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n))) :
    ContinuationWins objective.AcceptsFrom (fun _ : Unit => objective.initial)
      (strategyContinuationPolicy σ (fun _ : Unit => [])) := by
  intro h inputs
  cases h
  have actual := winning (fun n => EnvironmentRound.ofProd (inputs n))
  rw [← emptyContinuation_trace_execution] at actual
  exact actual

theorem continuationLabels_original {H I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    continuationLabels step initial (strategyContinuationPolicy σ past) n s =
      strategyHistoryLabel σ step q₀ (closingLayerHistory past n s) := by
  induction n with
  | zero => exact source s
  | succ n ih =>
    simp only [continuationLabels]
    rw [ih]
    exact (strategyHistoryLabel_append σ step q₀ (closingLayerHistory past n s.1)
      ⟨s.2.1, s.2.2.1, s.2.2.2, (), ()⟩).symm

theorem residualContinuationPolicy_original {H S I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (n : Nat) (keep : S → ClosingLayer H I₁ I₂ n) :
    residualContinuationPolicy (strategyContinuationPolicy σ past) n keep =
      strategyContinuationPolicy σ (closingLayerHistory past n ∘ keep) := by
  funext k s
  unfold residualContinuationPolicy strategyContinuationPolicy
  erw [graftClosingLayer_history past n keep (k+1) s]

theorem continuationTrace_same_history {H S I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (other : S → EnvHistory I₁ I₂)
    (h : H) (s : S) (same : past h = other s) (env : Nat → I₁ × I₂ × Graph) :
    continuationTrace (strategyContinuationPolicy σ past) h env =
      continuationTrace (strategyContinuationPolicy σ other) s env := by
  funext n
  unfold continuationTrace strategyContinuationPolicy
  rw [continuationScenario_history, continuationScenario_history, same]

/-- A single original strategy wins from every finite source history when
the incoming labels are its actual residual states. This holds for arbitrary
families and arbitrary physical depths. -/
theorem continuationWins_at_histories {H I₁ I₂ O₁ O₂ : Type}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n)))
    (past : H → EnvHistory I₁ I₂) :
    ContinuationWins objective.AcceptsFrom
      (fun h => strategyHistoryLabel σ (fun q input output => objective.step q (input, output))
        objective.initial (past h)) (strategyContinuationPolicy σ past) := by
  intro h env
  let empty : Unit → EnvHistory I₁ I₂ := fun _ => []
  let step := fun q input output => objective.step q (input, output)
  obtain ⟨s, exactHistory⟩ := closingLayer_contains_append empty () (past h).length (past h) rfl
  have history : closingLayerHistory empty (past h).length s = past h := by
    simpa only [empty, List.nil_append] using exactHistory
  have labels := continuationLabels_original σ empty step objective.initial
    (fun _ => objective.initial) (fun _ => rfl) (past h).length s
  rw [history] at labels
  have residual := residualContinuationPolicy_wins step objective.AcceptsFrom
    (parity_residualAcceptance objective) (fun _ : Unit => objective.initial)
    (strategyContinuationPolicy σ empty) (rootContinuation_wins_of_execution objective σ winning)
    (past h).length (fun _ : Unit => s)
  rw [residualContinuationPolicy_original] at residual
  have result := residual () env
  change objective.AcceptsFrom
    (continuationLabels step (fun _ : Unit => objective.initial) (strategyContinuationPolicy σ empty)
      (past h).length s)
    (continuationTrace (strategyContinuationPolicy σ (closingLayerHistory empty (past h).length ∘ fun _ : Unit => s)) () env) at result
  rw [labels, continuationTrace_same_history σ _ past () h history env] at result
  exact result

/-- The physical monitor required by joint phase compression is now an
explicit automaton and its winning premise follows from the original global
strategy. Instantiate objective with guardedPhysicalObjective for the
original omega-regular adversary and the LTL automaton. -/
theorem jointPhaseObjective_of_global_winning {H G I₁ I₂ O₁ O₂ : Type} [Fintype H]
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n)))
    (past : H → EnvHistory I₁ I₂) (group : H → G)
    (base : G → View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base (group h))
    (D : Nat) :
    ∀ env, (jointPhaseObjective objective
      (fun h => strategyHistoryLabel σ (fun q input output => objective.step q (input, output))
        objective.initial (past h)) group).WinsPlay
      (phasePhysicalPlay Prod.fst
        (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env)) :=
  jointPhaseObjective_original_wins objective _ group σ past base same
    (continuationWins_at_histories objective σ winning past) D

end Characterisation
