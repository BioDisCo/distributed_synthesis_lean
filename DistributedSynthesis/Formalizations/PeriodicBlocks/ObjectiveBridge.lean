/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.Reduction
import DistributedSynthesis.Library.Distributed.LeaderPhases.InputParityObjective

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

def environmentWord {I₁ I₂ : Type} (env : EnvironmentSequence I₁ I₂)
    (n : Nat) : RoundRecord I₁ I₂ Graph Unit Unit :=
  ⟨(env n).inputOne,(env n).inputTwo,(env n).graph,(),()⟩

def wordEnvironment {I₁ I₂ : Type} (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit) :
    EnvironmentSequence I₁ I₂ := fun n => ⟨(word n).inputOne,(word n).inputTwo,(word n).graph⟩

@[simp] theorem environmentWord_wordEnvironment {I₁ I₂ : Type}
    (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit) : environmentWord (wordEnvironment word) = word := by
  funext n
  dsimp only [environmentWord,wordEnvironment]

theorem environmentWord_graph {I₁ I₂ : Type} (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    History.graphSequence (branchNode (environmentWord env) n) = branchNode (fun t => (env t).graph) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [branchNode,History.graphSequence,List.map_append,List.map_singleton,environmentWord] using
      congrArg (fun xs => xs++[(env n).graph]) ih

theorem environmentWord_views {I₁ I₂ O₁ O₂ : Type} (σ : StrategyPair I₁ I₂ O₁ O₂)
    (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    viewPair (executionPrefix σ env n) = viewPair (branchNode (environmentWord env) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [executionPrefix_succ,viewPair_append]
    change advanceViews _ _ = viewPair (History.append (branchNode (environmentWord env) n)
      ⟨(env n).inputOne,(env n).inputTwo,(env n).graph,(),()⟩)
    rw [viewPair_append,ih]
    cases g : (env n).graph <;> simp only [advanceViews,nextRound,g]

theorem environmentWord_outputs {I₁ I₂ O₁ O₂ : Type} (σ : StrategyPair I₁ I₂ O₁ O₂)
    (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    recordContinuationLetter (execution σ env n) =
      (((env n).inputOne,(env n).inputTwo,(env n).graph),
       (σ.one (currentView .one (branchNode (environmentWord env) (n+1))),
        σ.two (currentView .two (branchNode (environmentWord env) (n+1))))) := by
  have one := congrArg Prod.fst (environmentWord_views σ env (n+1))
  have two := congrArg Prod.snd (environmentWord_views σ env (n+1))
  change currentView .one (executionPrefix σ env (n+1)) = _ at one
  change currentView .two (executionPrefix σ env (n+1)) = _ at two
  rw [currentView_executionPrefix_succ] at one two
  rw [execution_apply]
  exact Prod.ext rfl (Prod.ext (congrArg σ.one one) (congrArg σ.two two))

theorem objective_run_history {I₁ I₂ O₁ O₂ : Type}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    objective.run (fun t => recordContinuationLetter (execution σ env t)) n =
      strategyHistoryLabel σ (fun q e y => objective.step q (e,y)) objective.initial
        (branchNode (environmentWord env) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change objective.step (objective.run _ n) (recordContinuationLetter (execution σ env n)) = _
    rw [ih,environmentWord_outputs]
    change _ = strategyHistoryLabel σ _ _ (branchNode (environmentWord env) n ++ [environmentWord env n])
    rw [strategyHistoryLabel_append]
    rfl

theorem objective_accepts_history_iff {I₁ I₂ O₁ O₂ : Type}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂) :
    objective.Accepts (fun n => recordContinuationLetter (execution σ env n)) ↔
      NatSeqMinEvenParity (fun n => objective.priority
        (strategyHistoryLabel σ (fun q e y => objective.step q (e,y)) objective.initial
          (branchNode (environmentWord env) n))) := by
  rw [objective.accepts_iff_natSeqMinEvenParity]
  simp only [objective_run_history]

theorem objective_realizability_history_iff {I₁ I₂ O₁ O₂ : Type}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂)) :
    (∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ env,
      objective.Accepts (fun n => recordContinuationLetter (execution σ env n))) ↔
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
      NatSeqMinEvenParity (fun n => objective.priority
        (strategyHistoryLabel σ (fun q e y => objective.step q (e,y)) objective.initial (branchNode word n))) := by
  constructor
  · rintro ⟨σ,winning⟩
    refine ⟨σ,fun word => ?_⟩
    simpa only [environmentWord_wordEnvironment] using
      (objective_accepts_history_iff objective σ (wordEnvironment word)).mp (winning (wordEnvironment word))
  · rintro ⟨σ,winning⟩
    exact ⟨σ,fun env => (objective_accepts_history_iff objective σ env).mpr (winning _)⟩

end Characterisation.PeriodicBlocks
