/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialBlockRegularization

/-!
# Initial-block regularization from a winning strategy

This file supplies the mathematical witness required by the finite initial
block monitors.  It restricts the original distributed strategy to an
initial homogeneous block and stages both locally indistinguishable closing
graphs.  No process is told which process is the strict leader: every output
is read from that process's actual local view.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- The original strategy, restricted to the initial left block.  At a
possible close, process one supplies its right/no-receive value and process
two supplies its right/receive value.  The `both` values are shared exactly
where the corresponding local views are equal. -/
def initialLeftLambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blindTwo := blockSenderTwo strategy []
  informedOne := blockReceiverOne strategy []
  reversingOne := fun past move =>
    strategy.one
      (nextView Proc.one
        (extendPrefix strategy [] (past.map leftEnvironment))
        (rightEnvironment (move.2, move.1)))
  reversingTwo := fun past move =>
    strategy.two
      (nextView Proc.two
        (extendPrefix strategy [] (past.map leftEnvironment))
        (rightEnvironment (move.2, move.1)))

/-- The initial-left scan is exactly the objective scan of the actual
strategy-generated left prefix. -/
theorem initialLeftScanAfter_lambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) :
    initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past =
      blockEndAndMin A A.initial
        (extendPrefix strategy [] (past.map leftEnvironment)) := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [initialLeftScanAfter_append, List.map_append, List.map_singleton,
        extendPrefix_snoc]
      simp only [History.append]
      rw [blockEndAndMin_snoc, ih]
      simp only [initialLeftScanStep, initialBlockScanStep,
        initialLeftLetterAt, initialLeftLambdaOfStrategy]
      rw [blockSenderTwo_eq strategy [] past move]
      simp [blockReceiverOne, leftEnvironment, nextRound, leftRoundRecord]

/-- The staged close target is literally the fresh process-two paired memory
of the original strategy at the same generated prefix. -/
theorem initialLeftCloseTarget_lambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    initialLeftCloseTarget A
        (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past)
        (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy) past move) =
      (PairedStrategyMemory.processTwo
        (procTwoFreshPair strategy
          (extendPrefix strategy [] (past.map leftEnvironment))
          (strategyGenerated_extendPrefix_basic strategy
            StrategyGeneratedPrefix.empty _)
          move.1 move.2)
        (blockMinState A A.initial
          (extendPrefix strategy [] (past.map leftEnvironment)))).toTreeState := by
  rw [initialLeftScanAfter_lambdaOfStrategy A strategy past]
  apply congrArg (fun code => Sum.inr (Sum.inr
    (code, blockMinState A A.initial
      (extendPrefix strategy [] (past.map leftEnvironment)))))
  apply Prod.ext
  · simp [initialLeftCloseTarget, initialLeftLetterAt,
      initialLeftLambdaOfStrategy, blockEndAndMin_fst_eq_foldl,
      ProcTwoPairedEntryRep.code, procTwoFreshPair,
      entryState, History.append, List.foldl_append, nextRound,
      rightRoundRecord, rightEnvironment]
  · simp only [initialLeftCloseTarget, initialLeftLetterAt,
      initialLeftLambdaOfStrategy]
    rw [blockReceiverOne_eq_both]
    simp [
      initialLeftLambdaOfStrategy, blockEndAndMin_fst_eq_foldl,
      ProcTwoPairedEntryRep.code, procTwoFreshPair,
      entryState, History.append, List.foldl_append, nextRound,
      bothRoundRecord, rightEnvironment, nextView,
      advanceViewsWithEnvironment]

/-- If the original strategy wins, its restriction wins an initial left
block that never closes. -/
theorem initialLeftForeverAccepts_lambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    InitialLeftForeverAccepts A (initialLeftLambdaOfStrategy strategy) := by
  intro env
  have haccept := hwin (leftBlockEnvironment
    ([] : History In₁ In₂ Graph Out₁ Out₂) env)
  have hword :
      initialLeftOmegaWord (initialLeftLambdaOfStrategy strategy) env =
        execution strategy (leftBlockEnvironment
          ([] : History In₁ In₂ Graph Out₁ Out₂) env) := by
    funext n
    have hplay := execution_leftBlockEnvironment_eq_pairPlay strategy
      StrategyGeneratedPrefix.empty env n
    simpa [initialLeftOmegaWord, initialLeftLetterAt,
      initialLeftLambdaOfStrategy, initialLeftReceiverStrategy,
      initialLeftSenderStrategy, initialLeft_pairPlay_eq_letterAt,
      realizedRoundRecord, pairPlay, treePlay, treeOfPair,
      branchNode_eq_omegaPrefix, blockLabelApply,
      leftBlockEnvironment, History.length, leftRoundRecord] using hplay.symm
  rw [hword]
  exact haccept

/-- Every staged initial-left close has a rational recurrent continuation. -/
theorem initialLeftCloseFeasible_lambdaOfStrategy
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    InitialLeftCloseFeasible A (initialLeftLambdaOfStrategy strategy) := by
  intro past move
  rw [initialLeftCloseTarget_lambdaOfStrategy A strategy past move]
  exact PairedStrategyMemory.hasRationalRun_of_winning_flattened
    (A := A) hwin _ (basis _)

/-- The winning strategy therefore supplies the complete witness required by
the unconditional initial-left tree-automaton narrowing theorem. -/
theorem exists_initialLeftLambda_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    ∃ lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      InitialLeftForeverAccepts A lambda ∧ InitialLeftCloseFeasible A lambda :=
  ⟨initialLeftLambdaOfStrategy strategy,
    initialLeftForeverAccepts_lambdaOfStrategy A strategy hwin,
    initialLeftCloseFeasible_lambdaOfStrategy A strategy hwin basis⟩

/-! ## Initial right block -/

/-- Process-swapped restriction of the original strategy to the initial
right block. -/
def initialRightLambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blindOne := blockSenderOne strategy []
  informedTwo := blockReceiverTwo strategy []
  reversingOne := fun past move =>
    strategy.one
      (nextView Proc.one
        (extendPrefix strategy [] (past.map rightEnvironment))
        (leftEnvironment (move.2, move.1)))
  reversingTwo := fun past move =>
    strategy.two
      (nextView Proc.two
        (extendPrefix strategy [] (past.map rightEnvironment))
        (leftEnvironment (move.2, move.1)))

theorem initialRightScanAfter_lambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) :
    initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past =
      blockEndAndMin A A.initial
        (extendPrefix strategy [] (past.map rightEnvironment)) := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [initialRightScanAfter_append, List.map_append, List.map_singleton,
        extendPrefix_snoc]
      simp only [History.append]
      rw [blockEndAndMin_snoc, ih]
      simp only [initialRightScanStep, initialBlockScanStep,
        initialRightLetterAt, initialRightLambdaOfStrategy]
      rw [blockSenderOne_eq strategy [] past move]
      simp [blockReceiverTwo, rightEnvironment, nextRound, rightRoundRecord]

/-- The mirror staged target is the actual fresh process-one paired memory. -/
theorem initialRightCloseTarget_lambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    initialRightCloseTarget A
        (initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past)
        (initialRightLetterAt (initialRightLambdaOfStrategy strategy) past move) =
      (PairedStrategyMemory.processOne
        (procOneFreshPair strategy
          (extendPrefix strategy [] (past.map rightEnvironment))
          (strategyGenerated_extendPrefix_basic strategy
            StrategyGeneratedPrefix.empty _)
          move.2 move.1)
        (blockMinState A A.initial
          (extendPrefix strategy [] (past.map rightEnvironment)))).toTreeState := by
  rw [initialRightScanAfter_lambdaOfStrategy A strategy past]
  apply congrArg (fun code => Sum.inr (Sum.inl
    (code, blockMinState A A.initial
      (extendPrefix strategy [] (past.map rightEnvironment)))))
  apply Prod.ext
  · simp [initialRightLetterAt, initialRightLambdaOfStrategy,
      blockEndAndMin_fst_eq_foldl, ProcOnePairedEntryRep.code,
      procOneFreshPair, entryState, History.append, List.foldl_append,
      nextRound, leftRoundRecord, leftEnvironment]
  · simp only [initialRightLetterAt, initialRightLambdaOfStrategy]
    rw [blockReceiverTwo_eq_both]
    simp [blockEndAndMin_fst_eq_foldl, ProcOnePairedEntryRep.code,
      procOneFreshPair, entryState, History.append, List.foldl_append,
      nextRound, bothRoundRecord, leftEnvironment, nextView,
      advanceViewsWithEnvironment]

theorem initialRightForeverAccepts_lambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    InitialRightForeverAccepts A (initialRightLambdaOfStrategy strategy) := by
  intro env
  have haccept := hwin (rightBlockEnvironment
    ([] : History In₁ In₂ Graph Out₁ Out₂) env)
  have hword :
      initialRightOmegaWord (initialRightLambdaOfStrategy strategy) env =
        execution strategy (rightBlockEnvironment
          ([] : History In₁ In₂ Graph Out₁ Out₂) env) := by
    funext n
    have hplay := execution_rightBlockEnvironment_eq_pairPlay strategy
      StrategyGeneratedPrefix.empty env n
    simpa [initialRightOmegaWord, initialRightLetterAt,
      initialRightLambdaOfStrategy, initialRightReceiverStrategy,
      initialRightSenderStrategy, initialRight_pairPlay_eq_letterAt,
      realizedRoundRecordRight, pairPlay, treePlay, treeOfPair,
      branchNode_eq_omegaPrefix, blockLabelApply,
      rightBlockEnvironment, History.length, rightRoundRecord] using hplay.symm
  rw [hword]
  exact haccept

theorem initialRightCloseFeasible_lambdaOfStrategy
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    InitialRightCloseFeasible A (initialRightLambdaOfStrategy strategy) := by
  intro past move
  rw [initialRightCloseTarget_lambdaOfStrategy A strategy past move]
  exact PairedStrategyMemory.hasRationalRun_of_winning_flattened
    (A := A) hwin _ (basis _)

theorem exists_initialRightLambda_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    ∃ lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      InitialRightForeverAccepts A lambda ∧ InitialRightCloseFeasible A lambda :=
  ⟨initialRightLambdaOfStrategy strategy,
    initialRightForeverAccepts_lambdaOfStrategy A strategy hwin,
    initialRightCloseFeasible_lambdaOfStrategy A strategy hwin basis⟩

end DetParityAutomaton

end DistributedSynthesis
