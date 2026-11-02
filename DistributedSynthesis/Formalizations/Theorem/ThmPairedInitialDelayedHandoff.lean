/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialBlockFromWinning

/-!
# Delay-one initial handoff

The first recurrent controller cannot be selected from the first opposite
round: by then that round already belongs to the new homogeneous block.  The
correct delay-one construction stages, after every initial `left`/`both`
round, the paired process-one entry for a possible following right block (and
symmetrically stages a process-two entry after `right`/`both`).  If the next
round reverses, the process that becomes blind already received at the staged
boundary and therefore knows the finite paired key.  No strict-leader signal
is used.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## Target staged by an initial left block -/

/-- The process-one/right-block entry staged by one possible final
`left`/`both` round of the initial left block.  The stored minimum summarizes
the strict prefix; the two fresh DPA states consume the boundary round. -/
def initialLeftDelayedTarget
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    PairedEntryTreeState A :=
  let leftState := A.step scan.1
    (leftRoundRecord letter.1 letter.2.1.informedOne letter.2.2)
  let bothState := A.step scan.1
    (bothRoundRecord letter.1 letter.2.1.informedOne
      letter.2.1.reversingTwo)
  Sum.inr (Sum.inl ((leftState, bothState), scan.2))

/-- For the original distributed strategy, the delayed target is exactly the
generated `left`/`both` paired entry at that boundary. -/
theorem initialLeftDelayedTarget_lambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    initialLeftDelayedTarget A
        (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy) past)
        (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy) past move) =
      (PairedStrategyMemory.processOne
        (procOneFreshPair strategy
          (extendPrefix strategy [] (past.map leftEnvironment))
          (strategyGenerated_extendPrefix_basic strategy
            StrategyGeneratedPrefix.empty _)
          move.1 move.2)
        (blockMinState A A.initial
          (extendPrefix strategy [] (past.map leftEnvironment)))).toTreeState := by
  rw [initialLeftScanAfter_lambdaOfStrategy A strategy past]
  apply congrArg (fun code => Sum.inr (Sum.inl
    (code, blockMinState A A.initial
      (extendPrefix strategy [] (past.map leftEnvironment)))))
  apply Prod.ext
  · simp only [initialLeftDelayedTarget, initialLeftLetterAt,
      initialLeftLambdaOfStrategy]
    rw [blockSenderTwo_eq strategy [] past move]
    simp [blockEndAndMin_fst_eq_foldl,
      ProcOnePairedEntryRep.code, procOneFreshPair, entryState,
      History.append, List.foldl_append, nextRound, leftRoundRecord,
      blockReceiverOne, leftEnvironment]
  · simp only [initialLeftDelayedTarget, initialLeftLetterAt,
      initialLeftLambdaOfStrategy]
    rw [blockReceiverOne_eq_both]
    simp [blockEndAndMin_fst_eq_foldl, ProcOnePairedEntryRep.code,
      procOneFreshPair, entryState, History.append, List.foldl_append,
      nextRound, bothRoundRecord, leftEnvironment, rightEnvironment, nextView,
      advanceViewsWithEnvironment]

def InitialLeftDelayedFeasible
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ past move,
    (pairedEntryRunAutomaton A
      (initialLeftDelayedTarget A (initialLeftScanAfter A lambda past)
        (initialLeftLetterAt lambda past move))).HasRationalRun

/-- A winning strategy makes every correctly delayed initial-left target
feasible. -/
theorem initialLeftDelayedFeasible_lambdaOfStrategy
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    InitialLeftDelayedFeasible A (initialLeftLambdaOfStrategy strategy) := by
  intro past move
  rw [initialLeftDelayedTarget_lambdaOfStrategy A strategy past move]
  exact PairedStrategyMemory.hasRationalRun_of_winning_flattened
    (A := A) hwin _ (basis _)

/-! ## Mirror target staged by an initial right block -/

/-- Process-two/left-block entry staged by a possible final `right`/`both`
round of the initial right block. -/
def initialRightDelayedTarget
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    PairedEntryTreeState A :=
  let move : In₁ × In₂ := (letter.1.2, letter.1.1)
  let rightState := A.step scan.1
    (rightRoundRecord letter.1 letter.2.2 letter.2.1.informedTwo)
  let bothState := A.step scan.1
    (bothRoundRecord move letter.2.1.reversingOne
      letter.2.1.informedTwo)
  Sum.inr (Sum.inr ((rightState, bothState), scan.2))

theorem initialRightDelayedTarget_lambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    initialRightDelayedTarget A
        (initialRightScanAfter A (initialRightLambdaOfStrategy strategy) past)
        (initialRightLetterAt (initialRightLambdaOfStrategy strategy) past move) =
      (PairedStrategyMemory.processTwo
        (procTwoFreshPair strategy
          (extendPrefix strategy [] (past.map rightEnvironment))
          (strategyGenerated_extendPrefix_basic strategy
            StrategyGeneratedPrefix.empty _)
          move.2 move.1)
        (blockMinState A A.initial
          (extendPrefix strategy [] (past.map rightEnvironment)))).toTreeState := by
  rw [initialRightScanAfter_lambdaOfStrategy A strategy past]
  apply congrArg (fun code => Sum.inr (Sum.inr
    (code, blockMinState A A.initial
      (extendPrefix strategy [] (past.map rightEnvironment)))))
  apply Prod.ext
  · simp only [initialRightDelayedTarget, initialRightLetterAt,
      initialRightLambdaOfStrategy]
    rw [blockSenderOne_eq strategy [] past move]
    simp [blockEndAndMin_fst_eq_foldl,
      ProcTwoPairedEntryRep.code, procTwoFreshPair, entryState,
      History.append, List.foldl_append, nextRound, rightRoundRecord,
      blockReceiverTwo, rightEnvironment]
  · simp only [initialRightDelayedTarget, initialRightLetterAt,
      initialRightLambdaOfStrategy]
    have hone :
        strategy.one
            (nextView Proc.one
              (extendPrefix strategy [] (past.map rightEnvironment))
              (leftEnvironment (move.2, move.1))) =
          strategy.one
            (nextView Proc.one
              (extendPrefix strategy [] (past.map rightEnvironment))
              ⟨move.2, move.1, Graph.both⟩) := by
      rfl
    rw [hone]
    rw [blockReceiverTwo_eq_both]
    simp [blockEndAndMin_fst_eq_foldl, ProcTwoPairedEntryRep.code,
      procTwoFreshPair, entryState, History.append, List.foldl_append,
      nextRound, bothRoundRecord, rightEnvironment, nextView,
      advanceViewsWithEnvironment]

def InitialRightDelayedFeasible
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ past move,
    (pairedEntryRunAutomaton A
      (initialRightDelayedTarget A (initialRightScanAfter A lambda past)
        (initialRightLetterAt lambda past move))).HasRationalRun

theorem initialRightDelayedFeasible_lambdaOfStrategy
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    InitialRightDelayedFeasible A (initialRightLambdaOfStrategy strategy) := by
  intro past move
  rw [initialRightDelayedTarget_lambdaOfStrategy A strategy past move]
  exact PairedStrategyMemory.hasRationalRun_of_winning_flattened
    (A := A) hwin _ (basis _)

end DetParityAutomaton

end DistributedSynthesis
