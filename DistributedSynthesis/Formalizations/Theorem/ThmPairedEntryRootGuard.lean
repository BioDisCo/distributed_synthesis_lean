/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryRationalTree
import DistributedSynthesis.Formalizations.Theorem.ThmRootGuardedInputFreeRationalRun
import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialBlockFromWinning

/-!
# Finite overlap guards at a paired-entry root

At a delayed switch only one output table overlaps the old and new block:
after an actual left boundary, the process-one output on a zero-length right
block closed by `both`; after an actual right boundary, the process-two mirror.
The old entry row is resolved by that receive, so the other latent row need
not be identified with it.

This file makes the guarded transition independent of the raw histories.  A
guard is a predicate on the paired lambda selected at the fresh root.  The raw
strategy run satisfies the guard whenever its generated root lambda does, and
the generic one-shot construction preserves it through rationalization.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Finite process-one overlap table used when an actual left boundary is
closed immediately by a `both` round. -/
abbrev ProcOneEntryOverlapProfile := (In₂ × In₁) -> Out₁

/-- Process-two mirror. -/
abbrev ProcTwoEntryOverlapProfile := (In₁ × In₂) -> Out₂

def ProcOneEntryOverlapProfile.Matches
    (profile : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ move, lambda.bothOneLeft [] move = profile move

def ProcTwoEntryOverlapProfile.Matches
    (profile : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ move, lambda.bothTwoRight [] move = profile move

/-! ## The generated initial-boundary profiles are genuinely guarded -/

/-- The process-one table used by the old initial-left block on the next
`both` round.  The paired right-block move order is `(inputTwo,inputOne)`. -/
def initialLeftNextBothProfile
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) :=
  fun nextMove =>
    (initialLeftLambdaOfStrategy strategy).informedOne
      (past ++ [move]) (nextMove.2, nextMove.1)

/-- The genuine paired memory staged after an actual left boundary selects a
root lambda whose left-row `both` output is exactly the old block's finite
next-round table. -/
theorem initialLeftNextBothProfile_matches_generated
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let base := extendPrefix strategy [] (past.map leftEnvironment)
    let entry := procOneFreshPair strategy base
      (strategyGenerated_extendPrefix_basic strategy
        StrategyGeneratedPrefix.empty _) move.1 move.2
    (initialLeftNextBothProfile strategy past move).Matches
      entry.lambdaOfStrategy := by
  intro base entry nextMove
  simp [ProcOneEntryOverlapProfile.Matches,
    initialLeftNextBothProfile, initialLeftLambdaOfStrategy,
    ProcOnePairedEntryRep.lambdaOfStrategy, entry, base,
    procOneFreshPair, blockReceiverOne, List.map_append,
    extendPrefix_snoc]
  have hboth := blockReceiverOne_eq_both strategy
    ((extendPrefix strategy [] (past.map leftEnvironment)).append
      (nextRound strategy
        (extendPrefix strategy [] (past.map leftEnvironment))
        (leftEnvironment move))) [] (nextMove.2, nextMove.1)
  simpa [blockReceiverOne, leftEnvironment] using hboth.symm

/-- Process-two mirror table after an actual right boundary. -/
def initialRightNextBothProfile
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂) :=
  fun nextMove =>
    (initialRightLambdaOfStrategy strategy).informedTwo
      (past ++ [move]) (nextMove.2, nextMove.1)

theorem initialRightNextBothProfile_matches_generated
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let base := extendPrefix strategy [] (past.map rightEnvironment)
    let entry := procTwoFreshPair strategy base
      (strategyGenerated_extendPrefix_basic strategy
        StrategyGeneratedPrefix.empty _) move.2 move.1
    (initialRightNextBothProfile strategy past move).Matches
      entry.lambdaOfStrategy := by
  intro base entry nextMove
  simp [ProcTwoEntryOverlapProfile.Matches,
    initialRightNextBothProfile, initialRightLambdaOfStrategy,
    ProcTwoPairedEntryRep.lambdaOfStrategy, entry, base,
    procTwoFreshPair, blockReceiverTwo, List.map_append,
    extendPrefix_snoc]
  have hboth := blockReceiverTwo_eq_both strategy
    ((extendPrefix strategy [] (past.map rightEnvironment)).append
      (nextRound strategy
        (extendPrefix strategy [] (past.map rightEnvironment))
        (rightEnvironment move))) [] (nextMove.2, nextMove.1)
  simpa [blockReceiverTwo, rightEnvironment] using hboth.symm

/-- Root transition of the paired automaton, additionally guarding the lambda
selected in either live orientation. -/
def pairedEntryRootGuard
    (initialState : PairedEntryTreeState A)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (children : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) ->
      PairedEntryTreeState A) : Prop :=
  match initialState with
  | Sum.inl _ => ∀ direction, children direction = Sum.inl PUnit.unit
  | Sum.inr (Sum.inl (code, _)) =>
      ∃ lambda : ProcOnePairedRightLambda
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
        rightAllowed lambda ∧ PairedRightForeverAccepts A code lambda ∧
          ∀ direction,
            children direction =
              match direction with
              | .fromOne row past move => pairedOneChild A code lambda row past move
              | .fromTwo _ _ _ => Sum.inl PUnit.unit
  | Sum.inr (Sum.inr (code, _)) =>
      ∃ lambda : ProcTwoPairedLeftLambda
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
        leftAllowed lambda ∧ PairedLeftForeverAccepts A code lambda ∧
          ∀ direction,
            children direction =
              match direction with
              | .fromOne _ _ _ => Sum.inl PUnit.unit
              | .fromTwo row past move => pairedTwoChild A code lambda row past move

theorem pairedEntryRootGuard_implies_delta
    (initialState : PairedEntryTreeState A)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    {children : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) ->
      PairedEntryTreeState A}
    (hguard : pairedEntryRootGuard A initialState rightAllowed leftAllowed children) :
    pairedEntryDelta A initialState PUnit.unit children := by
  cases initialState with
  | inl sink => exact hguard
  | inr live =>
      cases live with
      | inl right =>
          rcases hguard with ⟨lambda, _, hforever, hchildren⟩
          exact ⟨lambda, hforever, hchildren⟩
      | inr left =>
          rcases hguard with ⟨lambda, _, hforever, hchildren⟩
          exact ⟨lambda, hforever, hchildren⟩

namespace PairedStrategyMemory

/-- The model-generated root lambda satisfies the supplied orientation guard.
Only the live orientation is relevant. -/
def RootLambdaAllowed
    [Inhabited In₁] [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : PairedStrategyMemory A strategy)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop) : Prop :=
  match initial with
  | .sink => True
  | .processOne entry _ => rightAllowed entry.lambdaOfStrategy
  | .processTwo entry _ => leftAllowed entry.lambdaOfStrategy

/-- The raw paired run satisfies the guarded transition at its root. -/
theorem rootGuard_at_run
    [Inhabited In₁] [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : PairedStrategyMemory A strategy)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (hforever : ForeverAccepts (A := A) initial)
    (hallowed : RootLambdaAllowed (A := A) initial rightAllowed leftAllowed) :
    pairedEntryRootGuard A initial.toTreeState rightAllowed leftAllowed
      (fun direction => run (A := A) initial [direction]) := by
  cases initial with
  | sink =>
      intro direction
      rfl
  | processOne entry minimum =>
      refine ⟨entry.lambdaOfStrategy, hallowed, ?_, ?_⟩
      · simpa [ForeverAccepts] using hforever []
      · intro direction
        simpa [run, atNode] using
          (toTreeState_step (A := A)
            (PairedStrategyMemory.processOne entry minimum) direction)
  | processTwo entry minimum =>
      refine ⟨entry.lambdaOfStrategy, hallowed, ?_, ?_⟩
      · simpa [ForeverAccepts] using hforever []
      · intro direction
        simpa [run, atNode] using
          (toTreeState_step (A := A)
            (PairedStrategyMemory.processTwo entry minimum) direction)

/-- End-to-end one-shot guarded rationalization of a generated paired run. -/
theorem rootGuarded_hasRationalRun
    [Inhabited In₁] [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : PairedStrategyMemory A strategy)
    (rightAllowed : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (leftAllowed : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) -> Prop)
    (hforever : ForeverAccepts (A := A) initial)
    (hswitching : SwitchingAccepts (A := A) initial)
    (hallowed : RootLambdaAllowed (A := A) initial rightAllowed leftAllowed)
    (basis :
      ((pairedEntryRunAutomaton A initial.toTreeState).rootGuarded
        (pairedEntryRootGuard A initial.toTreeState
          rightAllowed leftAllowed)).RationalRunBasis) :
    ((pairedEntryRunAutomaton A initial.toTreeState).rootGuarded
      (pairedEntryRootGuard A initial.toTreeState
        rightAllowed leftAllowed)).HasRationalRun := by
  apply InputFreeRunParityTreeAutomaton.rootGuarded_hasRationalRun
    (pairedEntryRunAutomaton A initial.toTreeState)
    (pairedEntryRootGuard A initial.toTreeState rightAllowed leftAllowed)
    (run (A := A) initial)
    (isAcceptingRun (A := A) initial hforever hswitching)
  · exact rootGuard_at_run A initial rightAllowed leftAllowed hforever hallowed
  · exact basis

end PairedStrategyMemory

end DetParityAutomaton

end DistributedSynthesis
