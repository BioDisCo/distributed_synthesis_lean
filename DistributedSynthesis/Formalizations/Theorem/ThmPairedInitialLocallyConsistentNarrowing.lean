/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmRootPinnedBlockNarrowing
import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialLocalConsistency

/-!
# Locally consistent finite initial controllers

This replaces the permissive initial-block extraction by the table-first
constrained narrowing theorem.  Besides winning and root compatibility, the
finite controllers retain the actual distributed information law at a
one-sided reversal: the process that does not receive cannot vary its output
with the other process's current input.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Root-compatible controllers together with the two missing local laws. -/
structure LocallyConsistentInitialControllers
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    extends RootCompatibleInitialControllers A strategy where
  leftLocal : NarrowedTablesAllowed
    ((initialLeftBlockMonitor A).rootPinned
      (fun move => initialLeftLetterAt
        (initialLeftLambdaOfStrategy strategy) [] move))
    InitialLeftTableLocallyConsistent leftController.labeledTree
  rightLocal : NarrowedTablesAllowed
    ((initialRightBlockMonitor A).rootPinned
      (fun move => initialRightLetterAt
        (initialRightLambdaOfStrategy strategy) [] move))
    InitialRightTableLocallyConsistent rightController.labeledTree

/-- A winning distributed strategy yields finite initial controllers without
introducing a strict-leader signal or hidden-current-input dependence. -/
noncomputable def locallyConsistentInitialControllers_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    LocallyConsistentInitialControllers A strategy := by
  classical
  let leftLambda := initialLeftLambdaOfStrategy strategy
  let leftExpected := fun move => initialLeftLetterAt leftLambda [] move
  let leftPin := (initialLeftBlockMonitor A).rootPinned leftExpected
  have hleftBase : ∀ env : Nat -> In₁ × In₂,
      (initialLeftBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy leftLambda)
          (initialLeftSenderStrategy leftLambda) env) :=
    initialLeftBlockMonitor_realizable A leftLambda
      (initialLeftForeverAccepts_lambdaOfStrategy A strategy hwin)
      (initialLeftCloseFeasible_lambdaOfStrategy A strategy hwin basis)
  have hleftRoot : ∀ move : In₁ × In₂,
      pairPlay (initialLeftReceiverStrategy leftLambda)
          (initialLeftSenderStrategy leftLambda) (fun _ => move) 0 =
        leftExpected move := by
    intro move
    simpa [leftExpected, leftLambda] using
      initialLeft_pairPlay_eq_letterAt leftLambda (fun _ => move) 0
  have hleftWin : ∀ env : Nat -> In₁ × In₂,
      leftPin.WinsPlay
        (pairPlay (initialLeftReceiverStrategy leftLambda)
          (initialLeftSenderStrategy leftLambda) env) :=
    (initialLeftBlockMonitor A).rootPinned_realizable leftExpected _ _
      hleftBase hleftRoot
  let leftDefault : In₁ × In₂ ->
      InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) :=
    fun _ => default
  have hleftDefault : InitialLeftTableLocallyConsistent leftDefault := by
    intro _ _ _
    rfl
  have hleftAllowed : ∀ past,
      InitialLeftTableLocallyConsistent
        (initialLeftReceiverStrategy leftLambda past) := by
    intro past
    exact initialLeftTableLocallyConsistent_lambdaOfStrategy strategy past
  have hleftControllers :=
    exists_implementable_controller_of_block_realizable_tablesAllowed
      leftPin InitialLeftTableLocallyConsistent leftDefault hleftDefault
      (initialLeftReceiverStrategy leftLambda)
      (initialLeftSenderStrategy leftLambda) hleftWin hleftAllowed
  let leftController := Classical.choose hleftControllers
  have hleftSpec := Classical.choose_spec hleftControllers
  have leftWins := hleftSpec.1
  have leftLocal := hleftSpec.2

  let rightLambda := initialRightLambdaOfStrategy strategy
  let rightExpected := fun move => initialRightLetterAt rightLambda [] move
  let rightPin := (initialRightBlockMonitor A).rootPinned rightExpected
  have hrightBase : ∀ env : Nat -> In₂ × In₁,
      (initialRightBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy rightLambda)
          (initialRightSenderStrategy rightLambda) env) :=
    initialRightBlockMonitor_realizable A rightLambda
      (initialRightForeverAccepts_lambdaOfStrategy A strategy hwin)
      (initialRightCloseFeasible_lambdaOfStrategy A strategy hwin basis)
  have hrightRoot : ∀ move : In₂ × In₁,
      pairPlay (initialRightReceiverStrategy rightLambda)
          (initialRightSenderStrategy rightLambda) (fun _ => move) 0 =
        rightExpected move := by
    intro move
    simpa [rightExpected, rightLambda] using
      initialRight_pairPlay_eq_letterAt rightLambda (fun _ => move) 0
  have hrightWin : ∀ env : Nat -> In₂ × In₁,
      rightPin.WinsPlay
        (pairPlay (initialRightReceiverStrategy rightLambda)
          (initialRightSenderStrategy rightLambda) env) :=
    (initialRightBlockMonitor A).rootPinned_realizable rightExpected _ _
      hrightBase hrightRoot
  let rightDefault : In₂ × In₁ ->
      InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) :=
    fun _ => default
  have hrightDefault : InitialRightTableLocallyConsistent rightDefault := by
    intro _ _ _
    rfl
  have hrightAllowed : ∀ past,
      InitialRightTableLocallyConsistent
        (initialRightReceiverStrategy rightLambda past) := by
    intro past
    exact initialRightTableLocallyConsistent_lambdaOfStrategy strategy past
  have hrightControllers :=
    exists_implementable_controller_of_block_realizable_tablesAllowed
      rightPin InitialRightTableLocallyConsistent rightDefault hrightDefault
      (initialRightReceiverStrategy rightLambda)
      (initialRightSenderStrategy rightLambda) hrightWin hrightAllowed
  let rightController := Classical.choose hrightControllers
  have hrightSpec := Classical.choose_spec hrightControllers
  have rightWins := hrightSpec.1
  have rightLocal := hrightSpec.2
  exact {
    leftController := leftController
    leftWins := leftWins
    rightController := rightController
    rightWins := rightWins
    leftLocal := leftLocal
    rightLocal := rightLocal
  }

/-- The finite left controller's blind close output cannot inspect input two. -/
theorem LocallyConsistentInitialControllers.left_reversingOne_independent
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₁ × In₂)) (inputOne : In₁)
    (inputTwo inputTwo' : In₂) :
    (initialLeftLambdaOfPinnedController A strategy controllers.toRootCompatibleInitialControllers).reversingOne
        past (inputOne, inputTwo) =
      (initialLeftLambdaOfPinnedController A strategy controllers.toRootCompatibleInitialControllers).reversingOne
        past (inputOne, inputTwo') := by
  exact controllers.leftLocal (senderWord past)
    (narrowedControl
      ((initialLeftBlockMonitor A).rootPinned
        (fun move => initialLeftLetterAt
          (initialLeftLambdaOfStrategy strategy) [] move))
      controllers.leftController.labeledTree past)
    inputOne inputTwo inputTwo'

/-- The finite right controller's blind close output cannot inspect input one. -/
theorem LocallyConsistentInitialControllers.right_reversingTwo_independent
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : LocallyConsistentInitialControllers A strategy)
    (past : List (In₂ × In₁)) (inputTwo : In₂)
    (inputOne inputOne' : In₁) :
    (initialRightLambdaOfPinnedController A strategy controllers.toRootCompatibleInitialControllers).reversingTwo
        past (inputTwo, inputOne) =
      (initialRightLambdaOfPinnedController A strategy controllers.toRootCompatibleInitialControllers).reversingTwo
        past (inputTwo, inputOne') := by
  exact controllers.rightLocal (senderWord past)
    (narrowedControl
      ((initialRightBlockMonitor A).rootPinned
        (fun move => initialRightLetterAt
          (initialRightLambdaOfStrategy strategy) [] move))
      controllers.rightController.labeledTree past)
    inputTwo inputOne inputOne'

end DetParityAutomaton

end DistributedSynthesis
