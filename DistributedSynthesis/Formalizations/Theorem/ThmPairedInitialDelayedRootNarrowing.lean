/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialDelayedRegularization
import DistributedSynthesis.Formalizations.Theorem.ThmRootPinnedBlockNarrowing

/-!
# Root-compatible delay-one initial controllers

This is the final initial-controller extraction used by the delayed route.  It
combines the corrected staged-entry monitors with the finite root pin.  The
pin shares the first `both` outputs; it is not a leader observation.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Independently finite initial controllers using the correct delay-one
monitor, pinned to the same raw-strategy root record. -/
structure DelayedRootCompatibleInitialControllers
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  leftController : TransitionRationalTree.{v, max u v x y s, s} In₂
    (NarrowedBlockLabel In₁ In₂
      (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
      ((initialLeftDelayedBlockMonitor A).rootPinned
        (fun move => initialLeftLetterAt
          (initialLeftLambdaOfStrategy strategy) [] move)).State)
  leftWins : NarrowedAllThreadsWin
    ((initialLeftDelayedBlockMonitor A).rootPinned
      (fun move => initialLeftLetterAt
        (initialLeftLambdaOfStrategy strategy) [] move))
    leftController.labeledTree
  rightController : TransitionRationalTree.{u, max u v x y s, s} In₁
    (NarrowedBlockLabel In₂ In₁
      (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
      ((initialRightDelayedBlockMonitor A).rootPinned
        (fun move => initialRightLetterAt
          (initialRightLambdaOfStrategy strategy) [] move)).State)
  rightWins : NarrowedAllThreadsWin
    ((initialRightDelayedBlockMonitor A).rootPinned
      (fun move => initialRightLetterAt
        (initialRightLambdaOfStrategy strategy) [] move))
    rightController.labeledTree

/-- Winning yields corrected finite, root-compatible initial controllers. -/
noncomputable def delayedRootCompatibleInitialControllers_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    DelayedRootCompatibleInitialControllers A strategy := by
  classical
  let leftLambda := initialLeftLambdaOfStrategy strategy
  let leftExpected := fun move => initialLeftLetterAt leftLambda [] move
  have hleftBase : ∀ env : Nat -> In₁ × In₂,
      (initialLeftDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy leftLambda)
          (initialLeftSenderStrategy leftLambda) env) :=
    initialLeftDelayedBlockMonitor_realizable A leftLambda
      (initialLeftForeverAccepts_lambdaOfStrategy A strategy hwin)
      (initialLeftDelayedFeasible_lambdaOfStrategy A strategy hwin basis)
  have hleftRoot : ∀ move : In₁ × In₂,
      pairPlay (initialLeftReceiverStrategy leftLambda)
          (initialLeftSenderStrategy leftLambda) (fun _ => move) 0 =
        leftExpected move := by
    intro move
    simpa [leftExpected, leftLambda] using
      initialLeft_pairPlay_eq_letterAt leftLambda (fun _ => move) 0
  have hleftRealizable :
      ∃ receiver : ReceiverBlockStrategy In₁ In₂
          (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)),
        ∃ sender : SenderBlockStrategy In₂ Out₂,
          ∀ env : Nat -> In₁ × In₂,
            ((initialLeftDelayedBlockMonitor A).rootPinned leftExpected).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨initialLeftReceiverStrategy leftLambda,
      initialLeftSenderStrategy leftLambda,
      (initialLeftDelayedBlockMonitor A).rootPinned_realizable leftExpected
        _ _ hleftBase hleftRoot⟩
  have hleftControllers :=
    (block_realizable_iff_implementable_controller_unconditional
      ((initialLeftDelayedBlockMonitor A).rootPinned leftExpected)).mp
        hleftRealizable
  let leftController := Classical.choose hleftControllers
  have leftWins := Classical.choose_spec hleftControllers

  let rightLambda := initialRightLambdaOfStrategy strategy
  let rightExpected := fun move => initialRightLetterAt rightLambda [] move
  have hrightBase : ∀ env : Nat -> In₂ × In₁,
      (initialRightDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy rightLambda)
          (initialRightSenderStrategy rightLambda) env) :=
    initialRightDelayedBlockMonitor_realizable A rightLambda
      (initialRightForeverAccepts_lambdaOfStrategy A strategy hwin)
      (initialRightDelayedFeasible_lambdaOfStrategy A strategy hwin basis)
  have hrightRoot : ∀ move : In₂ × In₁,
      pairPlay (initialRightReceiverStrategy rightLambda)
          (initialRightSenderStrategy rightLambda) (fun _ => move) 0 =
        rightExpected move := by
    intro move
    simpa [rightExpected, rightLambda] using
      initialRight_pairPlay_eq_letterAt rightLambda (fun _ => move) 0
  have hrightRealizable :
      ∃ receiver : ReceiverBlockStrategy In₂ In₁
          (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)),
        ∃ sender : SenderBlockStrategy In₁ Out₁,
          ∀ env : Nat -> In₂ × In₁,
            ((initialRightDelayedBlockMonitor A).rootPinned rightExpected).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨initialRightReceiverStrategy rightLambda,
      initialRightSenderStrategy rightLambda,
      (initialRightDelayedBlockMonitor A).rootPinned_realizable rightExpected
        _ _ hrightBase hrightRoot⟩
  have hrightControllers :=
    (block_realizable_iff_implementable_controller_unconditional
      ((initialRightDelayedBlockMonitor A).rootPinned rightExpected)).mp
        hrightRealizable
  let rightController := Classical.choose hrightControllers
  have rightWins := Classical.choose_spec hrightControllers
  exact ⟨leftController, leftWins, rightController, rightWins⟩

/-- The corrected pinned roots prescribe the same process-one output on the
initial `left`/`both` ambiguity. -/
theorem delayedRootCompatible_initial_outputOne
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy)
    (move : In₁ × In₂) :
    ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftDelayedBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).informedOne =
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightDelayedBlockMonitor A).rootPinned
          (fun move => initialRightLetterAt
            (initialRightLambdaOfStrategy strategy) [] move)).initial
        (move.2, move.1)).reversingOne := by
  have hleft := (initialLeftDelayedBlockMonitor A).rootPinned_root_record
    (fun move => initialLeftLetterAt
      (initialLeftLambdaOfStrategy strategy) [] move)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (initialRightDelayedBlockMonitor A).rootPinned_root_record
    (fun move => initialRightLetterAt
      (initialRightLambdaOfStrategy strategy) [] move)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.informedOne) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.reversingOne) hright
  have hleftOut' :
      ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftDelayedBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).informedOne =
        (initialLeftLetterAt
          (initialLeftLambdaOfStrategy strategy) [] move).2.1.informedOne := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hleftOut
  have hrightOut' :
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightDelayedBlockMonitor A).rootPinned
          (fun move => initialRightLetterAt
            (initialRightLambdaOfStrategy strategy) [] move)).initial
          (move.2, move.1)).reversingOne =
        (initialRightLetterAt
          (initialRightLambdaOfStrategy strategy) []
            (move.2, move.1)).2.1.reversingOne := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hrightOut
  rw [hleftOut', hrightOut']
  rfl

/-- Process-two root compatibility. -/
theorem delayedRootCompatible_initial_outputTwo
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy)
    (move : In₁ × In₂) :
    ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftDelayedBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).reversingTwo =
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightDelayedBlockMonitor A).rootPinned
          (fun move => initialRightLetterAt
            (initialRightLambdaOfStrategy strategy) [] move)).initial
        (move.2, move.1)).informedTwo := by
  have hleft := (initialLeftDelayedBlockMonitor A).rootPinned_root_record
    (fun move => initialLeftLetterAt
      (initialLeftLambdaOfStrategy strategy) [] move)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (initialRightDelayedBlockMonitor A).rootPinned_root_record
    (fun move => initialRightLetterAt
      (initialRightLambdaOfStrategy strategy) [] move)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.reversingTwo) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.informedTwo) hright
  have hleftOut' :
      ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftDelayedBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).reversingTwo =
        (initialLeftLetterAt
          (initialLeftLambdaOfStrategy strategy) [] move).2.1.reversingTwo := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hleftOut
  have hrightOut' :
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightDelayedBlockMonitor A).rootPinned
          (fun move => initialRightLetterAt
            (initialRightLambdaOfStrategy strategy) [] move)).initial
          (move.2, move.1)).informedTwo =
        (initialRightLetterAt
          (initialRightLambdaOfStrategy strategy) []
            (move.2, move.1)).2.1.informedTwo := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hrightOut
  rw [hleftOut', hrightOut']
  rfl

end DetParityAutomaton

end DistributedSynthesis
