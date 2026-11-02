/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialDelayedRootNarrowing
import DistributedSynthesis.Formalizations.Theorem.ThmPairedDelayedSwitchFactor

/-!
# Semantic readback of the delay-one initial controllers

The finite root-compatible controllers are read back as local lambdas.  Their
winning condition implies both ordinary initial-block acceptance and
feasibility of every target staged one round before a switch.  The resulting
feasibility proof feeds the paired-bank handoff directly; it is not an oracle
and it does not use a strict-leader predicate.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Initial-left lambda read from the finite delayed controller. -/
noncomputable def initialLeftLambdaOfDelayedPinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy) :
    InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := (initialLeftDelayedBlockMonitor A).rootPinned
    (fun move => initialLeftLetterAt
      (initialLeftLambdaOfStrategy strategy) [] move)
  let narrowed := controllers.leftController.labeledTree
  {
    blindTwo := fun word input => (narrowed word).1 input
    informedOne := fun past move =>
      ((narrowed (senderWord past)).2
        (narrowedControl monitor narrowed past) move).informedOne
    reversingOne := fun past move =>
      ((narrowed (senderWord past)).2
        (narrowedControl monitor narrowed past) move).reversingOne
    reversingTwo := fun past move =>
      ((narrowed (senderWord past)).2
        (narrowedControl monitor narrowed past) move).reversingTwo
  }

/-- Initial-right mirror. -/
noncomputable def initialRightLambdaOfDelayedPinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy) :
    InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := (initialRightDelayedBlockMonitor A).rootPinned
    (fun move => initialRightLetterAt
      (initialRightLambdaOfStrategy strategy) [] move)
  let narrowed := controllers.rightController.labeledTree
  {
    blindOne := fun word input => (narrowed word).1 input
    informedTwo := fun past move =>
      ((narrowed (senderWord past)).2
        (narrowedControl monitor narrowed past) move).informedTwo
    reversingOne := fun past move =>
      ((narrowed (senderWord past)).2
        (narrowedControl monitor narrowed past) move).reversingOne
    reversingTwo := fun past move =>
      ((narrowed (senderWord past)).2
        (narrowedControl monitor narrowed past) move).reversingTwo
  }

theorem initialLeft_pairPlay_delayedPinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy)
    (env : Nat -> In₁ × In₂) :
    pairPlay
        (initialLeftReceiverStrategy
          (initialLeftLambdaOfDelayedPinnedController A strategy controllers))
        (initialLeftSenderStrategy
          (initialLeftLambdaOfDelayedPinnedController A strategy controllers)) env =
      treePlay
        (narrowedInducedTree
          ((initialLeftDelayedBlockMonitor A).rootPinned
            (fun move => initialLeftLetterAt
              (initialLeftLambdaOfStrategy strategy) [] move))
          controllers.leftController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    initialLeftReceiverStrategy, initialLeftSenderStrategy,
    initialLeftLambdaOfDelayedPinnedController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

theorem initialRight_pairPlay_delayedPinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy)
    (env : Nat -> In₂ × In₁) :
    pairPlay
        (initialRightReceiverStrategy
          (initialRightLambdaOfDelayedPinnedController A strategy controllers))
        (initialRightSenderStrategy
          (initialRightLambdaOfDelayedPinnedController A strategy controllers)) env =
      treePlay
        (narrowedInducedTree
          ((initialRightDelayedBlockMonitor A).rootPinned
            (fun move => initialRightLetterAt
              (initialRightLambdaOfStrategy strategy) [] move))
          controllers.rightController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    initialRightReceiverStrategy, initialRightSenderStrategy,
    initialRightLambdaOfDelayedPinnedController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

/-- The finite delayed left controller retains both semantic obligations. -/
theorem DelayedRootCompatibleInitialControllers.left_sound
    [Inhabited In₁] [Inhabited In₂] [Inhabited (In₁ × In₂)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy) :
    let lambda := initialLeftLambdaOfDelayedPinnedController A strategy controllers
    InitialLeftForeverAccepts A lambda ∧ InitialLeftDelayedFeasible A lambda := by
  let expected := fun move => initialLeftLetterAt
    (initialLeftLambdaOfStrategy strategy) [] move
  let pin := (initialLeftDelayedBlockMonitor A).rootPinned expected
  let lambda := initialLeftLambdaOfDelayedPinnedController A strategy controllers
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.leftWins
  have hpin : ∀ env : Nat -> In₁ × In₂,
      pin.WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) := by
    intro env
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.leftController.labeledTree)).mp htree env
    rw [initialLeft_pairPlay_delayedPinnedController A strategy controllers env]
    exact hplay
  have hbase : ∀ env : Nat -> In₁ × In₂,
      (initialLeftDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) := by
    intro env
    let word := pairPlay (initialLeftReceiverStrategy lambda)
      (initialLeftSenderStrategy lambda) env
    have hrootRecord := (initialLeftDelayedBlockMonitor A).rootPinned_root_record
      expected controllers.leftController.labeledTree controllers.leftWins (env 0)
    have hwordRoot : word 0 = expected (word 0).1 := by
      have hplay := congrFun
        (initialLeft_pairPlay_delayedPinnedController A strategy controllers env) 0
      change pairPlay (initialLeftReceiverStrategy lambda)
        (initialLeftSenderStrategy lambda) env 0 =
          expected (pairPlay (initialLeftReceiverStrategy lambda)
            (initialLeftSenderStrategy lambda) env 0).1
      rw [hplay]
      simpa [treePlay, branchNode, narrowedInducedTree,
        narrowedControl, narrowedRecord] using hrootRecord
    have hsafe := (initialLeftDelayedBlockMonitor A).rootPinned_run_safe_of_root_eq
      expected word hwordRoot
    have hp := hpin env
    unfold BlockRecordMonitor.WinsPlay at hp ⊢
    have heq :
        (fun n => pin.priority (pin.run word n)) =
          fun n => (initialLeftDelayedBlockMonitor A).priority
            ((initialLeftDelayedBlockMonitor A).run word n) + 2 := by
      funext n
      change (if (pin.run word n).safe then
          (initialLeftDelayedBlockMonitor A).priority (pin.run word n).base + 2 else 1) = _
      rw [hsafe n, if_pos rfl,
        (initialLeftDelayedBlockMonitor A).rootPinned_run_base expected word n]
    rw [heq] at hp
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hp
  exact initialLeftDelayed_conditions_of_monitorWins A lambda hbase

/-- Mirror semantic guarantee. -/
theorem DelayedRootCompatibleInitialControllers.right_sound
    [Inhabited In₁] [Inhabited In₂] [Inhabited (In₂ × In₁)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : DelayedRootCompatibleInitialControllers A strategy) :
    let lambda := initialRightLambdaOfDelayedPinnedController A strategy controllers
    InitialRightForeverAccepts A lambda ∧ InitialRightDelayedFeasible A lambda := by
  let expected := fun move => initialRightLetterAt
    (initialRightLambdaOfStrategy strategy) [] move
  let pin := (initialRightDelayedBlockMonitor A).rootPinned expected
  let lambda := initialRightLambdaOfDelayedPinnedController A strategy controllers
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.rightWins
  have hpin : ∀ env : Nat -> In₂ × In₁,
      pin.WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) := by
    intro env
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.rightController.labeledTree)).mp htree env
    rw [initialRight_pairPlay_delayedPinnedController A strategy controllers env]
    exact hplay
  have hbase : ∀ env : Nat -> In₂ × In₁,
      (initialRightDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) := by
    intro env
    let word := pairPlay (initialRightReceiverStrategy lambda)
      (initialRightSenderStrategy lambda) env
    have hrootRecord := (initialRightDelayedBlockMonitor A).rootPinned_root_record
      expected controllers.rightController.labeledTree controllers.rightWins (env 0)
    have hwordRoot : word 0 = expected (word 0).1 := by
      have hplay := congrFun
        (initialRight_pairPlay_delayedPinnedController A strategy controllers env) 0
      change pairPlay (initialRightReceiverStrategy lambda)
        (initialRightSenderStrategy lambda) env 0 =
          expected (pairPlay (initialRightReceiverStrategy lambda)
            (initialRightSenderStrategy lambda) env 0).1
      rw [hplay]
      simpa [treePlay, branchNode, narrowedInducedTree,
        narrowedControl, narrowedRecord] using hrootRecord
    have hsafe := (initialRightDelayedBlockMonitor A).rootPinned_run_safe_of_root_eq
      expected word hwordRoot
    have hp := hpin env
    unfold BlockRecordMonitor.WinsPlay at hp ⊢
    have heq :
        (fun n => pin.priority (pin.run word n)) =
          fun n => (initialRightDelayedBlockMonitor A).priority
            ((initialRightDelayedBlockMonitor A).run word n) + 2 := by
      funext n
      change (if (pin.run word n).safe then
          (initialRightDelayedBlockMonitor A).priority (pin.run word n).base + 2 else 1) = _
      rw [hsafe n, if_pos rfl,
        (initialRightDelayedBlockMonitor A).rootPinned_run_base expected word n]
    rw [heq] at hp
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hp
  exact initialRightDelayed_conditions_of_monitorWins A lambda hbase

end DetParityAutomaton

end DistributedSynthesis
