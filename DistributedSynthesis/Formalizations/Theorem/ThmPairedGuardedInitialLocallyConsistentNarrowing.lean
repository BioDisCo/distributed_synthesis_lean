/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedFirstLocalHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialLocalConsistency
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentSenderNarrowing

/-!
# Root-compatible locally consistent guarded initial controllers

The guarded initial controllers must preserve two independent distributed
laws.  Their complete first records are pinned to the same raw-strategy
records, and the output of the process that does not receive at a one-sided
reversal is independent of the hidden current input.  Neither law reveals the
strict leader.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Local no-receive law for a guarded initial-left contingency table.  The
guarded source component is not constrained; it is used by the informed
receiver only. -/
def GuardedInitialLeftTableLocallyConsistent
    (table : In₁ × In₂ -> GuardedInitialLeftReceiverOutput A) : Prop :=
  ∀ inputOne inputTwo inputTwo',
    (table (inputOne, inputTwo)).1.reversingOne =
      (table (inputOne, inputTwo')).1.reversingOne

/-- Process-two mirror. -/
def GuardedInitialRightTableLocallyConsistent
    (table : In₂ × In₁ -> GuardedInitialRightReceiverOutput A) : Prop :=
  ∀ inputTwo inputOne inputOne',
    (table (inputTwo, inputOne)).1.reversingTwo =
      (table (inputTwo, inputOne')).1.reversingTwo

theorem guardedInitialLeftTableLocallyConsistent_strategy
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (guardedBasis : ∀ target profile,
      (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
    (past : List (In₁ × In₂)) :
    GuardedInitialLeftTableLocallyConsistent A
      (guardedInitialLeftReceiverStrategy A strategy hwin guardedBasis past) := by
  simpa [GuardedInitialLeftTableLocallyConsistent,
    guardedInitialLeftReceiverStrategy] using
    (initialLeftTableLocallyConsistent_lambdaOfStrategy strategy past)

theorem guardedInitialRightTableLocallyConsistent_strategy
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (guardedBasis : ∀ target profile,
      (leftProfileGuardedAutomaton A target profile).RationalRunBasis)
    (past : List (In₂ × In₁)) :
    GuardedInitialRightTableLocallyConsistent A
      (guardedInitialRightReceiverStrategy A strategy hwin guardedBasis past) := by
  simpa [GuardedInitialRightTableLocallyConsistent,
    guardedInitialRightReceiverStrategy] using
    (initialRightTableLocallyConsistent_lambdaOfStrategy strategy past)

/-- Complete guarded record prescribed at the common initial root. -/
noncomputable def guardedInitialLeftExpected
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (guardedBasis : ∀ target profile,
      (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
    (move : In₁ × In₂) :
    RealizedBlockRound In₁ In₂ (GuardedInitialLeftReceiverOutput A) Out₂ :=
  pairPlay (guardedInitialLeftReceiverStrategy A strategy hwin guardedBasis)
    (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
    (fun _ => move) 0

noncomputable def guardedInitialRightExpected
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (guardedBasis : ∀ target profile,
      (leftProfileGuardedAutomaton A target profile).RationalRunBasis)
    (move : In₂ × In₁) :
    RealizedBlockRound In₂ In₁ (GuardedInitialRightReceiverOutput A) Out₁ :=
  pairPlay (guardedInitialRightReceiverStrategy A strategy hwin guardedBasis)
    (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
    (fun _ => move) 0

/-- The two initial controllers after simultaneous root pinning and
table-law-preserving narrowing. -/
structure LocallyConsistentGuardedInitialControllers
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (rightBasis : ∀ target profile,
      (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
    (leftBasis : ∀ target profile,
      (leftProfileGuardedAutomaton A target profile).RationalRunBasis) where
  leftController : TransitionRationalTree.{v, max u v x y s, max s u v x} In₂
    (NarrowedBlockLabel In₁ In₂ (GuardedInitialLeftReceiverOutput A) Out₂
      ((guardedInitialLeftBlockMonitor A).rootPinned
        (guardedInitialLeftExpected A strategy hwin rightBasis)).State)
  leftWins : NarrowedAllThreadsWin
    ((guardedInitialLeftBlockMonitor A).rootPinned
      (guardedInitialLeftExpected A strategy hwin rightBasis))
    leftController.labeledTree
  leftLocal : NarrowedTablesAllowed
    ((guardedInitialLeftBlockMonitor A).rootPinned
      (guardedInitialLeftExpected A strategy hwin rightBasis))
    (GuardedInitialLeftTableLocallyConsistent A) leftController.labeledTree
  rightController : TransitionRationalTree.{u, max u v x y s, max s u v y} In₁
    (NarrowedBlockLabel In₂ In₁ (GuardedInitialRightReceiverOutput A) Out₁
      ((guardedInitialRightBlockMonitor A).rootPinned
        (guardedInitialRightExpected A strategy hwin leftBasis)).State)
  rightWins : NarrowedAllThreadsWin
    ((guardedInitialRightBlockMonitor A).rootPinned
      (guardedInitialRightExpected A strategy hwin leftBasis))
    rightController.labeledTree
  rightLocal : NarrowedTablesAllowed
    ((guardedInitialRightBlockMonitor A).rootPinned
      (guardedInitialRightExpected A strategy hwin leftBasis))
    (GuardedInitialRightTableLocallyConsistent A) rightController.labeledTree

/-- Winning yields the complete pair of guarded, root-compatible, locally
consistent finite initial controllers. -/
noncomputable def locallyConsistentGuardedInitialControllers_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (rightBasis : ∀ target profile,
      (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
    (leftBasis : ∀ target profile,
      (leftProfileGuardedAutomaton A target profile).RationalRunBasis) :
    LocallyConsistentGuardedInitialControllers A strategy hwin rightBasis leftBasis := by
  classical
  let leftReceiver := guardedInitialLeftReceiverStrategy A strategy hwin rightBasis
  let leftSender := initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy)
  let leftExpected := guardedInitialLeftExpected A strategy hwin rightBasis
  let leftPin := (guardedInitialLeftBlockMonitor A).rootPinned leftExpected
  have hleftBase : ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env) :=
    guardedInitialLeftBlockMonitor_wins A strategy hwin rightBasis
  have hleftRoot : ∀ move : In₁ × In₂,
      pairPlay leftReceiver leftSender (fun _ => move) 0 = leftExpected move :=
    fun _ => rfl
  have hleftWin : ∀ env : Nat -> In₁ × In₂,
      leftPin.WinsPlay (pairPlay leftReceiver leftSender env) :=
    (guardedInitialLeftBlockMonitor A).rootPinned_realizable
      leftExpected leftReceiver leftSender hleftBase hleftRoot
  let leftRootData := (initialLeftGuardedSource A strategy hwin []
    (default, default) (rightBasis _ _)).1
  letI : Inhabited (GuardedRightEntryData A) := ⟨leftRootData⟩
  letI : Inhabited (GuardedInitialLeftReceiverOutput A) := inferInstance
  let leftDefault : In₁ × In₂ -> GuardedInitialLeftReceiverOutput A :=
    fun _ => default
  have hleftDefault : GuardedInitialLeftTableLocallyConsistent A leftDefault := by
    intro _ _ _
    rfl
  have hleftAllowed : ∀ past,
      GuardedInitialLeftTableLocallyConsistent A (leftReceiver past) :=
    guardedInitialLeftTableLocallyConsistent_strategy A strategy hwin rightBasis
  have hleftControllers :=
    exists_implementable_controller_of_block_realizable_tablesAllowed
      leftPin (GuardedInitialLeftTableLocallyConsistent A)
      leftDefault hleftDefault leftReceiver leftSender hleftWin hleftAllowed
  let leftController := Classical.choose hleftControllers
  have hleftSpec := Classical.choose_spec hleftControllers

  let rightReceiver := guardedInitialRightReceiverStrategy A strategy hwin leftBasis
  let rightSender := initialRightSenderStrategy (initialRightLambdaOfStrategy strategy)
  let rightExpected := guardedInitialRightExpected A strategy hwin leftBasis
  let rightPin := (guardedInitialRightBlockMonitor A).rootPinned rightExpected
  have hrightBase : ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env) :=
    guardedInitialRightBlockMonitor_wins A strategy hwin leftBasis
  have hrightRoot : ∀ move : In₂ × In₁,
      pairPlay rightReceiver rightSender (fun _ => move) 0 = rightExpected move :=
    fun _ => rfl
  have hrightWin : ∀ env : Nat -> In₂ × In₁,
      rightPin.WinsPlay (pairPlay rightReceiver rightSender env) :=
    (guardedInitialRightBlockMonitor A).rootPinned_realizable
      rightExpected rightReceiver rightSender hrightBase hrightRoot
  let rightRootData := (initialRightGuardedSource A strategy hwin []
    (default, default) (leftBasis _ _)).1
  letI : Inhabited (GuardedLeftEntryData A) := ⟨rightRootData⟩
  letI : Inhabited (GuardedInitialRightReceiverOutput A) := inferInstance
  let rightDefault : In₂ × In₁ -> GuardedInitialRightReceiverOutput A :=
    fun _ => default
  have hrightDefault : GuardedInitialRightTableLocallyConsistent A rightDefault := by
    intro _ _ _
    rfl
  have hrightAllowed : ∀ past,
      GuardedInitialRightTableLocallyConsistent A (rightReceiver past) :=
    guardedInitialRightTableLocallyConsistent_strategy A strategy hwin leftBasis
  have hrightControllers :=
    exists_implementable_controller_of_block_realizable_tablesAllowed
      rightPin (GuardedInitialRightTableLocallyConsistent A)
      rightDefault hrightDefault rightReceiver rightSender hrightWin hrightAllowed
  let rightController := Classical.choose hrightControllers
  have hrightSpec := Classical.choose_spec hrightControllers
  exact {
    leftController := leftController
    leftWins := hleftSpec.1
    leftLocal := hleftSpec.2
    rightController := rightController
    rightWins := hrightSpec.1
    rightLocal := hrightSpec.2
  }

section Readback

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfileGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)

noncomputable abbrev guardedInitialLeftPinnedMonitor :=
  (guardedInitialLeftBlockMonitor A).rootPinned
    (guardedInitialLeftExpected A strategy hwin rightBasis)

noncomputable abbrev guardedInitialRightPinnedMonitor :=
  (guardedInitialRightBlockMonitor A).rootPinned
    (guardedInitialRightExpected A strategy hwin leftBasis)

/-- Receiver and sender tables read from the finite guarded initial-left
controller. -/
noncomputable def guardedInitialLeftReceiverOfController :
    ReceiverBlockStrategy In₁ In₂ (GuardedInitialLeftReceiverOutput A) :=
  fun past move =>
    ((controllers.leftController.labeledTree (senderWord past)).2
      (narrowedControl
        (guardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
        controllers.leftController.labeledTree past) move)

noncomputable def guardedInitialLeftSenderOfController :
    SenderBlockStrategy In₂ Out₂ :=
  fun word input => (controllers.leftController.labeledTree word).1 input

noncomputable def guardedInitialRightReceiverOfController :
    ReceiverBlockStrategy In₂ In₁ (GuardedInitialRightReceiverOutput A) :=
  fun past move =>
    ((controllers.rightController.labeledTree (senderWord past)).2
      (narrowedControl
        (guardedInitialRightPinnedMonitor A strategy hwin leftBasis)
        controllers.rightController.labeledTree past) move)

noncomputable def guardedInitialRightSenderOfController :
    SenderBlockStrategy In₁ Out₁ :=
  fun word input => (controllers.rightController.labeledTree word).1 input

theorem guardedInitialLeftController_reversingOne_independent
    (past : List (In₁ × In₂)) (inputOne : In₁)
    (inputTwo inputTwo' : In₂) :
    (guardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputOne, inputTwo)).1.reversingOne =
    (guardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputOne, inputTwo')).1.reversingOne := by
  exact controllers.leftLocal (senderWord past)
    (narrowedControl
      (guardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
      controllers.leftController.labeledTree past)
    inputOne inputTwo inputTwo'

theorem guardedInitialRightController_reversingTwo_independent
    (past : List (In₂ × In₁)) (inputTwo : In₂)
    (inputOne inputOne' : In₁) :
    (guardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputTwo, inputOne)).1.reversingTwo =
    (guardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputTwo, inputOne')).1.reversingTwo := by
  exact controllers.rightLocal (senderWord past)
    (narrowedControl
      (guardedInitialRightPinnedMonitor A strategy hwin leftBasis)
      controllers.rightController.labeledTree past)
    inputTwo inputOne inputOne'

/-- Both guarded initial orientations prescribe the same process-one physical
output at the common root. -/
theorem guardedInitialControllers_root_outputOne
    (move : In₁ × In₂) :
    (guardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] move).1.informedOne =
    (guardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] (move.2, move.1)).1.reversingOne := by
  have hleft := (guardedInitialLeftBlockMonitor A).rootPinned_root_record
    (guardedInitialLeftExpected A strategy hwin rightBasis)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (guardedInitialRightBlockMonitor A).rootPinned_root_record
    (guardedInitialRightExpected A strategy hwin leftBasis)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.1.informedOne) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.1.reversingOne) hright
  rw [show (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] move).1.informedOne =
      (guardedInitialLeftExpected A strategy hwin rightBasis move).2.1.1.informedOne by
        simpa [guardedInitialLeftReceiverOfController,
          guardedInitialLeftPinnedMonitor, narrowedRecord] using hleftOut]
  rw [show (guardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] (move.2, move.1)).1.reversingOne =
      (guardedInitialRightExpected A strategy hwin leftBasis
        (move.2, move.1)).2.1.1.reversingOne by
        simpa [guardedInitialRightReceiverOfController,
          guardedInitialRightPinnedMonitor, narrowedRecord] using hrightOut]
  rfl

/-- Process-two mirror. -/
theorem guardedInitialControllers_root_outputTwo
    (move : In₁ × In₂) :
    (guardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] move).1.reversingTwo =
    (guardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] (move.2, move.1)).1.informedTwo := by
  have hleft := (guardedInitialLeftBlockMonitor A).rootPinned_root_record
    (guardedInitialLeftExpected A strategy hwin rightBasis)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (guardedInitialRightBlockMonitor A).rootPinned_root_record
    (guardedInitialRightExpected A strategy hwin leftBasis)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.1.reversingTwo) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.1.informedTwo) hright
  rw [show (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] move).1.reversingTwo =
      (guardedInitialLeftExpected A strategy hwin rightBasis move).2.1.1.reversingTwo by
        simpa [guardedInitialLeftReceiverOfController,
          guardedInitialLeftPinnedMonitor, narrowedRecord] using hleftOut]
  rw [show (guardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] (move.2, move.1)).1.informedTwo =
      (guardedInitialRightExpected A strategy hwin leftBasis
        (move.2, move.1)).2.1.1.informedTwo by
        simpa [guardedInitialRightReceiverOfController,
          guardedInitialRightPinnedMonitor, narrowedRecord] using hrightOut]
  rfl

theorem guardedInitialLeft_pairPlay_controller
    (env : Nat -> In₁ × In₂) :
    pairPlay
        (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
          leftBasis controllers)
        (guardedInitialLeftSenderOfController A strategy hwin rightBasis
          leftBasis controllers) env =
      treePlay
        (narrowedInducedTree
          (guardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
          controllers.leftController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    guardedInitialLeftReceiverOfController,
    guardedInitialLeftSenderOfController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

theorem guardedInitialRight_pairPlay_controller
    (env : Nat -> In₂ × In₁) :
    pairPlay
        (guardedInitialRightReceiverOfController A strategy hwin rightBasis
          leftBasis controllers)
        (guardedInitialRightSenderOfController A strategy hwin rightBasis
          leftBasis controllers) env =
      treePlay
        (narrowedInducedTree
          (guardedInitialRightPinnedMonitor A strategy hwin leftBasis)
          controllers.rightController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    guardedInitialRightReceiverOfController,
    guardedInitialRightSenderOfController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

/-- Removing the root-pin wrapper from the selected left controller leaves a
winning guarded initial play. -/
theorem guardedInitialLeftController_baseWins :
    ∀ env : Nat -> In₁ × In₂,
      (guardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay
          (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (guardedInitialLeftSenderOfController A strategy hwin rightBasis
            leftBasis controllers) env) := by
  intro env
  let pin := guardedInitialLeftPinnedMonitor A strategy hwin rightBasis
  let word := pairPlay
    (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (guardedInitialLeftSenderOfController A strategy hwin rightBasis
      leftBasis controllers) env
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.leftWins
  have hpin : pin.WinsPlay word := by
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.leftController.labeledTree)).mp htree env
    dsimp [word]
    rw [guardedInitialLeft_pairPlay_controller A strategy hwin rightBasis
      leftBasis controllers env]
    exact hplay
  have hrootRecord := (guardedInitialLeftBlockMonitor A).rootPinned_root_record
    (guardedInitialLeftExpected A strategy hwin rightBasis)
    controllers.leftController.labeledTree controllers.leftWins (env 0)
  have hwordRoot : word 0 =
      guardedInitialLeftExpected A strategy hwin rightBasis (word 0).1 := by
    have hplay := congrFun
      (guardedInitialLeft_pairPlay_controller A strategy hwin rightBasis
        leftBasis controllers env) 0
    dsimp [word]
    rw [hplay]
    simpa [treePlay, branchNode, narrowedInducedTree,
      narrowedControl, narrowedRecord] using hrootRecord
  have hsafe := (guardedInitialLeftBlockMonitor A).rootPinned_run_safe_of_root_eq
    (guardedInitialLeftExpected A strategy hwin rightBasis) word hwordRoot
  unfold BlockRecordMonitor.WinsPlay at hpin ⊢
  have heq :
      (fun n => pin.priority (pin.run word n)) =
        fun n => (guardedInitialLeftBlockMonitor A).priority
          ((guardedInitialLeftBlockMonitor A).run word n) + 2 := by
    funext n
    change (if (pin.run word n).safe then
      (guardedInitialLeftBlockMonitor A).priority (pin.run word n).base + 2
      else 1) = _
    rw [hsafe n, if_pos rfl,
      (guardedInitialLeftBlockMonitor A).rootPinned_run_base
        (guardedInitialLeftExpected A strategy hwin rightBasis) word n]
  rw [heq] at hpin
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hpin

/-- Right mirror. -/
theorem guardedInitialRightController_baseWins :
    ∀ env : Nat -> In₂ × In₁,
      (guardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay
          (guardedInitialRightReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (guardedInitialRightSenderOfController A strategy hwin rightBasis
            leftBasis controllers) env) := by
  intro env
  let pin := guardedInitialRightPinnedMonitor A strategy hwin leftBasis
  let word := pairPlay
    (guardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (guardedInitialRightSenderOfController A strategy hwin rightBasis
      leftBasis controllers) env
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.rightWins
  have hpin : pin.WinsPlay word := by
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.rightController.labeledTree)).mp htree env
    dsimp [word]
    rw [guardedInitialRight_pairPlay_controller A strategy hwin rightBasis
      leftBasis controllers env]
    exact hplay
  have hrootRecord := (guardedInitialRightBlockMonitor A).rootPinned_root_record
    (guardedInitialRightExpected A strategy hwin leftBasis)
    controllers.rightController.labeledTree controllers.rightWins (env 0)
  have hwordRoot : word 0 =
      guardedInitialRightExpected A strategy hwin leftBasis (word 0).1 := by
    have hplay := congrFun
      (guardedInitialRight_pairPlay_controller A strategy hwin rightBasis
        leftBasis controllers env) 0
    dsimp [word]
    rw [hplay]
    simpa [treePlay, branchNode, narrowedInducedTree,
      narrowedControl, narrowedRecord] using hrootRecord
  have hsafe := (guardedInitialRightBlockMonitor A).rootPinned_run_safe_of_root_eq
    (guardedInitialRightExpected A strategy hwin leftBasis) word hwordRoot
  unfold BlockRecordMonitor.WinsPlay at hpin ⊢
  have heq :
      (fun n => pin.priority (pin.run word n)) =
        fun n => (guardedInitialRightBlockMonitor A).priority
          ((guardedInitialRightBlockMonitor A).run word n) + 2 := by
    funext n
    change (if (pin.run word n).safe then
      (guardedInitialRightBlockMonitor A).priority (pin.run word n).base + 2
      else 1) = _
    rw [hsafe n, if_pos rfl,
      (guardedInitialRightBlockMonitor A).rootPinned_run_base
        (guardedInitialRightExpected A strategy hwin leftBasis) word n]
  rw [heq] at hpin
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hpin

/-- Concrete finite key emitted by the selected guarded initial-left
controller at any boundary. -/
noncomputable def guardedInitialLeftController_firstMacroAt
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    GuardedFirstRightMacro A :=
  guardedInitialLeftFirstMacroAt A
    (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (guardedInitialLeftSenderOfController A strategy hwin rightBasis
      leftBasis controllers)
    (guardedInitialLeftController_baseWins A strategy hwin rightBasis
      leftBasis controllers) past move

/-- Right mirror. -/
noncomputable def guardedInitialRightController_firstMacroAt
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    GuardedFirstLeftMacro A :=
  guardedInitialRightFirstMacroAt A
    (guardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (guardedInitialRightSenderOfController A strategy hwin rightBasis
      leftBasis controllers)
    (guardedInitialRightController_baseWins A strategy hwin rightBasis
      leftBasis controllers) past move

end Readback

end DetParityAutomaton

end DistributedSynthesis
