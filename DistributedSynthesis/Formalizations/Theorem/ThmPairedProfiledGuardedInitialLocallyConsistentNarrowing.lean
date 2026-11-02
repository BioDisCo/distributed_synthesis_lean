/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedInitialRegularization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialLocalConsistency
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentSenderNarrowing

/-!
# Locally consistent profiled initial controllers

The profiled initial monitor supplies the recurrent entry certificate, but a
distributed implementation also needs two elementary constraints preserved by
regularization: both initial orientations agree with the realizing strategy at
their common root, and the output emitted by a process that does not receive
at a one-sided reversal is independent of the hidden partner input.

This is the profiled analogue of
`ThmPairedGuardedInitialLocallyConsistentNarrowing`.  It uses the same generic
table-law-preserving narrowing theorem; the extra profiled source is carried
by the informed table and is irrelevant to the local no-receive equation.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Local no-receive law for a profiled initial-left table. -/
def ProfiledGuardedInitialLeftTableLocallyConsistent
    (table : In₁ × In₂ → ProfiledGuardedInitialLeftReceiverOutput A) :
    Prop :=
  ∀ inputOne inputTwo inputTwo',
    (table (inputOne, inputTwo)).1.reversingOne =
      (table (inputOne, inputTwo')).1.reversingOne

/-- Process-two mirror. -/
def ProfiledGuardedInitialRightTableLocallyConsistent
    (table : In₂ × In₁ → ProfiledGuardedInitialRightReceiverOutput A) :
    Prop :=
  ∀ inputTwo inputOne inputOne',
    (table (inputTwo, inputOne)).1.reversingTwo =
      (table (inputTwo, inputOne')).1.reversingTwo

theorem profiledGuardedInitialLeftTableLocallyConsistent_strategy
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ target profile,
      (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
    (past : List (In₁ × In₂)) :
    ProfiledGuardedInitialLeftTableLocallyConsistent A
      (profiledGuardedInitialLeftReceiverStrategy A strategy hwin basis past) := by
  simpa [ProfiledGuardedInitialLeftTableLocallyConsistent,
    profiledGuardedInitialLeftReceiverStrategy] using
    (initialLeftTableLocallyConsistent_lambdaOfStrategy strategy past)

theorem profiledGuardedInitialRightTableLocallyConsistent_strategy
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ target profile,
      (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
    (past : List (In₂ × In₁)) :
    ProfiledGuardedInitialRightTableLocallyConsistent A
      (profiledGuardedInitialRightReceiverStrategy A strategy hwin basis past) := by
  simpa [ProfiledGuardedInitialRightTableLocallyConsistent,
    profiledGuardedInitialRightReceiverStrategy] using
    (initialRightTableLocallyConsistent_lambdaOfStrategy strategy past)

/-- Complete profiled record prescribed at the common initial-left root. -/
noncomputable def profiledGuardedInitialLeftExpected
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ target profile,
      (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
    (move : In₁ × In₂) :
    RealizedBlockRound In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) Out₂ :=
  pairPlay (profiledGuardedInitialLeftReceiverStrategy A strategy hwin basis)
    (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
    (fun _ => move) 0

/-- Initial-right mirror. -/
noncomputable def profiledGuardedInitialRightExpected
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ target profile,
      (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
    (move : In₂ × In₁) :
    RealizedBlockRound In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) Out₁ :=
  pairPlay (profiledGuardedInitialRightReceiverStrategy A strategy hwin basis)
    (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
    (fun _ => move) 0

/-- The two profiled initial controllers after simultaneous root pinning and
table-law-preserving narrowing. -/
structure LocallyConsistentProfiledGuardedInitialControllers
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (rightBasis : ∀ target profile,
      (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
    (leftBasis : ∀ target profile,
      (leftProfiledGuardedAutomaton A target profile).RationalRunBasis) where
  leftController : TransitionRationalTree.{v, max u v x y s, max s u v x y} In₂
    (NarrowedBlockLabel In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) Out₂
      ((profiledGuardedInitialLeftBlockMonitor A).rootPinned
        (profiledGuardedInitialLeftExpected A strategy hwin rightBasis)).State)
  leftWins : NarrowedAllThreadsWin
    ((profiledGuardedInitialLeftBlockMonitor A).rootPinned
      (profiledGuardedInitialLeftExpected A strategy hwin rightBasis))
    leftController.labeledTree
  leftLocal : NarrowedTablesAllowed
    ((profiledGuardedInitialLeftBlockMonitor A).rootPinned
      (profiledGuardedInitialLeftExpected A strategy hwin rightBasis))
    (ProfiledGuardedInitialLeftTableLocallyConsistent A)
    leftController.labeledTree
  rightController : TransitionRationalTree.{u, max u v x y s, max s u v x y} In₁
    (NarrowedBlockLabel In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) Out₁
      ((profiledGuardedInitialRightBlockMonitor A).rootPinned
        (profiledGuardedInitialRightExpected A strategy hwin leftBasis)).State)
  rightWins : NarrowedAllThreadsWin
    ((profiledGuardedInitialRightBlockMonitor A).rootPinned
      (profiledGuardedInitialRightExpected A strategy hwin leftBasis))
    rightController.labeledTree
  rightLocal : NarrowedTablesAllowed
    ((profiledGuardedInitialRightBlockMonitor A).rootPinned
      (profiledGuardedInitialRightExpected A strategy hwin leftBasis))
    (ProfiledGuardedInitialRightTableLocallyConsistent A)
    rightController.labeledTree

/-- Winning supplies the complete locally executable profiled initial pair. -/
noncomputable def locallyConsistentProfiledGuardedInitialControllers_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (rightBasis : ∀ target profile,
      (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
    (leftBasis : ∀ target profile,
      (leftProfiledGuardedAutomaton A target profile).RationalRunBasis) :
    LocallyConsistentProfiledGuardedInitialControllers A strategy hwin
      rightBasis leftBasis := by
  classical
  let leftReceiver :=
    profiledGuardedInitialLeftReceiverStrategy A strategy hwin rightBasis
  let leftSender :=
    initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy)
  let leftExpected :=
    profiledGuardedInitialLeftExpected A strategy hwin rightBasis
  let leftPin :=
    (profiledGuardedInitialLeftBlockMonitor A).rootPinned leftExpected
  have hleftBase : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env) :=
    profiledGuardedInitialLeftBlockMonitor_wins A strategy hwin rightBasis
  have hleftRoot : ∀ move : In₁ × In₂,
      pairPlay leftReceiver leftSender (fun _ => move) 0 = leftExpected move :=
    fun _ => rfl
  have hleftWin : ∀ env : Nat → In₁ × In₂,
      leftPin.WinsPlay (pairPlay leftReceiver leftSender env) :=
    (profiledGuardedInitialLeftBlockMonitor A).rootPinned_realizable
      leftExpected leftReceiver leftSender hleftBase hleftRoot
  let leftRootData :=
    (profiledGuardedInitialLeftSource A strategy hwin rightBasis
      [] (default, default)).1
  letI : Inhabited (ProfiledGuardedRightEntryData A) := ⟨leftRootData⟩
  letI : Inhabited (ProfiledGuardedInitialLeftReceiverOutput A) :=
    inferInstance
  let leftDefault : In₁ × In₂ →
      ProfiledGuardedInitialLeftReceiverOutput A := fun _ => default
  have hleftDefault :
      ProfiledGuardedInitialLeftTableLocallyConsistent A leftDefault := by
    intro _ _ _
    rfl
  have hleftAllowed : ∀ past,
      ProfiledGuardedInitialLeftTableLocallyConsistent A
        (leftReceiver past) :=
    profiledGuardedInitialLeftTableLocallyConsistent_strategy A strategy hwin
      rightBasis
  have hleftControllers :=
    exists_implementable_controller_of_block_realizable_tablesAllowed
      leftPin (ProfiledGuardedInitialLeftTableLocallyConsistent A)
      leftDefault hleftDefault leftReceiver leftSender hleftWin hleftAllowed
  let leftController := Classical.choose hleftControllers
  have hleftSpec := Classical.choose_spec hleftControllers

  let rightReceiver :=
    profiledGuardedInitialRightReceiverStrategy A strategy hwin leftBasis
  let rightSender :=
    initialRightSenderStrategy (initialRightLambdaOfStrategy strategy)
  let rightExpected :=
    profiledGuardedInitialRightExpected A strategy hwin leftBasis
  let rightPin :=
    (profiledGuardedInitialRightBlockMonitor A).rootPinned rightExpected
  have hrightBase : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env) :=
    profiledGuardedInitialRightBlockMonitor_wins A strategy hwin leftBasis
  have hrightRoot : ∀ move : In₂ × In₁,
      pairPlay rightReceiver rightSender (fun _ => move) 0 =
        rightExpected move := fun _ => rfl
  have hrightWin : ∀ env : Nat → In₂ × In₁,
      rightPin.WinsPlay (pairPlay rightReceiver rightSender env) :=
    (profiledGuardedInitialRightBlockMonitor A).rootPinned_realizable
      rightExpected rightReceiver rightSender hrightBase hrightRoot
  let rightRootData :=
    (profiledGuardedInitialRightSource A strategy hwin leftBasis
      [] (default, default)).1
  letI : Inhabited (ProfiledGuardedLeftEntryData A) := ⟨rightRootData⟩
  letI : Inhabited (ProfiledGuardedInitialRightReceiverOutput A) :=
    inferInstance
  let rightDefault : In₂ × In₁ →
      ProfiledGuardedInitialRightReceiverOutput A := fun _ => default
  have hrightDefault :
      ProfiledGuardedInitialRightTableLocallyConsistent A rightDefault := by
    intro _ _ _
    rfl
  have hrightAllowed : ∀ past,
      ProfiledGuardedInitialRightTableLocallyConsistent A
        (rightReceiver past) :=
    profiledGuardedInitialRightTableLocallyConsistent_strategy A strategy hwin
      leftBasis
  have hrightControllers :=
    exists_implementable_controller_of_block_realizable_tablesAllowed
      rightPin (ProfiledGuardedInitialRightTableLocallyConsistent A)
      rightDefault hrightDefault rightReceiver rightSender hrightWin
      hrightAllowed
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
    (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentProfiledGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)

noncomputable abbrev profiledGuardedInitialLeftPinnedMonitor :=
  (profiledGuardedInitialLeftBlockMonitor A).rootPinned
    (profiledGuardedInitialLeftExpected A strategy hwin rightBasis)

noncomputable abbrev profiledGuardedInitialRightPinnedMonitor :=
  (profiledGuardedInitialRightBlockMonitor A).rootPinned
    (profiledGuardedInitialRightExpected A strategy hwin leftBasis)

/-- Receiver and sender tables read from the finite guarded initial-left
controller. -/
noncomputable def profiledGuardedInitialLeftReceiverOfController :
    ReceiverBlockStrategy In₁ In₂ (ProfiledGuardedInitialLeftReceiverOutput A) :=
  fun past move =>
    ((controllers.leftController.labeledTree (senderWord past)).2
      (narrowedControl
        (profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
        controllers.leftController.labeledTree past) move)

noncomputable def profiledGuardedInitialLeftSenderOfController :
    SenderBlockStrategy In₂ Out₂ :=
  fun word input => (controllers.leftController.labeledTree word).1 input

noncomputable def profiledGuardedInitialRightReceiverOfController :
    ReceiverBlockStrategy In₂ In₁ (ProfiledGuardedInitialRightReceiverOutput A) :=
  fun past move =>
    ((controllers.rightController.labeledTree (senderWord past)).2
      (narrowedControl
        (profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis)
        controllers.rightController.labeledTree past) move)

noncomputable def profiledGuardedInitialRightSenderOfController :
    SenderBlockStrategy In₁ Out₁ :=
  fun word input => (controllers.rightController.labeledTree word).1 input

theorem profiledGuardedInitialLeftController_reversingOne_independent
    (past : List (In₁ × In₂)) (inputOne : In₁)
    (inputTwo inputTwo' : In₂) :
    (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputOne, inputTwo)).1.reversingOne =
    (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputOne, inputTwo')).1.reversingOne := by
  exact controllers.leftLocal (senderWord past)
    (narrowedControl
      (profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
      controllers.leftController.labeledTree past)
    inputOne inputTwo inputTwo'

theorem profiledGuardedInitialRightController_reversingTwo_independent
    (past : List (In₂ × In₁)) (inputTwo : In₂)
    (inputOne inputOne' : In₁) :
    (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputTwo, inputOne)).1.reversingTwo =
    (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      past (inputTwo, inputOne')).1.reversingTwo := by
  exact controllers.rightLocal (senderWord past)
    (narrowedControl
      (profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis)
      controllers.rightController.labeledTree past)
    inputTwo inputOne inputOne'

/-- Both guarded initial orientations prescribe the same process-one physical
output at the common root. -/
theorem profiledGuardedInitialControllers_root_outputOne
    (move : In₁ × In₂) :
    (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] move).1.informedOne =
    (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] (move.2, move.1)).1.reversingOne := by
  have hleft := (profiledGuardedInitialLeftBlockMonitor A).rootPinned_root_record
    (profiledGuardedInitialLeftExpected A strategy hwin rightBasis)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (profiledGuardedInitialRightBlockMonitor A).rootPinned_root_record
    (profiledGuardedInitialRightExpected A strategy hwin leftBasis)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.1.informedOne) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.1.reversingOne) hright
  rw [show (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] move).1.informedOne =
      (profiledGuardedInitialLeftExpected A strategy hwin rightBasis move).2.1.1.informedOne by
        simpa [profiledGuardedInitialLeftReceiverOfController,
          profiledGuardedInitialLeftPinnedMonitor, narrowedRecord] using hleftOut]
  rw [show (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] (move.2, move.1)).1.reversingOne =
      (profiledGuardedInitialRightExpected A strategy hwin leftBasis
        (move.2, move.1)).2.1.1.reversingOne by
        simpa [profiledGuardedInitialRightReceiverOfController,
          profiledGuardedInitialRightPinnedMonitor, narrowedRecord] using hrightOut]
  rfl

/-- Process-two mirror. -/
theorem profiledGuardedInitialControllers_root_outputTwo
    (move : In₁ × In₂) :
    (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] move).1.reversingTwo =
    (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis controllers
      [] (move.2, move.1)).1.informedTwo := by
  have hleft := (profiledGuardedInitialLeftBlockMonitor A).rootPinned_root_record
    (profiledGuardedInitialLeftExpected A strategy hwin rightBasis)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (profiledGuardedInitialRightBlockMonitor A).rootPinned_root_record
    (profiledGuardedInitialRightExpected A strategy hwin leftBasis)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.1.reversingTwo) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.1.informedTwo) hright
  rw [show (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] move).1.reversingTwo =
      (profiledGuardedInitialLeftExpected A strategy hwin rightBasis move).2.1.1.reversingTwo by
        simpa [profiledGuardedInitialLeftReceiverOfController,
          profiledGuardedInitialLeftPinnedMonitor, narrowedRecord] using hleftOut]
  rw [show (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers [] (move.2, move.1)).1.informedTwo =
      (profiledGuardedInitialRightExpected A strategy hwin leftBasis
        (move.2, move.1)).2.1.1.informedTwo by
        simpa [profiledGuardedInitialRightReceiverOfController,
          profiledGuardedInitialRightPinnedMonitor, narrowedRecord] using hrightOut]
  rfl

theorem profiledGuardedInitialLeft_pairPlay_controller
    (env : Nat -> In₁ × In₂) :
    pairPlay
        (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
          leftBasis controllers)
        (profiledGuardedInitialLeftSenderOfController A strategy hwin rightBasis
          leftBasis controllers) env =
      treePlay
        (narrowedInducedTree
          (profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
          controllers.leftController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    profiledGuardedInitialLeftReceiverOfController,
    profiledGuardedInitialLeftSenderOfController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

theorem profiledGuardedInitialRight_pairPlay_controller
    (env : Nat -> In₂ × In₁) :
    pairPlay
        (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
          leftBasis controllers)
        (profiledGuardedInitialRightSenderOfController A strategy hwin rightBasis
          leftBasis controllers) env =
      treePlay
        (narrowedInducedTree
          (profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis)
          controllers.rightController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    profiledGuardedInitialRightReceiverOfController,
    profiledGuardedInitialRightSenderOfController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

/-- Removing the root-pin wrapper from the selected left controller leaves a
winning guarded initial play. -/
theorem profiledGuardedInitialLeftController_baseWins :
    ∀ env : Nat -> In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay
          (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (profiledGuardedInitialLeftSenderOfController A strategy hwin rightBasis
            leftBasis controllers) env) := by
  intro env
  let pin := profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis
  let word := pairPlay
    (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (profiledGuardedInitialLeftSenderOfController A strategy hwin rightBasis
      leftBasis controllers) env
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.leftWins
  have hpin : pin.WinsPlay word := by
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.leftController.labeledTree)).mp htree env
    dsimp [word]
    rw [profiledGuardedInitialLeft_pairPlay_controller A strategy hwin rightBasis
      leftBasis controllers env]
    exact hplay
  have hrootRecord := (profiledGuardedInitialLeftBlockMonitor A).rootPinned_root_record
    (profiledGuardedInitialLeftExpected A strategy hwin rightBasis)
    controllers.leftController.labeledTree controllers.leftWins (env 0)
  have hwordRoot : word 0 =
      profiledGuardedInitialLeftExpected A strategy hwin rightBasis (word 0).1 := by
    have hplay := congrFun
      (profiledGuardedInitialLeft_pairPlay_controller A strategy hwin rightBasis
        leftBasis controllers env) 0
    dsimp [word]
    rw [hplay]
    simpa [treePlay, branchNode, narrowedInducedTree,
      narrowedControl, narrowedRecord] using hrootRecord
  have hsafe := (profiledGuardedInitialLeftBlockMonitor A).rootPinned_run_safe_of_root_eq
    (profiledGuardedInitialLeftExpected A strategy hwin rightBasis) word hwordRoot
  unfold BlockRecordMonitor.WinsPlay at hpin ⊢
  have heq :
      (fun n => pin.priority (pin.run word n)) =
        fun n => (profiledGuardedInitialLeftBlockMonitor A).priority
          ((profiledGuardedInitialLeftBlockMonitor A).run word n) + 2 := by
    funext n
    change (if (pin.run word n).safe then
      (profiledGuardedInitialLeftBlockMonitor A).priority (pin.run word n).base + 2
      else 1) = _
    rw [hsafe n, if_pos rfl,
      (profiledGuardedInitialLeftBlockMonitor A).rootPinned_run_base
        (profiledGuardedInitialLeftExpected A strategy hwin rightBasis) word n]
  rw [heq] at hpin
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hpin

/-- Right mirror. -/
theorem profiledGuardedInitialRightController_baseWins :
    ∀ env : Nat -> In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay
          (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (profiledGuardedInitialRightSenderOfController A strategy hwin rightBasis
            leftBasis controllers) env) := by
  intro env
  let pin := profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis
  let word := pairPlay
    (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (profiledGuardedInitialRightSenderOfController A strategy hwin rightBasis
      leftBasis controllers) env
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.rightWins
  have hpin : pin.WinsPlay word := by
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.rightController.labeledTree)).mp htree env
    dsimp [word]
    rw [profiledGuardedInitialRight_pairPlay_controller A strategy hwin rightBasis
      leftBasis controllers env]
    exact hplay
  have hrootRecord := (profiledGuardedInitialRightBlockMonitor A).rootPinned_root_record
    (profiledGuardedInitialRightExpected A strategy hwin leftBasis)
    controllers.rightController.labeledTree controllers.rightWins (env 0)
  have hwordRoot : word 0 =
      profiledGuardedInitialRightExpected A strategy hwin leftBasis (word 0).1 := by
    have hplay := congrFun
      (profiledGuardedInitialRight_pairPlay_controller A strategy hwin rightBasis
        leftBasis controllers env) 0
    dsimp [word]
    rw [hplay]
    simpa [treePlay, branchNode, narrowedInducedTree,
      narrowedControl, narrowedRecord] using hrootRecord
  have hsafe := (profiledGuardedInitialRightBlockMonitor A).rootPinned_run_safe_of_root_eq
    (profiledGuardedInitialRightExpected A strategy hwin leftBasis) word hwordRoot
  unfold BlockRecordMonitor.WinsPlay at hpin ⊢
  have heq :
      (fun n => pin.priority (pin.run word n)) =
        fun n => (profiledGuardedInitialRightBlockMonitor A).priority
          ((profiledGuardedInitialRightBlockMonitor A).run word n) + 2 := by
    funext n
    change (if (pin.run word n).safe then
      (profiledGuardedInitialRightBlockMonitor A).priority (pin.run word n).base + 2
      else 1) = _
    rw [hsafe n, if_pos rfl,
      (profiledGuardedInitialRightBlockMonitor A).rootPinned_run_base
        (profiledGuardedInitialRightExpected A strategy hwin leftBasis) word n]
  rw [heq] at hpin
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hpin

end Readback

end DetParityAutomaton

end DistributedSynthesis
