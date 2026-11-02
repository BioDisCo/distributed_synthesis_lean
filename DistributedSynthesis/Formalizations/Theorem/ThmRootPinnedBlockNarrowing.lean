/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialBlockFromWinning

/-!
# Root-pinned block narrowing

Independent rationalization of two initial block trees must preserve their
common `both`-round outputs.  This reusable wrapper pins the complete first
letter of a block monitor to a prescribed local lambda, while leaving every
later round governed by the original monitor.  The pin is a finite safety
condition and therefore survives unconditional sender narrowing.
-/

namespace DistributedSynthesis

universe u v x y w

namespace BlockRecordMonitor

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

structure RootPinnedState where
  base : M.State
  first : Bool
  safe : Bool

noncomputable instance : Fintype (RootPinnedState M) := by
  classical
  exact Fintype.ofEquiv (M.State × Bool × Bool) {
    toFun := fun state => ⟨state.1, state.2.1, state.2.2⟩
    invFun := fun state => (state.base, state.first, state.safe)
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; cases state; rfl
  }

/-- Add a sticky first-letter equality test to any block monitor. -/
noncomputable def rootPinned
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut) :
    BlockRecordMonitor RIn SIn ROut SOut := by
  classical
  set_option synthInstance.maxHeartbeats 200000 in
    exact {
      State := RootPinnedState M
      stateFinite := inferInstance
      initial := ⟨M.initial, true, true⟩
      step := fun state letter =>
        ⟨M.step state.base letter, false,
          Bool.and state.safe
            (Bool.or (!state.first) (decide (letter = expected letter.1)))⟩
      priority := fun state => if state.safe then M.priority state.base + 2 else 1
    }

@[simp] theorem rootPinned_initial
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut) :
    (M.rootPinned expected).initial = ⟨M.initial, true, true⟩ := rfl

@[simp] theorem rootPinned_step_base
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (state : RootPinnedState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut) :
    ((M.rootPinned expected).step state letter).base =
      M.step state.base letter := rfl

@[simp] theorem rootPinned_step_first
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (state : RootPinnedState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut) :
    ((M.rootPinned expected).step state letter).first = false := rfl

theorem rootPinned_run_base
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut)) : ∀ n,
    ((M.rootPinned expected).run word n).base = M.run word n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, BlockRecordMonitor.run]
      exact congrArg (fun state => M.step state (word n)) ih

theorem rootPinned_run_first_succ
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut)) (n : Nat) :
    ((M.rootPinned expected).run word (n + 1)).first = false := by
  rw [BlockRecordMonitor.run]
  rfl

/-- Once the pin fails, it remains failed forever. -/
theorem rootPinned_safe_false_persists
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (n : Nat)
    (hfalse : ((M.rootPinned expected).run word n).safe = false) :
    ∀ k, ((M.rootPinned expected).run word (n + k)).safe = false := by
  classical
  intro k
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      change
        Bool.and ((M.rootPinned expected).run word (n + k)).safe
          (Bool.or (!((M.rootPinned expected).run word (n + k)).first)
            (decide (word (n + k) = expected (word (n + k)).1))) = false
      rw [ih]
      rfl

/-- If the first letter is the prescribed one, the safety bit stays true. -/
theorem rootPinned_run_safe_of_root_eq
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hroot : word 0 = expected (word 0).1) : ∀ n,
    ((M.rootPinned expected).run word n).safe = true := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      cases n with
      | zero =>
          change Bool.and true
            (Bool.or (!true) (decide (word 0 = expected (word 0).1))) = true
          have hd : decide (word 0 = expected (word 0).1) = true :=
            decide_eq_true hroot
          rw [hd]
          rfl
      | succ n =>
          change
            Bool.and ((M.rootPinned expected).run word (n + 1)).safe
              (Bool.or (!((M.rootPinned expected).run word (n + 1)).first)
                (decide (word (n + 1) = expected (word (n + 1)).1))) = true
          rw [rootPinned_run_first_succ M expected word n]
          simp [ih]

/-- Winning the pinned monitor forces the sticky pin to remain safe. -/
theorem rootPinned_safe_of_wins
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hwins : (M.rootPinned expected).WinsPlay word) (n : Nat) :
    ((M.rootPinned expected).run word n).safe = true := by
  by_contra hnot
  have hfalse : ((M.rootPinned expected).run word n).safe = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist := M.rootPinned_safe_false_persists expected word n hfalse
  have heventual : ∀ k, n ≤ k ->
      (M.rootPinned expected).priority
        ((M.rootPinned expected).run word k) = 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    change (if ((M.rootPinned expected).run word (n + j)).safe
      then _ else 1) = 1
    rw [hpersist j]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwins

/-- Forgetting the finite root pin preserves winning of the underlying block
monitor. -/
theorem rootPinned_base_wins_of_wins
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hwins : (M.rootPinned expected).WinsPlay word) :
    M.WinsPlay word := by
  unfold BlockRecordMonitor.WinsPlay at hwins ⊢
  have heq :
      (fun n => (M.rootPinned expected).priority
        ((M.rootPinned expected).run word n)) =
        fun n => M.priority (M.run word n) + 2 := by
    funext n
    change (if ((M.rootPinned expected).run word n).safe
      then M.priority ((M.rootPinned expected).run word n).base + 2
      else 1) = M.priority (M.run word n) + 2
    rw [M.rootPinned_safe_of_wins expected word hwins n, if_pos rfl,
      M.rootPinned_run_base expected word n]
  rw [heq] at hwins
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwins

/-- A base-winning local pair whose first letter is pinned realizes the
wrapped monitor. -/
theorem rootPinned_realizable
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ env : Nat -> RIn × SIn,
      M.WinsPlay (pairPlay receiver sender env))
    (hroot : ∀ move : RIn × SIn,
      pairPlay receiver sender (fun _ => move) 0 = expected move) :
    ∀ env : Nat -> RIn × SIn,
      (M.rootPinned expected).WinsPlay (pairPlay receiver sender env) := by
  intro env
  let word := pairPlay receiver sender env
  have hfirst : word 0 = expected (word 0).1 := by
    have h := hroot (env 0)
    simpa [word, pairPlay, treePlay, treeOfPair, branchNode] using h
  have hsafe := rootPinned_run_safe_of_root_eq M expected word hfirst
  have hparity := hbase env
  unfold BlockRecordMonitor.WinsPlay at hparity ⊢
  have heq :
      (fun n => (M.rootPinned expected).priority
        ((M.rootPinned expected).run word n)) =
        fun n => M.priority (M.run word n) + 2 := by
    funext n
    change
      (if ((M.rootPinned expected).run word n).safe then
          M.priority ((M.rootPinned expected).run word n).base + 2
        else 1) = M.priority (M.run word n) + 2
    rw [hsafe n, if_pos rfl, rootPinned_run_base M expected word n]
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity

/-- Every winning narrowed tree for the pinned monitor has exactly the
prescribed complete root record, for every possible first move. -/
theorem rootPinned_root_record
    [Inhabited RIn] [Inhabited SIn]
    (expected : RIn × SIn -> RealizedBlockRound RIn SIn ROut SOut)
    (narrowed : LabeledTree SIn
      (NarrowedBlockLabel RIn SIn ROut SOut (M.rootPinned expected).State))
    (hthreads : NarrowedAllThreadsWin (M.rootPinned expected) narrowed)
    (move : RIn × SIn) :
    narrowedRecord (M.rootPinned expected) (narrowed [])
        (M.rootPinned expected).initial move = expected move := by
  classical
  by_contra hne
  let env : Nat -> RIn × SIn
    | 0 => move
    | _ + 1 => (default, default)
  have henv0 : env 0 = move := rfl
  have hfalse :
      (narrowedThreadState (M.rootPinned expected) narrowed env 1).safe = false := by
    change
      (narrowedControl (M.rootPinned expected) narrowed
        (branchNode env 0 ++ [env 0])).safe = false
    rw [narrowedControl_append]
    change Bool.and true
      (Bool.or (!true)
        (decide
          (narrowedRecord (M.rootPinned expected) (narrowed [])
            (M.rootPinned expected).initial move = expected move))) = false
    have hd : decide
        (narrowedRecord (M.rootPinned expected) (narrowed [])
          (M.rootPinned expected).initial move = expected move) = false :=
      decide_eq_false hne
    rw [hd]
    rfl
  have hpersist : ∀ k,
      (narrowedThreadState (M.rootPinned expected) narrowed env (1 + k)).safe = false := by
    intro k
    induction k with
    | zero => simpa using hfalse
    | succ k ih =>
        rw [Nat.add_succ]
        change
          (narrowedControl (M.rootPinned expected) narrowed
            (branchNode env (1 + k) ++ [env (1 + k)])).safe = false
        rw [narrowedControl_append]
        change Bool.and
          (narrowedThreadState (M.rootPinned expected) narrowed env (1 + k)).safe
          _ = false
        rw [ih]
        rfl
  have heventual : ∀ n, 1 ≤ n ->
      (M.rootPinned expected).priority
        (narrowedThreadState (M.rootPinned expected) narrowed env n) = 1 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    change
      (if (narrowedThreadState (M.rootPinned expected) narrowed env (1 + k)).safe
        then _ else 1) = 1
    rw [hpersist k]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ 1 heventual
    (hthreads env)

end BlockRecordMonitor

namespace DetParityAutomaton

universe s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- The two independently finite initial controllers, each pinned to the
same original strategy on its first letter. -/
structure RootCompatibleInitialControllers
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  leftController : TransitionRationalTree.{v, max u v x y s, s} In₂
    (NarrowedBlockLabel In₁ In₂
      (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
      ((initialLeftBlockMonitor A).rootPinned
        (fun move => initialLeftLetterAt
          (initialLeftLambdaOfStrategy strategy) [] move)).State)
  leftWins : NarrowedAllThreadsWin
    ((initialLeftBlockMonitor A).rootPinned
      (fun move => initialLeftLetterAt
        (initialLeftLambdaOfStrategy strategy) [] move))
    leftController.labeledTree
  rightController : TransitionRationalTree.{u, max u v x y s, s} In₁
    (NarrowedBlockLabel In₂ In₁
      (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
      ((initialRightBlockMonitor A).rootPinned
        (fun move => initialRightLetterAt
          (initialRightLambdaOfStrategy strategy) [] move)).State)
  rightWins : NarrowedAllThreadsWin
    ((initialRightBlockMonitor A).rootPinned
      (fun move => initialRightLetterAt
        (initialRightLambdaOfStrategy strategy) [] move))
    rightController.labeledTree

/-- A winning distributed strategy yields separately finite but root-compatible
initial controllers. -/
noncomputable def rootCompatibleInitialControllers_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    RootCompatibleInitialControllers A strategy := by
  classical
  let leftLambda := initialLeftLambdaOfStrategy strategy
  let leftExpected := fun move => initialLeftLetterAt leftLambda [] move
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
  have hleftRealizable :
      ∃ receiver : ReceiverBlockStrategy In₁ In₂
          (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)),
        ∃ sender : SenderBlockStrategy In₂ Out₂,
          ∀ env : Nat -> In₁ × In₂,
            ((initialLeftBlockMonitor A).rootPinned leftExpected).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨initialLeftReceiverStrategy leftLambda,
      initialLeftSenderStrategy leftLambda,
      (initialLeftBlockMonitor A).rootPinned_realizable leftExpected
        _ _ hleftBase hleftRoot⟩
  have hleftControllers :=
    (block_realizable_iff_implementable_controller_unconditional
      ((initialLeftBlockMonitor A).rootPinned leftExpected)).mp hleftRealizable
  let leftController := Classical.choose hleftControllers
  have leftWins := Classical.choose_spec hleftControllers
  let rightLambda := initialRightLambdaOfStrategy strategy
  let rightExpected := fun move => initialRightLetterAt rightLambda [] move
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
  have hrightRealizable :
      ∃ receiver : ReceiverBlockStrategy In₂ In₁
          (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)),
        ∃ sender : SenderBlockStrategy In₁ Out₁,
          ∀ env : Nat -> In₂ × In₁,
            ((initialRightBlockMonitor A).rootPinned rightExpected).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨initialRightReceiverStrategy rightLambda,
      initialRightSenderStrategy rightLambda,
      (initialRightBlockMonitor A).rootPinned_realizable rightExpected
        _ _ hrightBase hrightRoot⟩
  have hrightControllers :=
    (block_realizable_iff_implementable_controller_unconditional
      ((initialRightBlockMonitor A).rootPinned rightExpected)).mp hrightRealizable
  let rightController := Classical.choose hrightControllers
  have rightWins := Classical.choose_spec hrightControllers
  exact ⟨leftController, leftWins, rightController, rightWins⟩

/-- The two pinned controllers prescribe the same process-one output on the
locally indistinguishable initial `left`/`both` receive. -/
theorem rootCompatible_initial_outputOne
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (move : In₁ × In₂) :
    ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).informedOne =
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightBlockMonitor A).rootPinned
          (fun move => initialRightLetterAt
            (initialRightLambdaOfStrategy strategy) [] move)).initial
        (move.2, move.1)).reversingOne := by
  have hleft := (initialLeftBlockMonitor A).rootPinned_root_record
    (fun move => initialLeftLetterAt
      (initialLeftLambdaOfStrategy strategy) [] move)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (initialRightBlockMonitor A).rootPinned_root_record
    (fun move => initialRightLetterAt
      (initialRightLambdaOfStrategy strategy) [] move)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.informedOne) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.reversingOne) hright
  have hleftOut' :
      ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).informedOne =
        (initialLeftLetterAt
          (initialLeftLambdaOfStrategy strategy) [] move).2.1.informedOne := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hleftOut
  have hrightOut' :
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightBlockMonitor A).rootPinned
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

/-- Process-two mirror: the initial `right`/`both` receive output agrees. -/
theorem rootCompatible_initial_outputTwo
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (move : In₁ × In₂) :
    ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).reversingTwo =
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightBlockMonitor A).rootPinned
          (fun move => initialRightLetterAt
            (initialRightLambdaOfStrategy strategy) [] move)).initial
        (move.2, move.1)).informedTwo := by
  have hleft := (initialLeftBlockMonitor A).rootPinned_root_record
    (fun move => initialLeftLetterAt
      (initialLeftLambdaOfStrategy strategy) [] move)
    controllers.leftController.labeledTree controllers.leftWins move
  have hright := (initialRightBlockMonitor A).rootPinned_root_record
    (fun move => initialRightLetterAt
      (initialRightLambdaOfStrategy strategy) [] move)
    controllers.rightController.labeledTree controllers.rightWins (move.2, move.1)
  have hleftOut := congrArg (fun letter => letter.2.1.reversingTwo) hleft
  have hrightOut := congrArg (fun letter => letter.2.1.informedTwo) hright
  have hleftOut' :
      ((controllers.leftController.labelOf controllers.leftController.initial).2
        ((initialLeftBlockMonitor A).rootPinned
          (fun move => initialLeftLetterAt
            (initialLeftLambdaOfStrategy strategy) [] move)).initial move).reversingTwo =
        (initialLeftLetterAt
          (initialLeftLambdaOfStrategy strategy) [] move).2.1.reversingTwo := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hleftOut
  have hrightOut' :
      ((controllers.rightController.labelOf controllers.rightController.initial).2
        ((initialRightBlockMonitor A).rootPinned
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

/-! ## Semantic readback of the pinned controllers -/

/-- Initial-left lambda read from the finite pinned controller. -/
noncomputable def initialLeftLambdaOfPinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy) :
    InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := (initialLeftBlockMonitor A).rootPinned
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
noncomputable def initialRightLambdaOfPinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy) :
    InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := (initialRightBlockMonitor A).rootPinned
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

theorem initialLeft_pairPlay_pinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (env : Nat -> In₁ × In₂) :
    pairPlay
        (initialLeftReceiverStrategy
          (initialLeftLambdaOfPinnedController A strategy controllers))
        (initialLeftSenderStrategy
          (initialLeftLambdaOfPinnedController A strategy controllers)) env =
      treePlay
        (narrowedInducedTree
          ((initialLeftBlockMonitor A).rootPinned
            (fun move => initialLeftLetterAt
              (initialLeftLambdaOfStrategy strategy) [] move))
          controllers.leftController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    initialLeftReceiverStrategy, initialLeftSenderStrategy,
    initialLeftLambdaOfPinnedController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

theorem initialRight_pairPlay_pinnedController
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy)
    (env : Nat -> In₂ × In₁) :
    pairPlay
        (initialRightReceiverStrategy
          (initialRightLambdaOfPinnedController A strategy controllers))
        (initialRightSenderStrategy
          (initialRightLambdaOfPinnedController A strategy controllers)) env =
      treePlay
        (narrowedInducedTree
          ((initialRightBlockMonitor A).rootPinned
            (fun move => initialRightLetterAt
              (initialRightLambdaOfStrategy strategy) [] move))
          controllers.rightController.labeledTree) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    initialRightReceiverStrategy, initialRightSenderStrategy,
    initialRightLambdaOfPinnedController, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

/-- The finite pinned left controller retains both semantic obligations of
the raw initial lambda. -/
theorem RootCompatibleInitialControllers.left_sound
    [Inhabited In₁] [Inhabited In₂] [Inhabited (In₁ × In₂)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy) :
    let lambda := initialLeftLambdaOfPinnedController A strategy controllers
    InitialLeftForeverAccepts A lambda ∧ InitialLeftCloseFeasible A lambda := by
  let expected := fun move => initialLeftLetterAt
    (initialLeftLambdaOfStrategy strategy) [] move
  let pin := (initialLeftBlockMonitor A).rootPinned expected
  let lambda := initialLeftLambdaOfPinnedController A strategy controllers
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.leftWins
  have hpin : ∀ env : Nat -> In₁ × In₂,
      pin.WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) := by
    intro env
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.leftController.labeledTree)).mp htree env
    rw [initialLeft_pairPlay_pinnedController A strategy controllers env]
    exact hplay
  have hbase : ∀ env : Nat -> In₁ × In₂,
      (initialLeftBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) := by
    intro env
    let word := pairPlay (initialLeftReceiverStrategy lambda)
      (initialLeftSenderStrategy lambda) env
    have hrootRecord := (initialLeftBlockMonitor A).rootPinned_root_record
      expected controllers.leftController.labeledTree controllers.leftWins (env 0)
    have hwordRoot : word 0 = expected (word 0).1 := by
      have hplay := congrFun
        (initialLeft_pairPlay_pinnedController A strategy controllers env) 0
      change pairPlay (initialLeftReceiverStrategy lambda)
        (initialLeftSenderStrategy lambda) env 0 =
          expected (pairPlay (initialLeftReceiverStrategy lambda)
            (initialLeftSenderStrategy lambda) env 0).1
      rw [hplay]
      simpa [treePlay, branchNode, narrowedInducedTree,
        narrowedControl, narrowedRecord] using hrootRecord
    have hsafe := (initialLeftBlockMonitor A).rootPinned_run_safe_of_root_eq
      expected word hwordRoot
    have hp := hpin env
    unfold BlockRecordMonitor.WinsPlay at hp ⊢
    have heq :
        (fun n => pin.priority (pin.run word n)) =
          fun n => (initialLeftBlockMonitor A).priority
            ((initialLeftBlockMonitor A).run word n) + 2 := by
      funext n
      change (if (pin.run word n).safe then
          (initialLeftBlockMonitor A).priority (pin.run word n).base + 2 else 1) = _
      rw [hsafe n, if_pos rfl,
        (initialLeftBlockMonitor A).rootPinned_run_base expected word n]
    rw [heq] at hp
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hp
  exact initialLeft_conditions_of_monitorWins A lambda hbase

/-- Mirror semantic guarantee. -/
theorem RootCompatibleInitialControllers.right_sound
    [Inhabited In₁] [Inhabited In₂] [Inhabited (In₂ × In₁)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers : RootCompatibleInitialControllers A strategy) :
    let lambda := initialRightLambdaOfPinnedController A strategy controllers
    InitialRightForeverAccepts A lambda ∧ InitialRightCloseFeasible A lambda := by
  let expected := fun move => initialRightLetterAt
    (initialRightLambdaOfStrategy strategy) [] move
  let pin := (initialRightBlockMonitor A).rootPinned expected
  let lambda := initialRightLambdaOfPinnedController A strategy controllers
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    pin controllers.rightWins
  have hpin : ∀ env : Nat -> In₂ × In₁,
      pin.WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) := by
    intro env
    have hplay := (pin.lift_winningTree_iff
      (narrowedInducedTree pin controllers.rightController.labeledTree)).mp htree env
    rw [initialRight_pairPlay_pinnedController A strategy controllers env]
    exact hplay
  have hbase : ∀ env : Nat -> In₂ × In₁,
      (initialRightBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) := by
    intro env
    let word := pairPlay (initialRightReceiverStrategy lambda)
      (initialRightSenderStrategy lambda) env
    have hrootRecord := (initialRightBlockMonitor A).rootPinned_root_record
      expected controllers.rightController.labeledTree controllers.rightWins (env 0)
    have hwordRoot : word 0 = expected (word 0).1 := by
      have hplay := congrFun
        (initialRight_pairPlay_pinnedController A strategy controllers env) 0
      change pairPlay (initialRightReceiverStrategy lambda)
        (initialRightSenderStrategy lambda) env 0 =
          expected (pairPlay (initialRightReceiverStrategy lambda)
            (initialRightSenderStrategy lambda) env 0).1
      rw [hplay]
      simpa [treePlay, branchNode, narrowedInducedTree,
        narrowedControl, narrowedRecord] using hrootRecord
    have hsafe := (initialRightBlockMonitor A).rootPinned_run_safe_of_root_eq
      expected word hwordRoot
    have hp := hpin env
    unfold BlockRecordMonitor.WinsPlay at hp ⊢
    have heq :
        (fun n => pin.priority (pin.run word n)) =
          fun n => (initialRightBlockMonitor A).priority
            ((initialRightBlockMonitor A).run word n) + 2 := by
      funext n
      change (if (pin.run word n).safe then
          (initialRightBlockMonitor A).priority (pin.run word n).base + 2 else 1) = _
      rw [hsafe n, if_pos rfl,
        (initialRightBlockMonitor A).rootPinned_run_base expected word n]
    rw [heq] at hp
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hp
  exact initialRight_conditions_of_monitorWins A lambda hbase

end DetParityAutomaton

end DistributedSynthesis
