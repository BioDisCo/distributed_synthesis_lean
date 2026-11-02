/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedFeasiblePolicyBank
import Mathlib.Data.List.Indexes

/-!
# Regularizing the initial homogeneous block

The recurrent paired controller begins only after the first maximal
one-sided block closes.  This file builds the missing finite monitor for an
initial left block.  Its ordinary component checks the DPA from `A.initial`;
at every possible reversing round its sticky bit checks that the paired
right/both target is feasible.  The right-block mirror follows the same
construction.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Outputs controlled by the full-information side at one potential round
of the initial left block.  `informedOne` is shared by `left` and `both`;
`reversingTwo` is shared by `right` and `both`. -/
structure InitialLeftReceiverOutput where
  informedOne : Out₁
  reversingOne : Out₁
  reversingTwo : Out₂
deriving Fintype, Inhabited

abbrev InitialLeftLetter :=
  RealizedBlockRound In₁ In₂
    (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂

/-- Complete local lambda for the initial left block and its possible close. -/
structure InitialLeftLambda where
  blindTwo : SenderBlockStrategy In₂ Out₂
  informedOne : ReceiverBlockStrategy In₁ In₂ Out₁
  reversingOne : ReceiverBlockStrategy In₁ In₂ Out₁
  reversingTwo : ReceiverBlockStrategy In₁ In₂ Out₂

def initialLeftLetterAt
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    InitialLeftLetter (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) :=
  (move,
    ⟨lambda.informedOne past move, lambda.reversingOne past move,
      lambda.reversingTwo past move⟩,
    lambda.blindTwo (senderWord past) move.2)

def initialLeftOmegaWord
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n =>
    let letter := initialLeftLetterAt lambda (omegaPrefix env n) (env n)
    leftRoundRecord letter.1 letter.2.1.informedOne letter.2.2

/-- Current ordinary DPA state and minimum-priority representative of the
initial block prefix. -/
abbrev InitialBlockScan := A.State × A.State

def initialBlockScanStep
    (scan : InitialBlockScan A)
    (record : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    InitialBlockScan A :=
  let next := A.step scan.1 record
  (next, A.minPriorityState scan.2 next)

def initialLeftScanStep
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    InitialBlockScan A :=
  initialBlockScanStep A scan
    (leftRoundRecord letter.1 letter.2.1.informedOne letter.2.2)

/-- Paired process-two target staged if the current round is the first
`right`, respectively a synchronizing `both`, close. -/
def initialLeftCloseTarget
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    PairedEntryTreeState A :=
  let rightState := A.step scan.1
    (rightRoundRecord (letter.1.2, letter.1.1)
      letter.2.1.reversingOne letter.2.1.reversingTwo)
  let bothState := A.step scan.1
    (bothRoundRecord letter.1 letter.2.1.informedOne
      letter.2.1.reversingTwo)
  Sum.inr (Sum.inr ((rightState, bothState), scan.2))

def InitialLeftForeverAccepts
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ env : Nat -> In₁ × In₂,
    A.Accepts (initialLeftOmegaWord lambda env)

/-- The actual scan after a lambda prefix. -/
def initialLeftScanAfter
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) : InitialBlockScan A :=
  blockEndAndMin A A.initial
    (past.mapIdx fun i move =>
      let prior := past.take i
      leftRoundRecord move (lambda.informedOne prior move)
        (lambda.blindTwo (senderWord prior) move.2))

@[simp] theorem initialLeftScanAfter_nil
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    initialLeftScanAfter A lambda [] = (A.initial, A.initial) := rfl

def InitialLeftCloseFeasible
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ past move,
    (pairedEntryRunAutomaton A
      (initialLeftCloseTarget A (initialLeftScanAfter A lambda past)
        (initialLeftLetterAt lambda past move))).HasRationalRun

theorem initialLeftScanAfter_append
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    initialLeftScanAfter A lambda (past ++ [move]) =
      initialLeftScanStep A (initialLeftScanAfter A lambda past)
        (initialLeftLetterAt lambda past move) := by
  unfold initialLeftScanAfter
  rw [List.mapIdx_append_one, blockEndAndMin_snoc]
  have hmap :
      List.mapIdx
          (fun i oldMove =>
            leftRoundRecord oldMove
              (lambda.informedOne ((past ++ [move]).take i) oldMove)
              (lambda.blindTwo
                (senderWord ((past ++ [move]).take i)) oldMove.2)) past =
        List.mapIdx
          (fun i oldMove =>
            leftRoundRecord oldMove (lambda.informedOne (past.take i) oldMove)
              (lambda.blindTwo (senderWord (past.take i)) oldMove.2)) past := by
    rw [List.mapIdx_eq_ofFn, List.mapIdx_eq_ofFn]
    congr 1
    funext i
    rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  rw [hmap]
  simp [initialLeftScanStep, initialBlockScanStep, initialLeftLetterAt]

/-- Local receiver component of an initial-left lambda. -/
def initialLeftReceiverStrategy
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    ReceiverBlockStrategy In₁ In₂
      (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) :=
  fun past move =>
    ⟨lambda.informedOne past move, lambda.reversingOne past move,
      lambda.reversingTwo past move⟩

def initialLeftSenderStrategy
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    SenderBlockStrategy In₂ Out₂ := lambda.blindTwo

theorem initialLeft_pairPlay_eq_letterAt
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₁ × In₂) (n : Nat) :
    pairPlay (initialLeftReceiverStrategy lambda)
        (initialLeftSenderStrategy lambda) env n =
      initialLeftLetterAt lambda (omegaPrefix env n) (env n) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, initialLeftReceiverStrategy,
    initialLeftSenderStrategy, initialLeftLetterAt, senderWord]

/-- Finite initial-left monitor: ordinary DPA parity plus sticky feasibility
of every staged paired close. -/
noncomputable def initialLeftBlockMonitor :
    BlockRecordMonitor In₁ In₂
      (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂ := by
  classical
  exact {
    State := InitialBlockScan A × Bool
    stateFinite := inferInstance
    initial := ((A.initial, A.initial), true)
    step := fun state letter =>
      let feasible := (pairedEntryRunAutomaton A
        (initialLeftCloseTarget A state.1 letter)).HasRationalRun
      (initialLeftScanStep A state.1 letter, state.2 && decide feasible)
    priority := fun state => if state.2 then A.priority state.1.1 + 2 else 1
  }

theorem initialLeftBlockMonitor_run_eq
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : InitialLeftCloseFeasible A lambda)
    (env : Nat -> In₁ × In₂) : ∀ n,
    (initialLeftBlockMonitor A).run
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) n =
      (initialLeftScanAfter A lambda (omegaPrefix env n), true) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        initialLeft_pairPlay_eq_letterAt lambda env n,
        omegaPrefix_succ, initialLeftScanAfter_append]
      have hfeasible := hclose (omegaPrefix env n) (env n)
      simp [initialLeftBlockMonitor, hfeasible]

/-- Without assuming feasibility, the ordinary scan component still has its
exact shape; only the sticky bit is abstract. -/
theorem initialLeftBlockMonitor_run_shape
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₁ × In₂) : ∀ n, ∃ safe : Bool,
    (initialLeftBlockMonitor A).run
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) n =
      (initialLeftScanAfter A lambda (omegaPrefix env n), safe) := by
  intro n
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih,
        initialLeft_pairPlay_eq_letterAt lambda env n,
        omegaPrefix_succ, initialLeftScanAfter_append]
      exact ⟨((initialLeftBlockMonitor A).step
        (initialLeftScanAfter A lambda (omegaPrefix env n), safe)
        (initialLeftLetterAt lambda (omegaPrefix env n) (env n))).2, rfl⟩

theorem initialLeftBlockMonitor_safe_false_persists
    (play : Nat -> InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    {N : Nat}
    (hfalse : ((initialLeftBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n -> ((initialLeftBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((initialLeftBlockMonitor A).run play (N + k)).2 = false :=
        ih (Nat.le_add_right N k)
      change
        Bool.and ((initialLeftBlockMonitor A).run play (N + k)).2 _ = false
      rw [ih']
      rfl

/-- Winning the initial-left monitor forces every staged close to be
feasible. -/
theorem initialLeftCloseFeasible_of_monitorWins
    [Inhabited (In₁ × In₂)]
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (initialLeftBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env)) :
    InitialLeftCloseFeasible A lambda := by
  classical
  intro past move
  by_contra hnot
  let finiteWord := past ++ [move]
  let env : Nat -> In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      have henvN : env n = finiteWord[n] :=
        omegaOfList_eq_getElem finiteWord n hnPrefix
      rw [henvN]
      simp [finiteWord, hnRight]
  have henv : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    have henvN : env past.length = finiteWord[past.length] :=
      omegaOfList_eq_getElem finiteWord past.length hnPrefix
    rw [henvN]
    simp [finiteWord]
  rcases initialLeftBlockMonitor_run_shape A lambda env past.length with
    ⟨safe, hshape⟩
  have hfalse :
      ((initialLeftBlockMonitor A).run
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) (past.length + 1)).2 = false := by
    rw [BlockRecordMonitor.run, hshape,
      initialLeft_pairPlay_eq_letterAt lambda env past.length, hpast, henv]
    simp [initialLeftBlockMonitor, hnot]
  have hpersist := initialLeftBlockMonitor_safe_false_persists A
    (pairPlay (initialLeftReceiverStrategy lambda)
      (initialLeftSenderStrategy lambda) env) hfalse
  have heventual : ∀ n, past.length + 1 ≤ n ->
      (initialLeftBlockMonitor A).priority
        ((initialLeftBlockMonitor A).run
          (pairPlay (initialLeftReceiverStrategy lambda)
            (initialLeftSenderStrategy lambda) env) n) = 1 := by
    intro n hn
    have hs := hpersist n hn
    change (if ((initialLeftBlockMonitor A).run
      (pairPlay (initialLeftReceiverStrategy lambda)
        (initialLeftSenderStrategy lambda) env) n).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ _ heventual (hmonitor env)

/-- Monitor winning is equivalent to the two semantic initial-left
conditions consumed by the finite controller theorem. -/
theorem initialLeft_conditions_of_monitorWins
    [Inhabited (In₁ × In₂)]
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (initialLeftBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env)) :
    InitialLeftForeverAccepts A lambda ∧ InitialLeftCloseFeasible A lambda := by
  have hclose := initialLeftCloseFeasible_of_monitorWins A lambda hmonitor
  refine ⟨?_, hclose⟩
  intro env
  have hm := hmonitor env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n => (initialLeftBlockMonitor A).priority
        ((initialLeftBlockMonitor A).run
          (pairPlay (initialLeftReceiverStrategy lambda)
            (initialLeftSenderStrategy lambda) env) n)) =
        fun n => A.priority (A.run (initialLeftOmegaWord lambda env) n) + 2 := by
    funext n
    rw [initialLeftBlockMonitor_run_eq A lambda hclose env n]
    simp [initialLeftBlockMonitor]
    have hscan :
        (initialLeftScanAfter A lambda (omegaPrefix env n)).1 =
          A.run (initialLeftOmegaWord lambda env) n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [omegaPrefix_succ, initialLeftScanAfter_append]
          simp only [initialLeftScanStep, initialBlockScanStep]
          rw [ih]
          rfl
    rw [hscan]
  rw [heq] at hm
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hm

theorem initialLeftBlockMonitor_realizable
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : InitialLeftForeverAccepts A lambda)
    (hclose : InitialLeftCloseFeasible A lambda) :
    ∀ env : Nat -> In₁ × In₂,
      (initialLeftBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) := by
  intro env
  have hparity : NatSeqMinEvenParity
      (fun n => A.priority
        (A.run (initialLeftOmegaWord lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr (hforever env)
  unfold BlockRecordMonitor.WinsPlay
  convert hparity using 1
  funext n
  rw [initialLeftBlockMonitor_run_eq A lambda hclose env n]
  simp [initialLeftBlockMonitor]
  have hscan :
      (initialLeftScanAfter A lambda (omegaPrefix env n)).1 =
        A.run (initialLeftOmegaWord lambda env) n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [omegaPrefix_succ, initialLeftScanAfter_append]
        simp only [initialLeftScanStep, initialBlockScanStep]
        rw [ih]
        rfl
  rw [hscan]

/-- Once one T2-and-feasible initial-left lambda exists, unconditional sender
narrowing produces its finite controller. -/
theorem exists_finite_initialLeftController
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (hexists : ∃ lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      InitialLeftForeverAccepts A lambda ∧ InitialLeftCloseFeasible A lambda) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, s} In₂
      (NarrowedBlockLabel In₁ In₂
        (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
        (initialLeftBlockMonitor A).State),
      NarrowedAllThreadsWin (initialLeftBlockMonitor A)
        controller.labeledTree := by
  rcases hexists with ⟨lambda, hforever, hclose⟩
  refine (block_realizable_iff_implementable_controller_unconditional
    (initialLeftBlockMonitor A)).mp ?_
  exact ⟨initialLeftReceiverStrategy lambda, initialLeftSenderStrategy lambda,
    initialLeftBlockMonitor_realizable A lambda hforever hclose⟩

/-! ## Initial right block -/

/-- Outputs controlled by the full-information process two during a possible
round of the initial right block.  The same three-value staging is the exact
process-swapped mirror of `InitialLeftReceiverOutput`. -/
structure InitialRightReceiverOutput where
  informedTwo : Out₂
  reversingOne : Out₁
  reversingTwo : Out₂
deriving Fintype, Inhabited

abbrev InitialRightLetter :=
  RealizedBlockRound In₂ In₁
    (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁

/-- Complete local lambda for the initial right block and its possible close. -/
structure InitialRightLambda where
  blindOne : SenderBlockStrategy In₁ Out₁
  informedTwo : ReceiverBlockStrategy In₂ In₁ Out₂
  reversingOne : ReceiverBlockStrategy In₂ In₁ Out₁
  reversingTwo : ReceiverBlockStrategy In₂ In₁ Out₂

def initialRightLetterAt
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    InitialRightLetter (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) :=
  (move,
    ⟨lambda.informedTwo past move, lambda.reversingOne past move,
      lambda.reversingTwo past move⟩,
    lambda.blindOne (senderWord past) move.2)

def initialRightOmegaWord
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₂ × In₁) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n =>
    let letter := initialRightLetterAt lambda (omegaPrefix env n) (env n)
    rightRoundRecord letter.1 letter.2.2 letter.2.1.informedTwo

def initialRightScanStep
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    InitialBlockScan A :=
  initialBlockScanStep A scan
    (rightRoundRecord letter.1 letter.2.2 letter.2.1.informedTwo)

/-- Paired process-one target staged if the current round is the first
`left`, respectively a synchronizing `both`, close. -/
def initialRightCloseTarget
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    PairedEntryTreeState A :=
  let move : In₁ × In₂ := (letter.1.2, letter.1.1)
  let leftState := A.step scan.1
    (leftRoundRecord move letter.2.1.reversingOne
      letter.2.1.reversingTwo)
  let bothState := A.step scan.1
    (bothRoundRecord move letter.2.1.reversingOne
      letter.2.1.informedTwo)
  Sum.inr (Sum.inl ((leftState, bothState), scan.2))

def InitialRightForeverAccepts
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ env : Nat -> In₂ × In₁,
    A.Accepts (initialRightOmegaWord lambda env)

def initialRightScanAfter
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) : InitialBlockScan A :=
  blockEndAndMin A A.initial
    (past.mapIdx fun i move =>
      let prior := past.take i
      rightRoundRecord move
        (lambda.blindOne (senderWord prior) move.2)
        (lambda.informedTwo prior move))

@[simp] theorem initialRightScanAfter_nil
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    initialRightScanAfter A lambda [] = (A.initial, A.initial) := rfl

def InitialRightCloseFeasible
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ past move,
    (pairedEntryRunAutomaton A
      (initialRightCloseTarget A (initialRightScanAfter A lambda past)
        (initialRightLetterAt lambda past move))).HasRationalRun

theorem initialRightScanAfter_append
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    initialRightScanAfter A lambda (past ++ [move]) =
      initialRightScanStep A (initialRightScanAfter A lambda past)
        (initialRightLetterAt lambda past move) := by
  unfold initialRightScanAfter
  rw [List.mapIdx_append_one, blockEndAndMin_snoc]
  have hmap :
      List.mapIdx
          (fun i oldMove =>
            rightRoundRecord oldMove
              (lambda.blindOne
                (senderWord ((past ++ [move]).take i)) oldMove.2)
              (lambda.informedTwo ((past ++ [move]).take i) oldMove)) past =
        List.mapIdx
          (fun i oldMove =>
            rightRoundRecord oldMove
              (lambda.blindOne (senderWord (past.take i)) oldMove.2)
              (lambda.informedTwo (past.take i) oldMove)) past := by
    rw [List.mapIdx_eq_ofFn, List.mapIdx_eq_ofFn]
    congr 1
    funext i
    rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  rw [hmap]
  simp [initialRightScanStep, initialBlockScanStep, initialRightLetterAt]

def initialRightReceiverStrategy
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    ReceiverBlockStrategy In₂ In₁
      (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) :=
  fun past move =>
    ⟨lambda.informedTwo past move, lambda.reversingOne past move,
      lambda.reversingTwo past move⟩

def initialRightSenderStrategy
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    SenderBlockStrategy In₁ Out₁ := lambda.blindOne

theorem initialRight_pairPlay_eq_letterAt
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₂ × In₁) (n : Nat) :
    pairPlay (initialRightReceiverStrategy lambda)
        (initialRightSenderStrategy lambda) env n =
      initialRightLetterAt lambda (omegaPrefix env n) (env n) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, initialRightReceiverStrategy,
    initialRightSenderStrategy, initialRightLetterAt, senderWord]

noncomputable def initialRightBlockMonitor :
    BlockRecordMonitor In₂ In₁
      (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁ := by
  classical
  exact {
    State := InitialBlockScan A × Bool
    stateFinite := inferInstance
    initial := ((A.initial, A.initial), true)
    step := fun state letter =>
      let feasible := (pairedEntryRunAutomaton A
        (initialRightCloseTarget A state.1 letter)).HasRationalRun
      (initialRightScanStep A state.1 letter, state.2 && decide feasible)
    priority := fun state => if state.2 then A.priority state.1.1 + 2 else 1
  }

theorem initialRightBlockMonitor_run_eq
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : InitialRightCloseFeasible A lambda)
    (env : Nat -> In₂ × In₁) : ∀ n,
    (initialRightBlockMonitor A).run
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) n =
      (initialRightScanAfter A lambda (omegaPrefix env n), true) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        initialRight_pairPlay_eq_letterAt lambda env n,
        omegaPrefix_succ, initialRightScanAfter_append]
      have hfeasible := hclose (omegaPrefix env n) (env n)
      simp [initialRightBlockMonitor, hfeasible]

theorem initialRightBlockMonitor_run_shape
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₂ × In₁) : ∀ n, ∃ safe : Bool,
    (initialRightBlockMonitor A).run
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) n =
      (initialRightScanAfter A lambda (omegaPrefix env n), safe) := by
  intro n
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih,
        initialRight_pairPlay_eq_letterAt lambda env n,
        omegaPrefix_succ, initialRightScanAfter_append]
      exact ⟨((initialRightBlockMonitor A).step
        (initialRightScanAfter A lambda (omegaPrefix env n), safe)
        (initialRightLetterAt lambda (omegaPrefix env n) (env n))).2, rfl⟩

theorem initialRightBlockMonitor_safe_false_persists
    (play : Nat -> InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    {N : Nat}
    (hfalse : ((initialRightBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n -> ((initialRightBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((initialRightBlockMonitor A).run play (N + k)).2 = false :=
        ih (Nat.le_add_right N k)
      change Bool.and ((initialRightBlockMonitor A).run play (N + k)).2 _ = false
      rw [ih']
      rfl

theorem initialRightCloseFeasible_of_monitorWins
    [Inhabited (In₂ × In₁)]
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (initialRightBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env)) :
    InitialRightCloseFeasible A lambda := by
  classical
  intro past move
  by_contra hnot
  let finiteWord := past ++ [move]
  let env : Nat -> In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      have henvN : env n = finiteWord[n] :=
        omegaOfList_eq_getElem finiteWord n hnPrefix
      rw [henvN]
      simp [finiteWord, hnRight]
  have henv : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    have henvN : env past.length = finiteWord[past.length] :=
      omegaOfList_eq_getElem finiteWord past.length hnPrefix
    rw [henvN]
    simp [finiteWord]
  rcases initialRightBlockMonitor_run_shape A lambda env past.length with
    ⟨safe, hshape⟩
  have hfalse :
      ((initialRightBlockMonitor A).run
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) (past.length + 1)).2 = false := by
    rw [BlockRecordMonitor.run, hshape,
      initialRight_pairPlay_eq_letterAt lambda env past.length, hpast, henv]
    simp [initialRightBlockMonitor, hnot]
  have hpersist := initialRightBlockMonitor_safe_false_persists A
    (pairPlay (initialRightReceiverStrategy lambda)
      (initialRightSenderStrategy lambda) env) hfalse
  have heventual : ∀ n, past.length + 1 ≤ n ->
      (initialRightBlockMonitor A).priority
        ((initialRightBlockMonitor A).run
          (pairPlay (initialRightReceiverStrategy lambda)
            (initialRightSenderStrategy lambda) env) n) = 1 := by
    intro n hn
    have hs := hpersist n hn
    change (if ((initialRightBlockMonitor A).run
      (pairPlay (initialRightReceiverStrategy lambda)
        (initialRightSenderStrategy lambda) env) n).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ _ heventual (hmonitor env)

theorem initialRight_conditions_of_monitorWins
    [Inhabited (In₂ × In₁)]
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (initialRightBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env)) :
    InitialRightForeverAccepts A lambda ∧ InitialRightCloseFeasible A lambda := by
  have hclose := initialRightCloseFeasible_of_monitorWins A lambda hmonitor
  refine ⟨?_, hclose⟩
  intro env
  have hm := hmonitor env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n => (initialRightBlockMonitor A).priority
        ((initialRightBlockMonitor A).run
          (pairPlay (initialRightReceiverStrategy lambda)
            (initialRightSenderStrategy lambda) env) n)) =
        fun n => A.priority (A.run (initialRightOmegaWord lambda env) n) + 2 := by
    funext n
    rw [initialRightBlockMonitor_run_eq A lambda hclose env n]
    simp [initialRightBlockMonitor]
    have hscan :
        (initialRightScanAfter A lambda (omegaPrefix env n)).1 =
          A.run (initialRightOmegaWord lambda env) n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [omegaPrefix_succ, initialRightScanAfter_append]
          simp only [initialRightScanStep, initialBlockScanStep]
          rw [ih]
          rfl
    rw [hscan]
  rw [heq] at hm
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hm

theorem initialRightBlockMonitor_realizable
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : InitialRightForeverAccepts A lambda)
    (hclose : InitialRightCloseFeasible A lambda) :
    ∀ env : Nat -> In₂ × In₁,
      (initialRightBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) := by
  intro env
  have hparity : NatSeqMinEvenParity
      (fun n => A.priority
        (A.run (initialRightOmegaWord lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr (hforever env)
  unfold BlockRecordMonitor.WinsPlay
  convert hparity using 1
  funext n
  rw [initialRightBlockMonitor_run_eq A lambda hclose env n]
  simp [initialRightBlockMonitor]
  have hscan :
      (initialRightScanAfter A lambda (omegaPrefix env n)).1 =
        A.run (initialRightOmegaWord lambda env) n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [omegaPrefix_succ, initialRightScanAfter_append]
        simp only [initialRightScanStep, initialBlockScanStep]
        rw [ih]
        rfl
  rw [hscan]

theorem exists_finite_initialRightController
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (hexists : ∃ lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      InitialRightForeverAccepts A lambda ∧ InitialRightCloseFeasible A lambda) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, s} In₁
      (NarrowedBlockLabel In₂ In₁
        (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
        (initialRightBlockMonitor A).State),
      NarrowedAllThreadsWin (initialRightBlockMonitor A)
        controller.labeledTree := by
  rcases hexists with ⟨lambda, hforever, hclose⟩
  refine (block_realizable_iff_implementable_controller_unconditional
    (initialRightBlockMonitor A)).mp ?_
  exact ⟨initialRightReceiverStrategy lambda, initialRightSenderStrategy lambda,
    initialRightBlockMonitor_realizable A lambda hforever hclose⟩

end DetParityAutomaton

end DistributedSynthesis
