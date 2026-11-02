/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedInitialRegularization

/-!
# Initial-block regularization carrying profiled guarded sources

This is the finite initial seam required by the profiled recurrent bank.  The
informed output carries a profiled target and the old overlap table.  The
monitor checks that erasing the target gives the concrete delayed DPA state,
that its profiled root-guard automaton has a rational run, and that the pending
overlap table agrees with the next physical output.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 300000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- Finite data staged after an initial-left boundary. -/
abbrev ProfiledGuardedRightEntryData :=
  PairedProfiledTreeState A ×
    ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)

/-- Physical initial-left output plus its profiled guarded source. -/
abbrev ProfiledGuardedInitialLeftReceiverOutput :=
  InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    ProfiledGuardedRightEntryData A

def profiledGuardedInitialLeftPhysicalLetter
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) Out₂) :
    InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.1, letter.2.2)

def profiledGuardedInitialLeftOverlapOK
    (pending : Option (ProfiledGuardedRightEntryData A))
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) Out₂) : Prop :=
  match pending with
  | none => True
  | some source =>
      source.2 (letter.1.2, letter.1.1) = letter.2.1.1.informedOne

/-- Initial-left monitor whose certificates retain the recurrent profile. -/
noncomputable def profiledGuardedInitialLeftBlockMonitor :
    BlockRecordMonitor In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) Out₂ := by
  classical
  exact {
    State := (InitialBlockScan A ×
      Option (ProfiledGuardedRightEntryData A)) × Bool
    stateFinite := inferInstance
    initial := (((A.initial, A.initial), none), true)
    step := fun state letter =>
      let physical := profiledGuardedInitialLeftPhysicalLetter A letter
      let source := letter.2.1.2
      let targetOK := erasePairedProfiledState A source.1 =
        initialLeftDelayedTarget A state.1.1 physical
      let feasible :=
        (rightProfiledGuardedAutomaton A source.1 source.2).HasRationalRun
      let overlapOK := profiledGuardedInitialLeftOverlapOK A state.1.2 letter
      ((initialLeftScanStep A state.1.1 physical, some source),
        state.2 && decide targetOK && decide feasible && decide overlapOK)
    priority := fun state => if state.2 then A.priority state.1.1.1 + 2 else 1
  }

section LeftWitness

variable [Inhabited In₁] [Inhabited In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (profiledBasis : ∀ target overlap,
    (rightProfiledGuardedAutomaton A target overlap).RationalRunBasis)

noncomputable def profiledGuardedInitialLeftSource
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledGuardedRightEntrySource A :=
  ⟨(initialLeftProfiledTarget A strategy past move,
      initialLeftNextBothProfile strategy past move),
    initialLeft_profiledGuardedHasRationalRun A strategy hwin past move
      (profiledBasis _ _)⟩

noncomputable def profiledGuardedInitialLeftReceiverStrategy :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledGuardedInitialLeftReceiverOutput A) :=
  fun past move =>
    let lambda := initialLeftLambdaOfStrategy strategy
    (⟨lambda.informedOne past move, lambda.reversingOne past move,
        lambda.reversingTwo past move⟩,
      (profiledGuardedInitialLeftSource A strategy hwin profiledBasis
        past move).1)

noncomputable def profiledGuardedInitialLeftPending
    (env : Nat → In₁ × In₂) : Nat →
      Option (ProfiledGuardedRightEntryData A)
  | 0 => none
  | n + 1 => some
      (profiledGuardedInitialLeftSource A strategy hwin profiledBasis
        (omegaPrefix env n) (env n)).1

theorem profiledGuardedInitialLeft_pairPlay_physical
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledGuardedInitialLeftPhysicalLetter A
      (pairPlay
        (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
          profiledBasis)
        (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
        env n) =
      initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
        (omegaPrefix env n) (env n) := by
  simp [profiledGuardedInitialLeftPhysicalLetter, pairPlay, treePlay,
    treeOfPair, blockLabelApply, branchNode_eq_omegaPrefix,
    profiledGuardedInitialLeftReceiverStrategy, initialLeftSenderStrategy,
    initialLeftLetterAt]

theorem profiledGuardedInitialLeft_pairPlay_source
    (env : Nat → In₁ × In₂) (n : Nat) :
    (pairPlay
      (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
        profiledBasis)
      (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
      env n).2.1.2 =
      (profiledGuardedInitialLeftSource A strategy hwin profiledBasis
        (omegaPrefix env n) (env n)).1 := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix, profiledGuardedInitialLeftReceiverStrategy]

theorem profiledGuardedInitialLeft_overlapOK
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledGuardedInitialLeftOverlapOK A
      (profiledGuardedInitialLeftPending A strategy hwin profiledBasis env n)
      (pairPlay
        (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
          profiledBasis)
        (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
        env n) := by
  cases n with
  | zero => trivial
  | succ n =>
      simp only [profiledGuardedInitialLeftPending,
        profiledGuardedInitialLeftOverlapOK,
        profiledGuardedInitialLeftSource]
      have hphysical := profiledGuardedInitialLeft_pairPlay_physical
        A strategy hwin profiledBasis env (n + 1)
      have hmove := congrArg (fun letter => letter.1) hphysical
      have hout := congrArg (fun letter => letter.2.1.informedOne) hphysical
      have hmove' :
          (pairPlay
            (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
              profiledBasis)
            (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
            env (n + 1)).1 = env (n + 1) := by
        simpa [profiledGuardedInitialLeftPhysicalLetter,
          initialLeftLetterAt] using hmove
      have hout' :
          (pairPlay
            (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
              profiledBasis)
            (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
            env (n + 1)).2.1.1.informedOne =
            (initialLeftLambdaOfStrategy strategy).informedOne
              (omegaPrefix env (n + 1)) (env (n + 1)) := by
        simpa [profiledGuardedInitialLeftPhysicalLetter,
          initialLeftLetterAt] using hout
      rw [hmove', hout']
      change initialLeftNextBothProfile strategy (omegaPrefix env n) (env n)
          ((env (n + 1)).2, (env (n + 1)).1) =
        (initialLeftLambdaOfStrategy strategy).informedOne
          (omegaPrefix env (n + 1)) (env (n + 1))
      rw [omegaPrefix_succ]
      rfl

theorem profiledGuardedInitialLeftBlockMonitor_run_eq
    (env : Nat → In₁ × In₂) : ∀ n,
    (profiledGuardedInitialLeftBlockMonitor A).run
        (pairPlay
          (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
            profiledBasis)
          (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
          env) n =
      ((initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy)
          (omegaPrefix env n),
        profiledGuardedInitialLeftPending A strategy hwin profiledBasis env n),
        true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [profiledGuardedInitialLeftBlockMonitor]
      rw [profiledGuardedInitialLeft_pairPlay_physical
        A strategy hwin profiledBasis env n]
      rw [profiledGuardedInitialLeft_pairPlay_source
        A strategy hwin profiledBasis env n]
      let source := profiledGuardedInitialLeftSource A strategy hwin
        profiledBasis (omegaPrefix env n) (env n)
      have htarget : erasePairedProfiledState A source.1.1 =
          initialLeftDelayedTarget A
            (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy)
              (omegaPrefix env n))
            (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
              (omegaPrefix env n) (env n)) := by
        change (initialLeftProfiledMemory A strategy
          (omegaPrefix env n) (env n)).toTreeState = _
        exact (initialLeftDelayedTarget_lambdaOfStrategy A strategy
          (omegaPrefix env n) (env n)).symm
      have hfeasible :
          (rightProfiledGuardedAutomaton A source.1.1 source.1.2).HasRationalRun :=
        source.2
      have hoverlap := profiledGuardedInitialLeft_overlapOK
        A strategy hwin profiledBasis env n
      change
        ((initialLeftScanStep A
            (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy)
              (omegaPrefix env n))
            (initialLeftLetterAt (initialLeftLambdaOfStrategy strategy)
              (omegaPrefix env n) (env n)), some source.1),
          true && decide _ && decide _ && decide _) = _
      rw [decide_eq_true htarget, decide_eq_true hfeasible,
        decide_eq_true hoverlap]
      simp only [Bool.true_and]
      rw [omegaPrefix_succ, initialLeftScanAfter_append]
      rfl

theorem profiledGuardedInitialLeftBlockMonitor_wins
    (env : Nat → In₁ × In₂) :
    (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
      (pairPlay
        (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
          profiledBasis)
        (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
        env) := by
  have hforever := initialLeftForeverAccepts_lambdaOfStrategy A strategy hwin env
  unfold BlockRecordMonitor.WinsPlay
  have heq :
      (fun n => (profiledGuardedInitialLeftBlockMonitor A).priority
        ((profiledGuardedInitialLeftBlockMonitor A).run
          (pairPlay
            (profiledGuardedInitialLeftReceiverStrategy A strategy hwin
              profiledBasis)
            (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
            env) n)) =
        fun n => A.priority
          (A.run (initialLeftOmegaWord
            (initialLeftLambdaOfStrategy strategy) env) n) + 2 := by
    funext n
    rw [profiledGuardedInitialLeftBlockMonitor_run_eq
      A strategy hwin profiledBasis env n]
    simp only [profiledGuardedInitialLeftBlockMonitor, if_pos, Bool.true_eq]
    congr 2
    have hscan :
        (initialLeftScanAfter A (initialLeftLambdaOfStrategy strategy)
          (omegaPrefix env n)).1 =
          A.run (initialLeftOmegaWord
            (initialLeftLambdaOfStrategy strategy) env) n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [omegaPrefix_succ, initialLeftScanAfter_append]
          simp only [initialLeftScanStep, initialBlockScanStep]
          rw [ih]
          rfl
    exact hscan
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hforever

end LeftWitness

/-- Unconditional finite initial-left controller retaining profiled sources. -/
theorem exists_finite_profiledGuardedInitialLeftController_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (profiledBasis : ∀ target overlap,
      (rightProfiledGuardedAutomaton A target overlap).RationalRunBasis) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (ProfiledGuardedInitialLeftReceiverOutput A) Out₂
        (profiledGuardedInitialLeftBlockMonitor A).State),
      NarrowedAllThreadsWin
        (profiledGuardedInitialLeftBlockMonitor A)
        controller.labeledTree := by
  classical
  let rootData :=
    (profiledGuardedInitialLeftSource A strategy hwin profiledBasis
      [] (default, default)).1
  letI : Inhabited (ProfiledGuardedRightEntryData A) := ⟨rootData⟩
  letI : Inhabited (ProfiledGuardedInitialLeftReceiverOutput A) := inferInstance
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledGuardedInitialLeftBlockMonitor A)).mp
  exact ⟨profiledGuardedInitialLeftReceiverStrategy A strategy hwin profiledBasis,
    initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy),
    profiledGuardedInitialLeftBlockMonitor_wins A strategy hwin profiledBasis⟩

/-! ## Initial-right / process-two mirror -/

abbrev ProfiledGuardedLeftEntryData :=
  PairedProfiledTreeState A ×
    ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)

abbrev ProfiledGuardedInitialRightReceiverOutput :=
  InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    ProfiledGuardedLeftEntryData A

def profiledGuardedInitialRightPhysicalLetter
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) Out₁) :
    InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (letter.1, letter.2.1.1, letter.2.2)

def profiledGuardedInitialRightOverlapOK
    (pending : Option (ProfiledGuardedLeftEntryData A))
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) Out₁) : Prop :=
  match pending with
  | none => True
  | some source =>
      source.2 (letter.1.2, letter.1.1) = letter.2.1.1.informedTwo

noncomputable def profiledGuardedInitialRightBlockMonitor :
    BlockRecordMonitor In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) Out₁ := by
  classical
  exact {
    State := (InitialBlockScan A ×
      Option (ProfiledGuardedLeftEntryData A)) × Bool
    stateFinite := inferInstance
    initial := (((A.initial, A.initial), none), true)
    step := fun state letter =>
      let physical := profiledGuardedInitialRightPhysicalLetter A letter
      let source := letter.2.1.2
      let targetOK := erasePairedProfiledState A source.1 =
        initialRightDelayedTarget A state.1.1 physical
      let feasible :=
        (leftProfiledGuardedAutomaton A source.1 source.2).HasRationalRun
      let overlapOK := profiledGuardedInitialRightOverlapOK A state.1.2 letter
      ((initialRightScanStep A state.1.1 physical, some source),
        state.2 && decide targetOK && decide feasible && decide overlapOK)
    priority := fun state => if state.2 then A.priority state.1.1.1 + 2 else 1
  }

section RightWitness

variable [Inhabited In₁] [Inhabited In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (profiledBasis : ∀ target overlap,
    (leftProfiledGuardedAutomaton A target overlap).RationalRunBasis)

noncomputable def profiledGuardedInitialRightSource
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledGuardedLeftEntrySource A :=
  ⟨(initialRightProfiledTarget A strategy past move,
      initialRightNextBothProfile strategy past move),
    initialRight_profiledGuardedHasRationalRun A strategy hwin past move
      (profiledBasis _ _)⟩

noncomputable def profiledGuardedInitialRightReceiverStrategy :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledGuardedInitialRightReceiverOutput A) :=
  fun past move =>
    let lambda := initialRightLambdaOfStrategy strategy
    (⟨lambda.informedTwo past move, lambda.reversingOne past move,
        lambda.reversingTwo past move⟩,
      (profiledGuardedInitialRightSource A strategy hwin profiledBasis
        past move).1)

noncomputable def profiledGuardedInitialRightPending
    (env : Nat → In₂ × In₁) : Nat →
      Option (ProfiledGuardedLeftEntryData A)
  | 0 => none
  | n + 1 => some
      (profiledGuardedInitialRightSource A strategy hwin profiledBasis
        (omegaPrefix env n) (env n)).1

theorem profiledGuardedInitialRight_pairPlay_physical
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledGuardedInitialRightPhysicalLetter A
      (pairPlay
        (profiledGuardedInitialRightReceiverStrategy A strategy hwin
          profiledBasis)
        (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
        env n) =
      initialRightLetterAt (initialRightLambdaOfStrategy strategy)
        (omegaPrefix env n) (env n) := by
  simp [profiledGuardedInitialRightPhysicalLetter, pairPlay, treePlay,
    treeOfPair, blockLabelApply, branchNode_eq_omegaPrefix,
    profiledGuardedInitialRightReceiverStrategy, initialRightSenderStrategy,
    initialRightLetterAt]

theorem profiledGuardedInitialRight_pairPlay_source
    (env : Nat → In₂ × In₁) (n : Nat) :
    (pairPlay
      (profiledGuardedInitialRightReceiverStrategy A strategy hwin
        profiledBasis)
      (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
      env n).2.1.2 =
      (profiledGuardedInitialRightSource A strategy hwin profiledBasis
        (omegaPrefix env n) (env n)).1 := by
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix, profiledGuardedInitialRightReceiverStrategy]

theorem profiledGuardedInitialRight_overlapOK
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledGuardedInitialRightOverlapOK A
      (profiledGuardedInitialRightPending A strategy hwin profiledBasis env n)
      (pairPlay
        (profiledGuardedInitialRightReceiverStrategy A strategy hwin
          profiledBasis)
        (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
        env n) := by
  cases n with
  | zero => trivial
  | succ n =>
      simp only [profiledGuardedInitialRightPending,
        profiledGuardedInitialRightOverlapOK,
        profiledGuardedInitialRightSource]
      have hphysical := profiledGuardedInitialRight_pairPlay_physical
        A strategy hwin profiledBasis env (n + 1)
      have hmove := congrArg (fun letter => letter.1) hphysical
      have hout := congrArg (fun letter => letter.2.1.informedTwo) hphysical
      have hmove' :
          (pairPlay
            (profiledGuardedInitialRightReceiverStrategy A strategy hwin
              profiledBasis)
            (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
            env (n + 1)).1 = env (n + 1) := by
        simpa [profiledGuardedInitialRightPhysicalLetter,
          initialRightLetterAt] using hmove
      have hout' :
          (pairPlay
            (profiledGuardedInitialRightReceiverStrategy A strategy hwin
              profiledBasis)
            (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
            env (n + 1)).2.1.1.informedTwo =
            (initialRightLambdaOfStrategy strategy).informedTwo
              (omegaPrefix env (n + 1)) (env (n + 1)) := by
        simpa [profiledGuardedInitialRightPhysicalLetter,
          initialRightLetterAt] using hout
      rw [hmove', hout']
      change initialRightNextBothProfile strategy (omegaPrefix env n) (env n)
          ((env (n + 1)).2, (env (n + 1)).1) =
        (initialRightLambdaOfStrategy strategy).informedTwo
          (omegaPrefix env (n + 1)) (env (n + 1))
      rw [omegaPrefix_succ]
      rfl

theorem profiledGuardedInitialRightBlockMonitor_run_eq
    (env : Nat → In₂ × In₁) : ∀ n,
    (profiledGuardedInitialRightBlockMonitor A).run
        (pairPlay
          (profiledGuardedInitialRightReceiverStrategy A strategy hwin
            profiledBasis)
          (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
          env) n =
      ((initialRightScanAfter A (initialRightLambdaOfStrategy strategy)
          (omegaPrefix env n),
        profiledGuardedInitialRightPending A strategy hwin profiledBasis env n),
        true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [profiledGuardedInitialRightBlockMonitor]
      rw [profiledGuardedInitialRight_pairPlay_physical
        A strategy hwin profiledBasis env n]
      rw [profiledGuardedInitialRight_pairPlay_source
        A strategy hwin profiledBasis env n]
      let source := profiledGuardedInitialRightSource A strategy hwin
        profiledBasis (omegaPrefix env n) (env n)
      have htarget : erasePairedProfiledState A source.1.1 =
          initialRightDelayedTarget A
            (initialRightScanAfter A (initialRightLambdaOfStrategy strategy)
              (omegaPrefix env n))
            (initialRightLetterAt (initialRightLambdaOfStrategy strategy)
              (omegaPrefix env n) (env n)) := by
        change (initialRightProfiledMemory A strategy
          (omegaPrefix env n) (env n)).toTreeState = _
        exact (initialRightDelayedTarget_lambdaOfStrategy A strategy
          (omegaPrefix env n) (env n)).symm
      have hfeasible :
          (leftProfiledGuardedAutomaton A source.1.1 source.1.2).HasRationalRun :=
        source.2
      have hoverlap := profiledGuardedInitialRight_overlapOK
        A strategy hwin profiledBasis env n
      change
        ((initialRightScanStep A
            (initialRightScanAfter A (initialRightLambdaOfStrategy strategy)
              (omegaPrefix env n))
            (initialRightLetterAt (initialRightLambdaOfStrategy strategy)
              (omegaPrefix env n) (env n)), some source.1),
          true && decide _ && decide _ && decide _) = _
      rw [decide_eq_true htarget, decide_eq_true hfeasible,
        decide_eq_true hoverlap]
      simp only [Bool.true_and]
      rw [omegaPrefix_succ, initialRightScanAfter_append]
      rfl

theorem profiledGuardedInitialRightBlockMonitor_wins
    (env : Nat → In₂ × In₁) :
    (profiledGuardedInitialRightBlockMonitor A).WinsPlay
      (pairPlay
        (profiledGuardedInitialRightReceiverStrategy A strategy hwin
          profiledBasis)
        (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
        env) := by
  have hforever := initialRightForeverAccepts_lambdaOfStrategy A strategy hwin env
  unfold BlockRecordMonitor.WinsPlay
  have heq :
      (fun n => (profiledGuardedInitialRightBlockMonitor A).priority
        ((profiledGuardedInitialRightBlockMonitor A).run
          (pairPlay
            (profiledGuardedInitialRightReceiverStrategy A strategy hwin
              profiledBasis)
            (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
            env) n)) =
        fun n => A.priority
          (A.run (initialRightOmegaWord
            (initialRightLambdaOfStrategy strategy) env) n) + 2 := by
    funext n
    rw [profiledGuardedInitialRightBlockMonitor_run_eq
      A strategy hwin profiledBasis env n]
    simp only [profiledGuardedInitialRightBlockMonitor, if_pos, Bool.true_eq]
    congr 2
    have hscan :
        (initialRightScanAfter A (initialRightLambdaOfStrategy strategy)
          (omegaPrefix env n)).1 =
          A.run (initialRightOmegaWord
            (initialRightLambdaOfStrategy strategy) env) n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [omegaPrefix_succ, initialRightScanAfter_append]
          simp only [initialRightScanStep, initialBlockScanStep]
          rw [ih]
          rfl
    exact hscan
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hforever

end RightWitness

theorem exists_finite_profiledGuardedInitialRightController_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (profiledBasis : ∀ target overlap,
      (leftProfiledGuardedAutomaton A target overlap).RationalRunBasis) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (ProfiledGuardedInitialRightReceiverOutput A) Out₁
        (profiledGuardedInitialRightBlockMonitor A).State),
      NarrowedAllThreadsWin (profiledGuardedInitialRightBlockMonitor A)
        controller.labeledTree := by
  classical
  let rootData :=
    (profiledGuardedInitialRightSource A strategy hwin profiledBasis
      [] (default, default)).1
  letI : Inhabited (ProfiledGuardedLeftEntryData A) := ⟨rootData⟩
  letI : Inhabited (ProfiledGuardedInitialRightReceiverOutput A) := inferInstance
  apply (block_realizable_iff_implementable_controller_unconditional
    (profiledGuardedInitialRightBlockMonitor A)).mp
  exact ⟨profiledGuardedInitialRightReceiverStrategy A strategy hwin profiledBasis,
    initialRightSenderStrategy (initialRightLambdaOfStrategy strategy),
    profiledGuardedInitialRightBlockMonitor_wins A strategy hwin profiledBasis⟩

end DetParityAutomaton

end DistributedSynthesis
