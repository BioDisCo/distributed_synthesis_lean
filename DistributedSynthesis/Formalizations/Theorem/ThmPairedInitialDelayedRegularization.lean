/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialDelayedHandoff

/-!
# Finite regularization of the delay-one initial handoff

These monitors are the corrected initial-block monitors.  Their parity part
accepts an infinite initial homogeneous block.  Their sticky safety part
checks the paired entry staged by the *current homogeneous boundary round*,
so that it is available if the next round reverses.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## Initial left -/

noncomputable def initialLeftDelayedBlockMonitor :
    BlockRecordMonitor In₁ In₂
      (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂ := by
  classical
  exact {
    State := InitialBlockScan A × Bool
    stateFinite := inferInstance
    initial := ((A.initial, A.initial), true)
    step := fun state letter =>
      let feasible := (pairedEntryRunAutomaton A
        (initialLeftDelayedTarget A state.1 letter)).HasRationalRun
      (initialLeftScanStep A state.1 letter, state.2 && decide feasible)
    priority := fun state => if state.2 then A.priority state.1.1 + 2 else 1
  }

theorem initialLeftDelayedBlockMonitor_run_eq
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hfeasible : InitialLeftDelayedFeasible A lambda)
    (env : Nat -> In₁ × In₂) : ∀ n,
    (initialLeftDelayedBlockMonitor A).run
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
      have h := hfeasible (omegaPrefix env n) (env n)
      simp [initialLeftDelayedBlockMonitor, h]

theorem initialLeftDelayedBlockMonitor_run_shape
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₁ × In₂) : ∀ n, ∃ safe : Bool,
    (initialLeftDelayedBlockMonitor A).run
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
      exact ⟨((initialLeftDelayedBlockMonitor A).step
        (initialLeftScanAfter A lambda (omegaPrefix env n), safe)
        (initialLeftLetterAt lambda (omegaPrefix env n) (env n))).2, rfl⟩

theorem initialLeftDelayedBlockMonitor_safe_false_persists
    (play : Nat -> InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    {N : Nat}
    (hfalse : ((initialLeftDelayedBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n ->
      ((initialLeftDelayedBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((initialLeftDelayedBlockMonitor A).run play (N + k)).2 = false :=
        ih (Nat.le_add_right N k)
      change Bool.and
        ((initialLeftDelayedBlockMonitor A).run play (N + k)).2 _ = false
      rw [ih']
      rfl

/-- Winning the corrected monitor forces feasibility of every staged
delay-one target. -/
theorem initialLeftDelayedFeasible_of_monitorWins
    [Inhabited (In₁ × In₂)]
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (initialLeftDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env)) :
    InitialLeftDelayedFeasible A lambda := by
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
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    have henvN : env past.length = finiteWord[past.length] :=
      omegaOfList_eq_getElem finiteWord past.length hnPrefix
    rw [henvN]
    simp [finiteWord]
  rcases initialLeftDelayedBlockMonitor_run_shape A lambda env past.length with
    ⟨safe, hshape⟩
  have hfalse :
      ((initialLeftDelayedBlockMonitor A).run
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) (past.length + 1)).2 = false := by
    rw [BlockRecordMonitor.run, hshape,
      initialLeft_pairPlay_eq_letterAt lambda env past.length, hpast, hmove]
    simp [initialLeftDelayedBlockMonitor, hnot]
  have hpersist := initialLeftDelayedBlockMonitor_safe_false_persists A
    (pairPlay (initialLeftReceiverStrategy lambda)
      (initialLeftSenderStrategy lambda) env) hfalse
  have heventual : ∀ n, past.length + 1 ≤ n ->
      (initialLeftDelayedBlockMonitor A).priority
        ((initialLeftDelayedBlockMonitor A).run
          (pairPlay (initialLeftReceiverStrategy lambda)
            (initialLeftSenderStrategy lambda) env) n) = 1 := by
    intro n hn
    have hs := hpersist n hn
    change (if ((initialLeftDelayedBlockMonitor A).run
      (pairPlay (initialLeftReceiverStrategy lambda)
        (initialLeftSenderStrategy lambda) env) n).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ _ heventual (hmonitor env)

theorem initialLeftDelayed_conditions_of_monitorWins
    [Inhabited (In₁ × In₂)]
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₁ × In₂,
      (initialLeftDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env)) :
    InitialLeftForeverAccepts A lambda ∧ InitialLeftDelayedFeasible A lambda := by
  have hfeasible := initialLeftDelayedFeasible_of_monitorWins A lambda hmonitor
  refine ⟨?_, hfeasible⟩
  intro env
  have hm := hmonitor env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n => (initialLeftDelayedBlockMonitor A).priority
        ((initialLeftDelayedBlockMonitor A).run
          (pairPlay (initialLeftReceiverStrategy lambda)
            (initialLeftSenderStrategy lambda) env) n)) =
        fun n => A.priority (A.run (initialLeftOmegaWord lambda env) n) + 2 := by
    funext n
    rw [initialLeftDelayedBlockMonitor_run_eq A lambda hfeasible env n]
    simp [initialLeftDelayedBlockMonitor]
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

theorem initialLeftDelayedBlockMonitor_realizable
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : InitialLeftForeverAccepts A lambda)
    (hfeasible : InitialLeftDelayedFeasible A lambda) :
    ∀ env : Nat -> In₁ × In₂,
      (initialLeftDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialLeftReceiverStrategy lambda)
          (initialLeftSenderStrategy lambda) env) := by
  intro env
  have hparity : NatSeqMinEvenParity
      (fun n => A.priority (A.run (initialLeftOmegaWord lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr (hforever env)
  unfold BlockRecordMonitor.WinsPlay
  convert hparity using 1
  funext n
  rw [initialLeftDelayedBlockMonitor_run_eq A lambda hfeasible env n]
  simp [initialLeftDelayedBlockMonitor]
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

/-- The corrected initial-left block has a finite controller whenever its
delay-one semantic witness exists. -/
theorem exists_finite_initialLeftDelayedController
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (hexists : ∃ lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      InitialLeftForeverAccepts A lambda ∧ InitialLeftDelayedFeasible A lambda) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, s} In₂
      (NarrowedBlockLabel In₁ In₂
        (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
        (initialLeftDelayedBlockMonitor A).State),
      NarrowedAllThreadsWin (initialLeftDelayedBlockMonitor A)
        controller.labeledTree := by
  rcases hexists with ⟨lambda, hforever, hfeasible⟩
  refine (block_realizable_iff_implementable_controller_unconditional
    (initialLeftDelayedBlockMonitor A)).mp ?_
  exact ⟨initialLeftReceiverStrategy lambda, initialLeftSenderStrategy lambda,
    initialLeftDelayedBlockMonitor_realizable A lambda hforever hfeasible⟩

/-- A winning strategy supplies the corrected finite initial-left
controller. -/
theorem exists_finite_initialLeftDelayedController_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, s} In₂
      (NarrowedBlockLabel In₁ In₂
        (InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
        (initialLeftDelayedBlockMonitor A).State),
      NarrowedAllThreadsWin (initialLeftDelayedBlockMonitor A)
        controller.labeledTree :=
  exists_finite_initialLeftDelayedController A ⟨initialLeftLambdaOfStrategy strategy,
    initialLeftForeverAccepts_lambdaOfStrategy A strategy hwin,
    initialLeftDelayedFeasible_lambdaOfStrategy A strategy hwin basis⟩

/-! ## Initial right mirror -/

noncomputable def initialRightDelayedBlockMonitor :
    BlockRecordMonitor In₂ In₁
      (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁ := by
  classical
  exact {
    State := InitialBlockScan A × Bool
    stateFinite := inferInstance
    initial := ((A.initial, A.initial), true)
    step := fun state letter =>
      let feasible := (pairedEntryRunAutomaton A
        (initialRightDelayedTarget A state.1 letter)).HasRationalRun
      (initialRightScanStep A state.1 letter, state.2 && decide feasible)
    priority := fun state => if state.2 then A.priority state.1.1 + 2 else 1
  }

theorem initialRightDelayedBlockMonitor_run_eq
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hfeasible : InitialRightDelayedFeasible A lambda)
    (env : Nat -> In₂ × In₁) : ∀ n,
    (initialRightDelayedBlockMonitor A).run
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
      have h := hfeasible (omegaPrefix env n) (env n)
      simp [initialRightDelayedBlockMonitor, h]

theorem initialRightDelayedBlockMonitor_run_shape
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₂ × In₁) : ∀ n, ∃ safe : Bool,
    (initialRightDelayedBlockMonitor A).run
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
      exact ⟨((initialRightDelayedBlockMonitor A).step
        (initialRightScanAfter A lambda (omegaPrefix env n), safe)
        (initialRightLetterAt lambda (omegaPrefix env n) (env n))).2, rfl⟩

theorem initialRightDelayedBlockMonitor_safe_false_persists
    (play : Nat -> InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    {N : Nat}
    (hfalse : ((initialRightDelayedBlockMonitor A).run play N).2 = false) :
    ∀ n, N ≤ n ->
      ((initialRightDelayedBlockMonitor A).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((initialRightDelayedBlockMonitor A).run play (N + k)).2 = false :=
        ih (Nat.le_add_right N k)
      change Bool.and
        ((initialRightDelayedBlockMonitor A).run play (N + k)).2 _ = false
      rw [ih']
      rfl

theorem initialRightDelayedFeasible_of_monitorWins
    [Inhabited (In₂ × In₁)]
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (initialRightDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env)) :
    InitialRightDelayedFeasible A lambda := by
  classical
  intro past move
  by_contra hnot
  let finiteWord := past ++ [move]
  let env : Nat -> In₂ × In₁ := omegaOfList finiteWord
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
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    have henvN : env past.length = finiteWord[past.length] :=
      omegaOfList_eq_getElem finiteWord past.length hnPrefix
    rw [henvN]
    simp [finiteWord]
  rcases initialRightDelayedBlockMonitor_run_shape A lambda env past.length with
    ⟨safe, hshape⟩
  have hfalse :
      ((initialRightDelayedBlockMonitor A).run
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) (past.length + 1)).2 = false := by
    rw [BlockRecordMonitor.run, hshape,
      initialRight_pairPlay_eq_letterAt lambda env past.length, hpast, hmove]
    simp [initialRightDelayedBlockMonitor, hnot]
  have hpersist := initialRightDelayedBlockMonitor_safe_false_persists A
    (pairPlay (initialRightReceiverStrategy lambda)
      (initialRightSenderStrategy lambda) env) hfalse
  have heventual : ∀ n, past.length + 1 ≤ n ->
      (initialRightDelayedBlockMonitor A).priority
        ((initialRightDelayedBlockMonitor A).run
          (pairPlay (initialRightReceiverStrategy lambda)
            (initialRightSenderStrategy lambda) env) n) = 1 := by
    intro n hn
    have hs := hpersist n hn
    change (if ((initialRightDelayedBlockMonitor A).run
      (pairPlay (initialRightReceiverStrategy lambda)
        (initialRightSenderStrategy lambda) env) n).2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ _ heventual (hmonitor env)

theorem initialRightDelayed_conditions_of_monitorWins
    [Inhabited (In₂ × In₁)]
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hmonitor : ∀ env : Nat -> In₂ × In₁,
      (initialRightDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env)) :
    InitialRightForeverAccepts A lambda ∧ InitialRightDelayedFeasible A lambda := by
  have hfeasible := initialRightDelayedFeasible_of_monitorWins A lambda hmonitor
  refine ⟨?_, hfeasible⟩
  intro env
  have hm := hmonitor env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n => (initialRightDelayedBlockMonitor A).priority
        ((initialRightDelayedBlockMonitor A).run
          (pairPlay (initialRightReceiverStrategy lambda)
            (initialRightSenderStrategy lambda) env) n)) =
        fun n => A.priority (A.run (initialRightOmegaWord lambda env) n) + 2 := by
    funext n
    rw [initialRightDelayedBlockMonitor_run_eq A lambda hfeasible env n]
    simp [initialRightDelayedBlockMonitor]
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

theorem initialRightDelayedBlockMonitor_realizable
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : InitialRightForeverAccepts A lambda)
    (hfeasible : InitialRightDelayedFeasible A lambda) :
    ∀ env : Nat -> In₂ × In₁,
      (initialRightDelayedBlockMonitor A).WinsPlay
        (pairPlay (initialRightReceiverStrategy lambda)
          (initialRightSenderStrategy lambda) env) := by
  intro env
  have hparity : NatSeqMinEvenParity
      (fun n => A.priority (A.run (initialRightOmegaWord lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr (hforever env)
  unfold BlockRecordMonitor.WinsPlay
  convert hparity using 1
  funext n
  rw [initialRightDelayedBlockMonitor_run_eq A lambda hfeasible env n]
  simp [initialRightDelayedBlockMonitor]
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

theorem exists_finite_initialRightDelayedController
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (hexists : ∃ lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      InitialRightForeverAccepts A lambda ∧ InitialRightDelayedFeasible A lambda) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, s} In₁
      (NarrowedBlockLabel In₂ In₁
        (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
        (initialRightDelayedBlockMonitor A).State),
      NarrowedAllThreadsWin (initialRightDelayedBlockMonitor A)
        controller.labeledTree := by
  rcases hexists with ⟨lambda, hforever, hfeasible⟩
  refine (block_realizable_iff_implementable_controller_unconditional
    (initialRightDelayedBlockMonitor A)).mp ?_
  exact ⟨initialRightReceiverStrategy lambda, initialRightSenderStrategy lambda,
    initialRightDelayedBlockMonitor_realizable A lambda hforever hfeasible⟩

theorem exists_finite_initialRightDelayedController_of_winning
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A state).RationalRunBasis) :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, s} In₁
      (NarrowedBlockLabel In₂ In₁
        (InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
        (initialRightDelayedBlockMonitor A).State),
      NarrowedAllThreadsWin (initialRightDelayedBlockMonitor A)
        controller.labeledTree :=
  exists_finite_initialRightDelayedController A ⟨initialRightLambdaOfStrategy strategy,
    initialRightForeverAccepts_lambdaOfStrategy A strategy hwin,
    initialRightDelayedFeasible_lambdaOfStrategy A strategy hwin basis⟩

end DetParityAutomaton

end DistributedSynthesis
