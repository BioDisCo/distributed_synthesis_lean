/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.List.GetD
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryBlockRegularization

/-!
# Soundness of finite paired block controllers

The regularization theorem produces a finite narrowed controller.  This file
turns its labels back into the paired lambda used by the macro transition and
proves the two semantic facts needed by the local handoff: an infinite block
is accepting, and every possible staged close is an `Allowed` macro edge.

There is deliberately no strict-leader test here.  The sender component is
one shared table.  The receiver component is indexed only by the finite
monitor state; the two entry rows are values stored in the receiver output
record and are selected later from the receiver's locally observable entry
bit.
-/

namespace DistributedSynthesis

universe u v x y s z

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Extend a finite word arbitrarily to an omega word. -/
def omegaOfList {Move : Type*} [Inhabited Move] (word : List Move) : Nat -> Move :=
  fun n => word.getD n default

@[simp]
theorem omegaOfList_eq_getElem {Move : Type*} [Inhabited Move]
    (word : List Move) (n : Nat) (hn : n < word.length) :
    omegaOfList word n = word[n] := by
  unfold omegaOfList
  exact List.getD_eq_getElem word default hn

theorem omegaPrefix_omegaOfList_length {Move : Type*} [Inhabited Move]
    (word : List Move) :
    omegaPrefix (omegaOfList word) word.length = word := by
  apply List.ext_get
  · simp [omegaPrefix]
  · intro n hnLeft hnRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [omegaPrefix, List.getElem_ofFn]
    exact omegaOfList_eq_getElem word n hnRight

section Right

variable
  {initialState : PairedEntryTreeState A}
  (policy :
    (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
  (code : A.State × A.State) (minimum : A.State)

abbrev RightNarrowedControllerLabel :=
  NarrowedBlockLabel In₂ In₁
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
    (pairedRightBlockMonitor.{u, v, x, y, s, 0}
      A policy code minimum).State

noncomputable abbrev RightPairedMonitor :=
  pairedRightBlockMonitor.{u, v, x, y, s, 0} A policy code minimum

/-- Paired lambda read directly from one narrowed controller tree. -/
noncomputable def pairedRightLambdaOfNarrowed
    (narrowed : List In₁ ->
      RightNarrowedControllerLabel A policy code minimum) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := fun word input => (narrowed word).1 input
  informedLeft := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (RightPairedMonitor A policy code minimum)
        narrowed past) move).informedFirst
  informedBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (RightPairedMonitor A policy code minimum)
        narrowed past) move).informedBoth
  bothOneLeft := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (RightPairedMonitor A policy code minimum)
        narrowed past) move).closingFirst
  bothOneBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (RightPairedMonitor A policy code minimum)
        narrowed past) move).closingBoth

theorem pairedRight_pairPlay_lambdaOfNarrowed
    (narrowed : List In₁ ->
      RightNarrowedControllerLabel A policy code minimum)
    (env : Nat -> In₂ × In₁) :
    pairPlay
        (pairedRightReceiverStrategy
          (pairedRightLambdaOfNarrowed A policy code minimum narrowed))
        (pairedRightSenderStrategy
          (pairedRightLambdaOfNarrowed A policy code minimum narrowed)) env =
      treePlay
        (narrowedInducedTree (RightPairedMonitor A policy code minimum)
          narrowed) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    pairedRightReceiverStrategy, pairedRightSenderStrategy,
    pairedRightLambdaOfNarrowed, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

/-- The monitor run always has the exact universal and scan components;
only the sticky safety bit is left abstract. -/
theorem pairedRightBlockMonitor_run_shape
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₂ × In₁) :
    ∀ n, ∃ safe : Bool,
      (RightPairedMonitor A policy code minimum).run
          (pairPlay (pairedRightReceiverStrategy lambda)
            (pairedRightSenderStrategy lambda) env) n =
        ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n,
          pairedRightScanAfter A code lambda (omegaPrefix env n), safe) := by
  intro n
  classical
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih,
        pairedRight_pairPlay_eq_blockWord lambda env,
        pairedRightBlockWord_eq_letterAt,
        omegaPrefix_succ, pairedRightScanAfter_append]
      refine ⟨((RightPairedMonitor A policy code minimum).step
        ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n,
          pairedRightScanAfter A code lambda (omegaPrefix env n), safe)
        (pairedRightBlockLetterAt lambda (omegaPrefix env n) (env n))).2.2, ?_⟩
      simp [pairedRightBlockMonitor, pairedRightBlockWord_eq_letterAt]

/-- Once the paired monitor's safety bit is false, it stays false. -/
theorem pairedRightBlockMonitor_safe_false_persists
    (play : Nat -> RealizedBlockRound In₂ In₁
      (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁)
    {N : Nat}
    (hfalse : ((RightPairedMonitor A policy code minimum).run play N).2.2 =
      false) :
    ∀ n, N ≤ n ->
      ((RightPairedMonitor A policy code minimum).run play n).2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((RightPairedMonitor A policy code minimum).run play (N + k)).2.2 =
            false := ih (Nat.le_add_right N k)
      change
        (((RightPairedMonitor A policy code minimum).run play (N + k)).2.2 &&
          decide _) = false
      rw [ih']
      rfl

/-- Winning the sticky paired monitor forces every possible close to be an
allowed macro edge. -/
theorem pairedRight_closeSafe_of_monitorWins
    [Inhabited (In₂ × In₁)]
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₂ × In₁,
      (RightPairedMonitor A policy code minimum).WinsPlay
        (pairPlay (pairedRightReceiverStrategy lambda)
          (pairedRightSenderStrategy lambda) env)) :
    PairedRationalPolicy.ProcessOneCloseSafe
      A policy code minimum lambda := by
  intro row past move
  by_contra hnotAllowed
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
  rcases pairedRightBlockMonitor_run_shape A policy code minimum lambda env
      past.length with ⟨safe, hshape⟩
  have hfalse :
      ((RightPairedMonitor A policy code minimum).run
        (pairPlay (pairedRightReceiverStrategy lambda)
          (pairedRightSenderStrategy lambda) env) (past.length + 1)).2.2 = false := by
    have hnotClose :
        ¬ PairedRationalPolicy.Allowed A policy
          (Sum.inr (Sum.inl (code, minimum)))
          (pairedRightCloseTarget A (pairedRightScanAfter A code lambda past)
            row (pairedRightBlockLetterAt lambda past move)) := by
      rw [pairedRightCloseTarget_scanAfter A code lambda past move row]
      exact hnotAllowed
    rw [BlockRecordMonitor.run, hshape,
      pairedRight_pairPlay_eq_blockWord lambda env,
      pairedRightBlockWord_eq_letterAt, hpast, hmove]
    cases row <;> simp_all [RightPairedMonitor, pairedRightBlockMonitor]
  have hpersist := pairedRightBlockMonitor_safe_false_persists
    A policy code minimum
    (pairPlay (pairedRightReceiverStrategy lambda)
      (pairedRightSenderStrategy lambda) env) hfalse
  have heventual : ∀ n, past.length + 1 ≤ n ->
      (RightPairedMonitor A policy code minimum).priority
          ((RightPairedMonitor A policy code minimum).run
            (pairPlay (pairedRightReceiverStrategy lambda)
              (pairedRightSenderStrategy lambda) env) n) = 1 := by
    intro n hn
    have := hpersist n hn
    change
      (if ((RightPairedMonitor A policy code minimum).run
          (pairPlay (pairedRightReceiverStrategy lambda)
            (pairedRightSenderStrategy lambda) env) n).2.2
        then _ else 1) = 1
    rw [this]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ _ heventual (hwin env)

/-- The universal two-row monitor condition implies the original T2
condition for both concrete entry rows. -/
theorem pairedRightForeverAccepts_of_universalDPA
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (huniversal : ∀ env : Nat -> In₂ × In₁,
      (pairedRightThreadSystem A code).universalRunDPA.Accepts
        (pairedRightBlockWord lambda env)) :
    PairedRightForeverAccepts A code lambda := by
  constructor
  · intro env
    let q := pairedRightThreadRun A code lambda env PairedEntryRow.first
    have hrun : (pairedRightThreadSystem A code).IsRun
        (pairedRightBlockWord lambda env) q := by
      constructor
      · rfl
      · intro n
        exact ⟨PairedEntryRow.first, by cases n <;> rfl⟩
    have hq := ((pairedRightThreadSystem A code).universalRunDPA_accepts_iff
      (pairedRightBlockWord lambda env)).mp (huniversal env) q hrun
    have hshift : NatSeqMinEvenParity
        (fun n => A.priority (A.runFrom code.1
          (pairedRightOmegaWord lambda.blind lambda.informedLeft env) (n + 1))) := by
      convert (natSeqMinEvenParity_shift
        (fun n => (pairedRightThreadSystem A code).priority (q n)) 1).mpr hq
        using 1
      simp [q, pairedRightThreadRun, pairedRightThreadSystem,
          Nat.add_comm]
    exact (natSeqMinEvenParity_shift
      (fun n => A.priority (A.runFrom code.1
        (pairedRightOmegaWord lambda.blind lambda.informedLeft env) n)) 1).mp
      (by simpa [Nat.add_comm] using hshift)
  · intro env
    let q := pairedRightThreadRun A code lambda env PairedEntryRow.both
    have hrun : (pairedRightThreadSystem A code).IsRun
        (pairedRightBlockWord lambda env) q := by
      constructor
      · rfl
      · intro n
        exact ⟨PairedEntryRow.both, by cases n <;> rfl⟩
    have hq := ((pairedRightThreadSystem A code).universalRunDPA_accepts_iff
      (pairedRightBlockWord lambda env)).mp (huniversal env) q hrun
    have hshift : NatSeqMinEvenParity
        (fun n => A.priority (A.runFrom code.2
          (pairedRightOmegaWord lambda.blind lambda.informedBoth env) (n + 1))) := by
      convert (natSeqMinEvenParity_shift
        (fun n => (pairedRightThreadSystem A code).priority (q n)) 1).mpr hq
        using 1
      simp [q, pairedRightThreadRun, pairedRightThreadSystem,
          Nat.add_comm]
    exact (natSeqMinEvenParity_shift
      (fun n => A.priority (A.runFrom code.2
        (pairedRightOmegaWord lambda.blind lambda.informedBoth env) n)) 1).mp
      (by simpa [Nat.add_comm] using hshift)

/-- Soundness of one implementable process-one block controller. -/
theorem pairedRightController_sound
    [Inhabited (In₂ × In₁)]
    [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (controller : TransitionRationalTree.{u, max u v x y s, z} In₁
      (RightNarrowedControllerLabel A policy code minimum))
    (hthreads : NarrowedAllThreadsWin
      (RightPairedMonitor A policy code minimum) controller.labeledTree) :
    let lambda := pairedRightLambdaOfNarrowed A policy code minimum
      controller.labeledTree
    PairedRightForeverAccepts A code lambda ∧
      PairedRationalPolicy.ProcessOneCloseSafe
        A policy code minimum lambda := by
  let lambda := pairedRightLambdaOfNarrowed A policy code minimum
    controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    (RightPairedMonitor A policy code minimum) hthreads
  have hmonitor : ∀ env : Nat -> In₂ × In₁,
      (RightPairedMonitor A policy code minimum).WinsPlay
        (pairPlay (pairedRightReceiverStrategy lambda)
          (pairedRightSenderStrategy lambda) env) := by
    intro env
    have hplay := ((RightPairedMonitor A policy code minimum).lift_winningTree_iff
      (narrowedInducedTree (RightPairedMonitor A policy code minimum)
        controller.labeledTree)).mp htree env
    rw [pairedRight_pairPlay_lambdaOfNarrowed A policy code minimum
      controller.labeledTree env]
    exact hplay
  have hclose := pairedRight_closeSafe_of_monitorWins
    A policy code minimum lambda hmonitor
  refine ⟨?_, hclose⟩
  apply pairedRightForeverAccepts_of_universalDPA A code lambda
  intro env
  have hm := hmonitor env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n =>
        (RightPairedMonitor A policy code minimum).priority
          ((RightPairedMonitor A policy code minimum).run
            (pairPlay (pairedRightReceiverStrategy lambda)
              (pairedRightSenderStrategy lambda) env) n)) =
      (fun n =>
        (pairedRightThreadSystem A code).universalRunDPA.priority
          ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n) + 2) := by
    funext n
    rw [pairedRightBlockMonitor_run_eq A policy code minimum lambda hclose env n]
    rfl
  rw [heq] at hm
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hm

end Right

section Left

variable
  {initialState : PairedEntryTreeState A}
  (policy :
    (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
  (code : A.State × A.State) (minimum : A.State)

abbrev LeftNarrowedControllerLabel :=
  NarrowedBlockLabel In₁ In₂
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
    (pairedLeftBlockMonitor.{u, v, x, y, s, 0}
      A policy code minimum).State

noncomputable abbrev LeftPairedMonitor :=
  pairedLeftBlockMonitor.{u, v, x, y, s, 0} A policy code minimum

/-- Paired lambda read directly from one narrowed controller tree. -/
noncomputable def pairedLeftLambdaOfNarrowed
    (narrowed : List In₂ ->
      LeftNarrowedControllerLabel A policy code minimum) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := fun word input => (narrowed word).1 input
  informedRight := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (LeftPairedMonitor A policy code minimum)
        narrowed past) move).informedFirst
  informedBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (LeftPairedMonitor A policy code minimum)
        narrowed past) move).informedBoth
  bothTwoRight := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (LeftPairedMonitor A policy code minimum)
        narrowed past) move).closingFirst
  bothTwoBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (LeftPairedMonitor A policy code minimum)
        narrowed past) move).closingBoth

theorem pairedLeft_pairPlay_lambdaOfNarrowed
    (narrowed : List In₂ ->
      LeftNarrowedControllerLabel A policy code minimum)
    (env : Nat -> In₁ × In₂) :
    pairPlay
        (pairedLeftReceiverStrategy
          (pairedLeftLambdaOfNarrowed A policy code minimum narrowed))
        (pairedLeftSenderStrategy
          (pairedLeftLambdaOfNarrowed A policy code minimum narrowed)) env =
      treePlay
        (narrowedInducedTree (LeftPairedMonitor A policy code minimum)
          narrowed) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    pairedLeftReceiverStrategy, pairedLeftSenderStrategy,
    pairedLeftLambdaOfNarrowed, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

/-- The monitor run always has the exact universal and scan components;
only the sticky safety bit is left abstract. -/
theorem pairedLeftBlockMonitor_run_shape
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₁ × In₂) :
    ∀ n, ∃ safe : Bool,
      (LeftPairedMonitor A policy code minimum).run
          (pairPlay (pairedLeftReceiverStrategy lambda)
            (pairedLeftSenderStrategy lambda) env) n =
        ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n,
          pairedLeftScanAfter A code lambda (omegaPrefix env n), safe) := by
  intro n
  classical
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih,
        pairedLeft_pairPlay_eq_blockWord lambda env,
        omegaPrefix_succ, pairedLeftScanAfter_append]
      refine ⟨((LeftPairedMonitor A policy code minimum).step
        ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n,
          pairedLeftScanAfter A code lambda (omegaPrefix env n), safe)
        (pairedLeftBlockLetterAt lambda (omegaPrefix env n) (env n))).2.2, ?_⟩
      simp [pairedLeftBlockMonitor, pairedLeftBlockWord]

/-- Once the paired monitor's safety bit is false, it stays false. -/
theorem pairedLeftBlockMonitor_safe_false_persists
    (play : Nat -> RealizedBlockRound In₁ In₂
      (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂)
    {N : Nat}
    (hfalse : ((LeftPairedMonitor A policy code minimum).run play N).2.2 =
      false) :
    ∀ n, N ≤ n ->
      ((LeftPairedMonitor A policy code minimum).run play n).2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((LeftPairedMonitor A policy code minimum).run play (N + k)).2.2 =
            false := ih (Nat.le_add_right N k)
      change
        (((LeftPairedMonitor A policy code minimum).run play (N + k)).2.2 &&
          decide _) = false
      rw [ih']
      rfl

/-- Winning the sticky paired monitor forces every possible close to be an
allowed macro edge. -/
theorem pairedLeft_closeSafe_of_monitorWins
    [Inhabited (In₁ × In₂)]
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₁ × In₂,
      (LeftPairedMonitor A policy code minimum).WinsPlay
        (pairPlay (pairedLeftReceiverStrategy lambda)
          (pairedLeftSenderStrategy lambda) env)) :
    PairedRationalPolicy.ProcessTwoCloseSafe
      A policy code minimum lambda := by
  intro row past move
  by_contra hnotAllowed
  let finiteWord := past ++ [move]
  let env : Nat -> In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix, finiteWord]
    · intro n hnLeft hnLeft
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      have henvN : env n = finiteWord[n] :=
        omegaOfList_eq_getElem finiteWord n hnPrefix
      rw [henvN]
      simp [finiteWord, hnLeft]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    have henvN : env past.length = finiteWord[past.length] :=
      omegaOfList_eq_getElem finiteWord past.length hnPrefix
    rw [henvN]
    simp [finiteWord]
  rcases pairedLeftBlockMonitor_run_shape A policy code minimum lambda env
      past.length with ⟨safe, hshape⟩
  have hfalse :
      ((LeftPairedMonitor A policy code minimum).run
        (pairPlay (pairedLeftReceiverStrategy lambda)
          (pairedLeftSenderStrategy lambda) env) (past.length + 1)).2.2 = false := by
    have hnotClose :
        ¬ PairedRationalPolicy.Allowed A policy
          (Sum.inr (Sum.inr (code, minimum)))
          (pairedLeftCloseTarget A (pairedLeftScanAfter A code lambda past)
            row (pairedLeftBlockLetterAt lambda past move)) := by
      rw [pairedLeftCloseTarget_scanAfter A code lambda past move row]
      exact hnotAllowed
    rw [BlockRecordMonitor.run, hshape,
      pairedLeft_pairPlay_eq_blockWord lambda env]
    simp only [pairedLeftBlockWord]
    rw [hpast, hmove]
    cases row <;> simp_all [LeftPairedMonitor, pairedLeftBlockMonitor]
  have hpersist := pairedLeftBlockMonitor_safe_false_persists
    A policy code minimum
    (pairPlay (pairedLeftReceiverStrategy lambda)
      (pairedLeftSenderStrategy lambda) env) hfalse
  have heventual : ∀ n, past.length + 1 ≤ n ->
      (LeftPairedMonitor A policy code minimum).priority
          ((LeftPairedMonitor A policy code minimum).run
            (pairPlay (pairedLeftReceiverStrategy lambda)
              (pairedLeftSenderStrategy lambda) env) n) = 1 := by
    intro n hn
    have := hpersist n hn
    change
      (if ((LeftPairedMonitor A policy code minimum).run
          (pairPlay (pairedLeftReceiverStrategy lambda)
            (pairedLeftSenderStrategy lambda) env) n).2.2
        then _ else 1) = 1
    rw [this]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ _ heventual (hwin env)

/-- The universal two-row monitor condition implies the original T2
condition for both concrete entry rows. -/
theorem pairedLeftForeverAccepts_of_universalDPA
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (huniversal : ∀ env : Nat -> In₁ × In₂,
      (pairedLeftThreadSystem A code).universalRunDPA.Accepts
        (pairedLeftBlockWord lambda env)) :
    PairedLeftForeverAccepts A code lambda := by
  constructor
  · intro env
    let q := pairedLeftThreadRun A code lambda env PairedEntryRow.first
    have hrun : (pairedLeftThreadSystem A code).IsRun
        (pairedLeftBlockWord lambda env) q := by
      constructor
      · rfl
      · intro n
        exact ⟨PairedEntryRow.first, by cases n <;> rfl⟩
    have hq := ((pairedLeftThreadSystem A code).universalRunDPA_accepts_iff
      (pairedLeftBlockWord lambda env)).mp (huniversal env) q hrun
    have hshift : NatSeqMinEvenParity
        (fun n => A.priority (A.runFrom code.1
          (pairedLeftOmegaWord lambda.blind lambda.informedRight env) (n + 1))) := by
      convert (natSeqMinEvenParity_shift
        (fun n => (pairedLeftThreadSystem A code).priority (q n)) 1).mpr hq
        using 1
      simp [q, pairedLeftThreadRun, pairedLeftThreadSystem,
          Nat.add_comm]
    exact (natSeqMinEvenParity_shift
      (fun n => A.priority (A.runFrom code.1
        (pairedLeftOmegaWord lambda.blind lambda.informedRight env) n)) 1).mp
      (by simpa [Nat.add_comm] using hshift)
  · intro env
    let q := pairedLeftThreadRun A code lambda env PairedEntryRow.both
    have hrun : (pairedLeftThreadSystem A code).IsRun
        (pairedLeftBlockWord lambda env) q := by
      constructor
      · rfl
      · intro n
        exact ⟨PairedEntryRow.both, by cases n <;> rfl⟩
    have hq := ((pairedLeftThreadSystem A code).universalRunDPA_accepts_iff
      (pairedLeftBlockWord lambda env)).mp (huniversal env) q hrun
    have hshift : NatSeqMinEvenParity
        (fun n => A.priority (A.runFrom code.2
          (pairedLeftOmegaWord lambda.blind lambda.informedBoth env) (n + 1))) := by
      convert (natSeqMinEvenParity_shift
        (fun n => (pairedLeftThreadSystem A code).priority (q n)) 1).mpr hq
        using 1
      simp [q, pairedLeftThreadRun, pairedLeftThreadSystem,
          Nat.add_comm]
    exact (natSeqMinEvenParity_shift
      (fun n => A.priority (A.runFrom code.2
        (pairedLeftOmegaWord lambda.blind lambda.informedBoth env) n)) 1).mp
      (by simpa [Nat.add_comm] using hshift)

/-- Soundness of one implementable process-one block controller. -/
theorem pairedLeftController_sound
    [Inhabited (In₁ × In₂)]
    [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (controller : TransitionRationalTree.{v, max u v x y s, z} In₂
      (LeftNarrowedControllerLabel A policy code minimum))
    (hthreads : NarrowedAllThreadsWin
      (LeftPairedMonitor A policy code minimum) controller.labeledTree) :
    let lambda := pairedLeftLambdaOfNarrowed A policy code minimum
      controller.labeledTree
    PairedLeftForeverAccepts A code lambda ∧
      PairedRationalPolicy.ProcessTwoCloseSafe
        A policy code minimum lambda := by
  let lambda := pairedLeftLambdaOfNarrowed A policy code minimum
    controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    (LeftPairedMonitor A policy code minimum) hthreads
  have hmonitor : ∀ env : Nat -> In₁ × In₂,
      (LeftPairedMonitor A policy code minimum).WinsPlay
        (pairPlay (pairedLeftReceiverStrategy lambda)
          (pairedLeftSenderStrategy lambda) env) := by
    intro env
    have hplay := ((LeftPairedMonitor A policy code minimum).lift_winningTree_iff
      (narrowedInducedTree (LeftPairedMonitor A policy code minimum)
        controller.labeledTree)).mp htree env
    rw [pairedLeft_pairPlay_lambdaOfNarrowed A policy code minimum
      controller.labeledTree env]
    exact hplay
  have hclose := pairedLeft_closeSafe_of_monitorWins
    A policy code minimum lambda hmonitor
  refine ⟨?_, hclose⟩
  apply pairedLeftForeverAccepts_of_universalDPA A code lambda
  intro env
  have hm := hmonitor env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n =>
        (LeftPairedMonitor A policy code minimum).priority
          ((LeftPairedMonitor A policy code minimum).run
            (pairPlay (pairedLeftReceiverStrategy lambda)
              (pairedLeftSenderStrategy lambda) env) n)) =
      (fun n =>
        (pairedLeftThreadSystem A code).universalRunDPA.priority
          ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n) + 2) := by
    funext n
    rw [pairedLeftBlockMonitor_run_eq A policy code minimum lambda hclose env n]
    rfl
  rw [heq] at hm
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hm

end Left

/-! ## A coherent finite controller family -/

/-- One selected finite controller for every reachable live state of a
rational paired policy.  Reachability proofs cannot encode information or act
as a leader oracle. -/
structure FinitePairedPolicyFamily
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy) where
  rightController : ∀ (code : A.State × A.State) (minimum : A.State),
    PairedRationalPolicy.Reachable A policy
      (Sum.inr (Sum.inl (code, minimum))) ->
      TransitionRationalTree.{u, max u v x y s, s} In₁
        (RightNarrowedControllerLabel A policy code minimum)
  rightWins : ∀ (code : A.State × A.State) (minimum : A.State)
      (hreachable : PairedRationalPolicy.Reachable A policy
        (Sum.inr (Sum.inl (code, minimum)))),
    NarrowedAllThreadsWin (RightPairedMonitor A policy code minimum)
      (rightController code minimum hreachable).labeledTree
  leftController : ∀ (code : A.State × A.State) (minimum : A.State),
    PairedRationalPolicy.Reachable A policy
      (Sum.inr (Sum.inr (code, minimum))) ->
      TransitionRationalTree.{v, max u v x y s, s} In₂
        (LeftNarrowedControllerLabel A policy code minimum)
  leftWins : ∀ (code : A.State × A.State) (minimum : A.State)
      (hreachable : PairedRationalPolicy.Reachable A policy
        (Sum.inr (Sum.inr (code, minimum)))),
    NarrowedAllThreadsWin (LeftPairedMonitor A policy code minimum)
      (leftController code minimum hreachable).labeledTree

/-- Select all reachable block controllers simultaneously. -/
noncomputable def finitePairedPolicyFamily
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy) :
    FinitePairedPolicyFamily A policy := by
  classical
  let chooseRight := fun (code : A.State × A.State) (minimum : A.State)
      (hreachable : PairedRationalPolicy.Reachable A policy
        (Sum.inr (Sum.inl (code, minimum)))) =>
    Classical.choose
      (exists_finite_processOneBlockController A policy code minimum hreachable)
  let chooseLeft := fun (code : A.State × A.State) (minimum : A.State)
      (hreachable : PairedRationalPolicy.Reachable A policy
        (Sum.inr (Sum.inr (code, minimum)))) =>
    Classical.choose
      (exists_finite_processTwoBlockController A policy code minimum hreachable)
  exact {
    rightController := chooseRight
    rightWins := fun code minimum hreachable =>
      Classical.choose_spec
        (exists_finite_processOneBlockController A policy code minimum hreachable)
    leftController := chooseLeft
    leftWins := fun code minimum hreachable =>
      Classical.choose_spec
        (exists_finite_processTwoBlockController A policy code minimum hreachable)
  }

/-- Semantic guarantee of every selected process-one controller. -/
theorem FinitePairedPolicyFamily.right_sound
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    {initialState : PairedEntryTreeState A}
    {policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy}
    (family : FinitePairedPolicyFamily A policy)
    (code : A.State × A.State) (minimum : A.State)
    (hreachable : PairedRationalPolicy.Reachable A policy
      (Sum.inr (Sum.inl (code, minimum)))) :
    let lambda := pairedRightLambdaOfNarrowed A policy code minimum
      (family.rightController code minimum hreachable).labeledTree
    PairedRightForeverAccepts A code lambda ∧
      PairedRationalPolicy.ProcessOneCloseSafe A policy code minimum lambda :=
  pairedRightController_sound A policy code minimum
    (family.rightController code minimum hreachable)
    (family.rightWins code minimum hreachable)

/-- Process-two mirror of `right_sound`. -/
theorem FinitePairedPolicyFamily.left_sound
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    {initialState : PairedEntryTreeState A}
    {policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy}
    (family : FinitePairedPolicyFamily A policy)
    (code : A.State × A.State) (minimum : A.State)
    (hreachable : PairedRationalPolicy.Reachable A policy
      (Sum.inr (Sum.inr (code, minimum)))) :
    let lambda := pairedLeftLambdaOfNarrowed A policy code minimum
      (family.leftController code minimum hreachable).labeledTree
    PairedLeftForeverAccepts A code lambda ∧
      PairedRationalPolicy.ProcessTwoCloseSafe A policy code minimum lambda :=
  pairedLeftController_sound A policy code minimum
    (family.leftController code minimum hreachable)
    (family.leftWins code minimum hreachable)

/-! ## Root-indexed finite policy families -/

/-- The finite recurrent data selected at every possible first input pair.
The root key is finite; the policies themselves are compile-time constants
indexed by that key and are never stored as run-time observations. -/
structure FirstEntryFinitePolicyFamilies
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  processOnePolicy : ∀ inputOne inputTwo,
    (pairedEntryRunAutomaton A
      (firstProcOneMemory A strategy inputOne inputTwo).toTreeState).RationalTransitionPolicy
  processOneFamily : ∀ inputOne inputTwo,
    FinitePairedPolicyFamily A (processOnePolicy inputOne inputTwo)
  processTwoPolicy : ∀ inputOne inputTwo,
    (pairedEntryRunAutomaton A
      (firstProcTwoMemory A strategy inputOne inputTwo).toTreeState).RationalTransitionPolicy
  processTwoFamily : ∀ inputOne inputTwo,
    FinitePairedPolicyFamily A (processTwoPolicy inputOne inputTwo)

/-- Rational runs at all finite root keys yield a selected finite policy and
controller family at every key. -/
noncomputable def FirstEntryRationalRuns.toFinitePolicyFamilies
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (runs : FirstEntryRationalRuns A strategy) :
    FirstEntryFinitePolicyFamilies A strategy := by
  classical
  let policyOne := fun inputOne inputTwo =>
    Classical.choice
      (InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
        (pairedEntryRunAutomaton A
          (firstProcOneMemory A strategy inputOne inputTwo).toTreeState)
        (runs.processOne inputOne inputTwo))
  let policyTwo := fun inputOne inputTwo =>
    Classical.choice
      (InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
        (pairedEntryRunAutomaton A
          (firstProcTwoMemory A strategy inputOne inputTwo).toTreeState)
        (runs.processTwo inputOne inputTwo))
  exact {
    processOnePolicy := policyOne
    processOneFamily := fun inputOne inputTwo =>
      finitePairedPolicyFamily A (policyOne inputOne inputTwo)
    processTwoPolicy := policyTwo
    processTwoFamily := fun inputOne inputTwo =>
      finitePairedPolicyFamily A (policyTwo inputOne inputTwo)
  }

/-- The initial process-one macro state occurs at the empty policy node. -/
theorem FirstEntryFinitePolicyFamilies.processOne_root_reachable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (families : FirstEntryFinitePolicyFamilies A strategy)
    (inputOne : In₁) (inputTwo : In₂) :
    PairedRationalPolicy.Reachable A
      (families.processOnePolicy inputOne inputTwo)
      (firstProcOneMemory A strategy inputOne inputTwo).toTreeState := by
  refine ⟨[], ?_⟩
  exact (families.processOnePolicy inputOne inputTwo).accepts.1.1

/-- Process-two mirror of root reachability. -/
theorem FirstEntryFinitePolicyFamilies.processTwo_root_reachable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (families : FirstEntryFinitePolicyFamilies A strategy)
    (inputOne : In₁) (inputTwo : In₂) :
    PairedRationalPolicy.Reachable A
      (families.processTwoPolicy inputOne inputTwo)
      (firstProcTwoMemory A strategy inputOne inputTwo).toTreeState := by
  refine ⟨[], ?_⟩
  exact (families.processTwoPolicy inputOne inputTwo).accepts.1.1


end DetParityAutomaton

end DistributedSynthesis
