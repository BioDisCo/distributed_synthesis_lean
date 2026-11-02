/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedFirstBlockRegularization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryControllerSoundness

/-!
# Soundness of finite guarded first-block controllers

The first recurrent controller contains no leader oracle.  Its sender label is
one shared table, and its receiver label is selected from the monitor state.
This file reads such a narrowed controller back into the guarded activation
interface: the root overlap is respected, both latent parity threads accept,
and every possible close has an ordinary rational continuation.
-/

namespace DistributedSynthesis

universe u v x y s z

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section Right

variable (source : GuardedRightEntrySource A)
variable (code : A.State × A.State)

noncomputable abbrev GuardedFirstRightMonitor :=
  guardedFirstRightBlockMonitor.{u, v, x, y, s, 0} A source code

abbrev GuardedFirstRightNarrowedLabel :=
  NarrowedBlockLabel In₂ In₁
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
    (GuardedFirstRightMonitor A source code).State

/-- The paired lambda stored by a narrowed guarded-first-right controller. -/
noncomputable def guardedFirstRightLambdaOfNarrowed
    (narrowed : List In₁ -> GuardedFirstRightNarrowedLabel A source code) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := fun word input => (narrowed word).1 input
  informedLeft := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstRightMonitor A source code)
        narrowed past) move).informedFirst
  informedBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstRightMonitor A source code)
        narrowed past) move).informedBoth
  bothOneLeft := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstRightMonitor A source code)
        narrowed past) move).closingFirst
  bothOneBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstRightMonitor A source code)
        narrowed past) move).closingBoth

theorem guardedFirstRight_pairPlay_lambdaOfNarrowed
    (narrowed : List In₁ -> GuardedFirstRightNarrowedLabel A source code)
    (env : Nat -> In₂ × In₁) :
    pairPlay
        (pairedRightReceiverStrategy
          (guardedFirstRightLambdaOfNarrowed A source code narrowed))
        (pairedRightSenderStrategy
          (guardedFirstRightLambdaOfNarrowed A source code narrowed)) env =
      treePlay
        (narrowedInducedTree (GuardedFirstRightMonitor A source code)
          narrowed) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    pairedRightReceiverStrategy, pairedRightSenderStrategy,
    guardedFirstRightLambdaOfNarrowed, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

/-- Exact semantic components of a guarded first-right monitor run. -/
theorem guardedFirstRightBlockMonitor_run_shape
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₂ × In₁) :
    ∀ n, ∃ safe : Bool,
      (GuardedFirstRightMonitor A source code).run
          (pairPlay (pairedRightReceiverStrategy lambda)
            (pairedRightSenderStrategy lambda) env) n =
        ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n,
          pairedRightScanAfter A code lambda (omegaPrefix env n), n == 0, safe) := by
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
      refine ⟨((GuardedFirstRightMonitor A source code).step
        ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n,
          pairedRightScanAfter A code lambda (omegaPrefix env n), n == 0, safe)
        (pairedRightBlockLetterAt lambda (omegaPrefix env n) (env n))).2.2.2, ?_⟩
      simp [guardedFirstRightBlockMonitor,
        pairedRightBlockWord_eq_letterAt]

/-- Failure of the guarded monitor's safety bit is permanent. -/
theorem guardedFirstRight_safe_false_persists
    (play : Nat -> RealizedBlockRound In₂ In₁
      (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁)
    {N : Nat}
    (hfalse : ((GuardedFirstRightMonitor A source code).run play N).2.2.2 =
      false) :
    ∀ n, N ≤ n ->
      ((GuardedFirstRightMonitor A source code).run play n).2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((GuardedFirstRightMonitor A source code).run play (N + k)).2.2.2 =
            false := ih (Nat.le_add_right N k)
      change
        (((GuardedFirstRightMonitor A source code).run play (N + k)).2.2.2 &&
          _ && _) = false
      rw [ih']
      rfl

/-- A winning play never enters the sticky rejecting state. -/
theorem guardedFirstRight_safe_of_wins
    (play : Nat -> RealizedBlockRound In₂ In₁
      (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁)
    (hwin : (GuardedFirstRightMonitor A source code).WinsPlay play)
    (n : Nat) :
    ((GuardedFirstRightMonitor A source code).run play n).2.2.2 = true := by
  cases hsafe :
      ((GuardedFirstRightMonitor A source code).run play n).2.2.2 with
  | true => rfl
  | false =>
      have hpersist := guardedFirstRight_safe_false_persists
        A source code play hsafe
      have heventual : ∀ m, n ≤ m ->
          (GuardedFirstRightMonitor A source code).priority
              ((GuardedFirstRightMonitor A source code).run play m) = 1 := by
        intro m hm
        have h := hpersist m hm
        change
          (if ((GuardedFirstRightMonitor A source code).run play m).2.2.2
            then _ else 1) = 1
        rw [h]
        rfl
      exact False.elim
        (not_natSeqMinEvenParity_of_eventually_one _ _ heventual hwin)

/-- Winning the guarded monitor recovers the promised root overlap table. -/
theorem guardedFirstRight_profile_of_monitorWins
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₂ × In₁,
      (GuardedFirstRightMonitor A source code).WinsPlay
        (pairPlay (pairedRightReceiverStrategy lambda)
          (pairedRightSenderStrategy lambda) env)) :
    source.1.2.Matches lambda := by
  intro move
  let env : Nat -> In₂ × In₁ := fun _ => move
  have hs := guardedFirstRight_safe_of_wins A source code
    (pairPlay (pairedRightReceiverStrategy lambda)
      (pairedRightSenderStrategy lambda) env) (hwin env) 1
  have hall : source.1.2 move = lambda.bothOneLeft [] move ∧
      (pairedEntryRunAutomaton A
        (pairedRightCloseTarget A (pairedRightScanInitial A code) .first
          (pairedRightBlockLetterAt lambda [] move))).HasRationalRun ∧
      (pairedEntryRunAutomaton A
        (pairedRightCloseTarget A (pairedRightScanInitial A code) .both
          (pairedRightBlockLetterAt lambda [] move))).HasRationalRun := by
    simpa [GuardedFirstRightMonitor, guardedFirstRightBlockMonitor,
      BlockRecordMonitor.run, pairPlay, pairedRightReceiverStrategy,
      pairedRightSenderStrategy, treePlay, treeOfPair, blockLabelApply,
      branchNode_eq_omegaPrefix, env, senderWord] using hs
  exact hall.1.symm

/-- Winning the guarded monitor certifies an ordinary rational continuation
at every possible closing child. -/
theorem guardedFirstRight_children_of_monitorWins
    [Inhabited (In₂ × In₁)]
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₂ × In₁,
      (GuardedFirstRightMonitor A source code).WinsPlay
        (pairPlay (pairedRightReceiverStrategy lambda)
          (pairedRightSenderStrategy lambda) env)) :
    ∀ row past move,
      (pairedEntryRunAutomaton A
        (pairedOneChild A code lambda row past move)).HasRationalRun := by
  classical
  intro row past move
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
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  rcases guardedFirstRightBlockMonitor_run_shape A source code lambda env
      past.length with ⟨safe, hshape⟩
  have hs := guardedFirstRight_safe_of_wins A source code
    (pairPlay (pairedRightReceiverStrategy lambda)
      (pairedRightSenderStrategy lambda) env) (hwin env) (past.length + 1)
  rw [BlockRecordMonitor.run, hshape,
    pairedRight_pairPlay_eq_blockWord lambda env,
    pairedRightBlockWord_eq_letterAt, hpast, hmove] at hs
  change ((safe && _) && decide
    ((pairedEntryRunAutomaton A
        (pairedRightCloseTarget A (pairedRightScanAfter A code lambda past)
          .first (pairedRightBlockLetterAt lambda past move))).HasRationalRun ∧
      (pairedEntryRunAutomaton A
        (pairedRightCloseTarget A (pairedRightScanAfter A code lambda past)
          .both (pairedRightBlockLetterAt lambda past move))).HasRationalRun)) = true at hs
  have hboth := of_decide_eq_true (Bool.and_eq_true_iff.mp hs).2
  rw [pairedRightCloseTarget_scanAfter A code lambda past move .first,
    pairedRightCloseTarget_scanAfter A code lambda past move .both] at hboth
  cases row with
  | first => exact hboth.1
  | both => exact hboth.2

/-- Winning the guarded monitor also recovers both latent parity threads. -/
theorem guardedFirstRight_forever_of_monitorWins
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₂ × In₁,
      (GuardedFirstRightMonitor A source code).WinsPlay
        (pairPlay (pairedRightReceiverStrategy lambda)
          (pairedRightSenderStrategy lambda) env)) :
    PairedRightForeverAccepts A code lambda := by
  apply pairedRightForeverAccepts_of_universalDPA A code lambda
  intro env
  have hm := hwin env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n =>
        (GuardedFirstRightMonitor A source code).priority
          ((GuardedFirstRightMonitor A source code).run
            (pairPlay (pairedRightReceiverStrategy lambda)
              (pairedRightSenderStrategy lambda) env) n)) =
      (fun n =>
        (pairedRightThreadSystem A code).universalRunDPA.priority
          ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n) + 2) := by
    funext n
    rcases guardedFirstRightBlockMonitor_run_shape A source code lambda env n with
      ⟨safe, hshape⟩
    have hs := guardedFirstRight_safe_of_wins A source code
      (pairPlay (pairedRightReceiverStrategy lambda)
        (pairedRightSenderStrategy lambda) env) (hwin env) n
    rw [hshape] at hs ⊢
    change safe = true at hs
    change (if safe then _ else 1) = _
    rw [hs]
    simp
    rfl
  rw [heq] at hm
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hm

/-- Semantic readback of any winning guarded first-right controller. -/
noncomputable def guardedFirstRightController_sound
    [Inhabited (In₂ × In₁)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (minimum : A.State)
    (controller : TransitionRationalTree.{u, max u v x y s, z} In₁
      (GuardedFirstRightNarrowedLabel A source code))
    (hthreads : NarrowedAllThreadsWin
      (GuardedFirstRightMonitor A source code) controller.labeledTree) :
    GuardedRightActivation A source code minimum := by
  let lambda := guardedFirstRightLambdaOfNarrowed A source code
    controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    (GuardedFirstRightMonitor A source code) hthreads
  have hmonitor : ∀ env : Nat -> In₂ × In₁,
      (GuardedFirstRightMonitor A source code).WinsPlay
        (pairPlay (pairedRightReceiverStrategy lambda)
          (pairedRightSenderStrategy lambda) env) := by
    intro env
    have hplay := ((GuardedFirstRightMonitor A source code).lift_winningTree_iff
      (narrowedInducedTree (GuardedFirstRightMonitor A source code)
        controller.labeledTree)).mp htree env
    rw [guardedFirstRight_pairPlay_lambdaOfNarrowed A source code
      controller.labeledTree env]
    exact hplay
  exact {
    lambda := lambda
    profile_matches := guardedFirstRight_profile_of_monitorWins
      A source code lambda hmonitor
    forever := guardedFirstRight_forever_of_monitorWins
      A source code lambda hmonitor
    childFeasible := guardedFirstRight_children_of_monitorWins
      A source code lambda hmonitor
  }

end Right

section Left

variable (source : GuardedLeftEntrySource A)
variable (code : A.State × A.State)

noncomputable abbrev GuardedFirstLeftMonitor :=
  guardedFirstLeftBlockMonitor.{u, v, x, y, s, 0} A source code

abbrev GuardedFirstLeftNarrowedLabel :=
  NarrowedBlockLabel In₁ In₂
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
    (GuardedFirstLeftMonitor A source code).State

noncomputable def guardedFirstLeftLambdaOfNarrowed
    (narrowed : List In₂ -> GuardedFirstLeftNarrowedLabel A source code) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := fun word input => (narrowed word).1 input
  informedRight := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstLeftMonitor A source code)
        narrowed past) move).informedFirst
  informedBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstLeftMonitor A source code)
        narrowed past) move).informedBoth
  bothTwoRight := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstLeftMonitor A source code)
        narrowed past) move).closingFirst
  bothTwoBoth := fun past move =>
    ((narrowed (senderWord past)).2
      (narrowedControl (GuardedFirstLeftMonitor A source code)
        narrowed past) move).closingBoth

theorem guardedFirstLeft_pairPlay_lambdaOfNarrowed
    (narrowed : List In₂ -> GuardedFirstLeftNarrowedLabel A source code)
    (env : Nat -> In₁ × In₂) :
    pairPlay
        (pairedLeftReceiverStrategy
          (guardedFirstLeftLambdaOfNarrowed A source code narrowed))
        (pairedLeftSenderStrategy
          (guardedFirstLeftLambdaOfNarrowed A source code narrowed)) env =
      treePlay
        (narrowedInducedTree (GuardedFirstLeftMonitor A source code)
          narrowed) env := by
  funext n
  simp [pairPlay, treePlay, treeOfPair, blockLabelApply,
    pairedLeftReceiverStrategy, pairedLeftSenderStrategy,
    guardedFirstLeftLambdaOfNarrowed, narrowedInducedTree,
    branchNode_eq_omegaPrefix, senderWord]

theorem guardedFirstLeftBlockMonitor_run_shape
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (env : Nat -> In₁ × In₂) :
    ∀ n, ∃ safe : Bool,
      (GuardedFirstLeftMonitor A source code).run
          (pairPlay (pairedLeftReceiverStrategy lambda)
            (pairedLeftSenderStrategy lambda) env) n =
        ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n,
          pairedLeftScanAfter A code lambda (omegaPrefix env n), n == 0, safe) := by
  intro n
  classical
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
      rcases ih with ⟨safe, ih⟩
      rw [BlockRecordMonitor.run, ih,
        pairedLeft_pairPlay_eq_blockWord lambda env,
        omegaPrefix_succ, pairedLeftScanAfter_append]
      refine ⟨((GuardedFirstLeftMonitor A source code).step
        ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n,
          pairedLeftScanAfter A code lambda (omegaPrefix env n), n == 0, safe)
        (pairedLeftBlockLetterAt lambda (omegaPrefix env n) (env n))).2.2.2, ?_⟩
      simp [guardedFirstLeftBlockMonitor, pairedLeftBlockWord]

theorem guardedFirstLeft_safe_false_persists
    (play : Nat -> RealizedBlockRound In₁ In₂
      (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂)
    {N : Nat}
    (hfalse : ((GuardedFirstLeftMonitor A source code).run play N).2.2.2 = false) :
    ∀ n, N ≤ n ->
      ((GuardedFirstLeftMonitor A source code).run play n).2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      have ih' :
          ((GuardedFirstLeftMonitor A source code).run play (N + k)).2.2.2 =
            false := ih (Nat.le_add_right N k)
      change
        (((GuardedFirstLeftMonitor A source code).run play (N + k)).2.2.2 &&
          _ && _) = false
      rw [ih']
      rfl

theorem guardedFirstLeft_safe_of_wins
    (play : Nat -> RealizedBlockRound In₁ In₂
      (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂)
    (hwin : (GuardedFirstLeftMonitor A source code).WinsPlay play)
    (n : Nat) :
    ((GuardedFirstLeftMonitor A source code).run play n).2.2.2 = true := by
  cases hsafe : ((GuardedFirstLeftMonitor A source code).run play n).2.2.2 with
  | true => rfl
  | false =>
      have hpersist := guardedFirstLeft_safe_false_persists
        A source code play hsafe
      have heventual : ∀ m, n ≤ m ->
          (GuardedFirstLeftMonitor A source code).priority
              ((GuardedFirstLeftMonitor A source code).run play m) = 1 := by
        intro m hm
        have h := hpersist m hm
        change
          (if ((GuardedFirstLeftMonitor A source code).run play m).2.2.2
            then _ else 1) = 1
        rw [h]
        rfl
      exact False.elim
        (not_natSeqMinEvenParity_of_eventually_one _ _ heventual hwin)

theorem guardedFirstLeft_profile_of_monitorWins
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₁ × In₂,
      (GuardedFirstLeftMonitor A source code).WinsPlay
        (pairPlay (pairedLeftReceiverStrategy lambda)
          (pairedLeftSenderStrategy lambda) env)) :
    source.1.2.Matches lambda := by
  intro move
  let env : Nat -> In₁ × In₂ := fun _ => move
  have hs := guardedFirstLeft_safe_of_wins A source code
    (pairPlay (pairedLeftReceiverStrategy lambda)
      (pairedLeftSenderStrategy lambda) env) (hwin env) 1
  have hall : source.1.2 move = lambda.bothTwoRight [] move ∧
      (pairedEntryRunAutomaton A
        (pairedLeftCloseTarget A (pairedLeftScanInitial A code) .first
          (pairedLeftBlockLetterAt lambda [] move))).HasRationalRun ∧
      (pairedEntryRunAutomaton A
        (pairedLeftCloseTarget A (pairedLeftScanInitial A code) .both
          (pairedLeftBlockLetterAt lambda [] move))).HasRationalRun := by
    simpa [GuardedFirstLeftMonitor, guardedFirstLeftBlockMonitor,
      BlockRecordMonitor.run, pairPlay, pairedLeftReceiverStrategy,
      pairedLeftSenderStrategy, treePlay, treeOfPair, blockLabelApply,
      branchNode_eq_omegaPrefix, env, senderWord] using hs
  exact hall.1.symm

theorem guardedFirstLeft_children_of_monitorWins
    [Inhabited (In₁ × In₂)]
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₁ × In₂,
      (GuardedFirstLeftMonitor A source code).WinsPlay
        (pairPlay (pairedLeftReceiverStrategy lambda)
          (pairedLeftSenderStrategy lambda) env)) :
    ∀ row past move,
      (pairedEntryRunAutomaton A
        (pairedTwoChild A code lambda row past move)).HasRationalRun := by
  classical
  intro row past move
  let finiteWord := past ++ [move]
  let env : Nat -> In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  rcases guardedFirstLeftBlockMonitor_run_shape A source code lambda env
      past.length with ⟨safe, hshape⟩
  have hs := guardedFirstLeft_safe_of_wins A source code
    (pairPlay (pairedLeftReceiverStrategy lambda)
      (pairedLeftSenderStrategy lambda) env) (hwin env) (past.length + 1)
  rw [BlockRecordMonitor.run, hshape,
    pairedLeft_pairPlay_eq_blockWord lambda env] at hs
  simp only [pairedLeftBlockWord] at hs
  rw [hpast, hmove] at hs
  change ((safe && _) && decide
    ((pairedEntryRunAutomaton A
        (pairedLeftCloseTarget A (pairedLeftScanAfter A code lambda past)
          .first (pairedLeftBlockLetterAt lambda past move))).HasRationalRun ∧
      (pairedEntryRunAutomaton A
        (pairedLeftCloseTarget A (pairedLeftScanAfter A code lambda past)
          .both (pairedLeftBlockLetterAt lambda past move))).HasRationalRun)) = true at hs
  have hboth := of_decide_eq_true (Bool.and_eq_true_iff.mp hs).2
  rw [pairedLeftCloseTarget_scanAfter A code lambda past move .first,
    pairedLeftCloseTarget_scanAfter A code lambda past move .both] at hboth
  cases row with
  | first => exact hboth.1
  | both => exact hboth.2

theorem guardedFirstLeft_forever_of_monitorWins
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hwin : ∀ env : Nat -> In₁ × In₂,
      (GuardedFirstLeftMonitor A source code).WinsPlay
        (pairPlay (pairedLeftReceiverStrategy lambda)
          (pairedLeftSenderStrategy lambda) env)) :
    PairedLeftForeverAccepts A code lambda := by
  apply pairedLeftForeverAccepts_of_universalDPA A code lambda
  intro env
  have hm := hwin env
  unfold BlockRecordMonitor.WinsPlay at hm
  have heq :
      (fun n =>
        (GuardedFirstLeftMonitor A source code).priority
          ((GuardedFirstLeftMonitor A source code).run
            (pairPlay (pairedLeftReceiverStrategy lambda)
              (pairedLeftSenderStrategy lambda) env) n)) =
      (fun n =>
        (pairedLeftThreadSystem A code).universalRunDPA.priority
          ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n) + 2) := by
    funext n
    rcases guardedFirstLeftBlockMonitor_run_shape A source code lambda env n with
      ⟨safe, hshape⟩
    have hs := guardedFirstLeft_safe_of_wins A source code
      (pairPlay (pairedLeftReceiverStrategy lambda)
        (pairedLeftSenderStrategy lambda) env) (hwin env) n
    rw [hshape] at hs ⊢
    change safe = true at hs
    change (if safe then _ else 1) = _
    rw [hs]
    simp
    rfl
  rw [heq] at hm
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hm

noncomputable def guardedFirstLeftController_sound
    [Inhabited (In₁ × In₂)]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (minimum : A.State)
    (controller : TransitionRationalTree.{v, max u v x y s, z} In₂
      (GuardedFirstLeftNarrowedLabel A source code))
    (hthreads : NarrowedAllThreadsWin
      (GuardedFirstLeftMonitor A source code) controller.labeledTree) :
    GuardedLeftActivation A source code minimum := by
  let lambda := guardedFirstLeftLambdaOfNarrowed A source code
    controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin
    (GuardedFirstLeftMonitor A source code) hthreads
  have hmonitor : ∀ env : Nat -> In₁ × In₂,
      (GuardedFirstLeftMonitor A source code).WinsPlay
        (pairPlay (pairedLeftReceiverStrategy lambda)
          (pairedLeftSenderStrategy lambda) env) := by
    intro env
    have hplay := ((GuardedFirstLeftMonitor A source code).lift_winningTree_iff
      (narrowedInducedTree (GuardedFirstLeftMonitor A source code)
        controller.labeledTree)).mp htree env
    rw [guardedFirstLeft_pairPlay_lambdaOfNarrowed A source code
      controller.labeledTree env]
    exact hplay
  exact {
    lambda := lambda
    profile_matches := guardedFirstLeft_profile_of_monitorWins
      A source code lambda hmonitor
    forever := guardedFirstLeft_forever_of_monitorWins
      A source code lambda hmonitor
    childFeasible := guardedFirstLeft_children_of_monitorWins
      A source code lambda hmonitor
  }

end Left

end DetParityAutomaton

end DistributedSynthesis
