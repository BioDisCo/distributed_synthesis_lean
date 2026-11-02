/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalStrictInstallation

/-!
# Reachability and checked targets of the local guarded strict blocks

The first-letter guard wraps the ordinary physical sibling monitor.  Its
winning narrowed controller therefore projects to a winning play of the base
monitor.  This file uses that projection to recover, at every real finite
controller prefix, both halves of the close certificate:

* the emitted target is in the base descriptor's allowed relation;
* erasing the target is exactly the physical close computed by the monitor.

Consequently every retained target along the local pending/resolved strict
trace materializes the finite handoff key from the preceding file and feeds
the existing target-indexed kernel.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## Forgetting the first-letter guard recovers target safety -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every target emitted by a guarded right controller is a base-allowed
target and an exact physical close. -/
theorem
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController_targetSafe
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
      member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).base.2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      profiledRawJointRightPhysicalSiblingAllowed A move.1.base
        ((play n).2.1.target row) := by
  dsimp only
  let base := profiledRawJointRightPhysicalSiblingMonitor A move.1.base false
  let monitor := base.firstLetterGuard move.1.firstAllowed
  let controller := move.memberController A member
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (move.memberController_wins A member)
  have hguard : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base
      move.1.firstAllowed play hguard
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A move.1.base)
    move.1.base.source play hbase n row
  rw [← BlockRecordMonitor.firstLetterGuard_run_base base
    move.1.firstAllowed play n] at hsafe
  exact hsafe

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController_targetSafe
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
      member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).base.2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      profiledRawJointLeftPhysicalSiblingAllowed A move.1.base
        ((play n).2.1.target row) := by
  dsimp only
  let base := profiledRawJointLeftPhysicalSiblingMonitor A move.1.base false
  let monitor := base.firstLetterGuard move.1.firstAllowed
  let controller := move.memberController A member
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (move.memberController_wins A member)
  have hguard : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base
      move.1.firstAllowed play hguard
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A move.1.base)
    move.1.base.source play hbase n row
  rw [← BlockRecordMonitor.firstLetterGuard_run_base base
    move.1.firstAllowed play n] at hsafe
  exact hsafe

/-! ## Exact guarded-controller prefixes -/

private abbrev RightFiniteState (pair : CommonPair A strategy hwin) :=
  ((pair.1.1).memberController A false).Control ×
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A pair.1.1.1 false
      ).State

private abbrev LeftFiniteState (pair : CommonPair A strategy hwin) :=
  ((pair.1.2).memberController A false).Control ×
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A pair.1.2.1 false
      ).State

private noncomputable def rightInitialFiniteState
    (pair : CommonPair A strategy hwin) : RightFiniteState A strategy hwin pair :=
  (((pair.1.1).memberController A false).initial,
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A pair.1.1.1 false
      ).initial)

private noncomputable def leftInitialFiniteState
    (pair : CommonPair A strategy hwin) : LeftFiniteState A strategy hwin pair :=
  (((pair.1.2).memberController A false).initial,
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A pair.1.2.1 false
      ).initial)

private noncomputable def rightStepFiniteState
    (pair : CommonPair A strategy hwin)
    (state : RightFiniteState A strategy hwin pair) (input : In₂ × In₁) :
    RightFiniteState A strategy hwin pair :=
  let move := pair.1.1
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let label := controller.labelOf state.1
  (controller.step state.1 input.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 input))

private noncomputable def leftStepFiniteState
    (pair : CommonPair A strategy hwin)
    (state : LeftFiniteState A strategy hwin pair) (input : In₁ × In₂) :
    LeftFiniteState A strategy hwin pair :=
  let move := pair.1.2
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let label := controller.labelOf state.1
  (controller.step state.1 input.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 input))

/-- Exact controller and guarded-monitor state after a finite right prefix. -/
noncomputable def profiledRawJointGuardedCommonRightFiniteStateAfter
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁)) :
    RightFiniteState A strategy hwin pair :=
  past.foldl (rightStepFiniteState A strategy hwin pair)
    (rightInitialFiniteState A strategy hwin pair)

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonLeftFiniteStateAfter
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂)) :
    LeftFiniteState A strategy hwin pair :=
  past.foldl (leftStepFiniteState A strategy hwin pair)
    (leftInitialFiniteState A strategy hwin pair)

theorem profiledRawJointGuardedCommonRightFiniteStateAfter_eq
    (pair : CommonPair A strategy hwin) : ∀ past : List (In₂ × In₁),
    profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        past =
      (((pair.1.1).memberController A false).controlAt (senderWord past),
        narrowedControl
          (profiledRawJointGuardedRightPhysicalSiblingMonitor A pair.1.1.1
            false)
          ((pair.1.1).memberController A false).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past input ih =>
      rw [profiledRawJointGuardedCommonRightFiniteStateAfter,
        List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change rightStepFiniteState A strategy hwin pair
        (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
          pair past) input = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

theorem profiledRawJointGuardedCommonLeftFiniteStateAfter_eq
    (pair : CommonPair A strategy hwin) : ∀ past : List (In₁ × In₂),
    profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        past =
      (((pair.1.2).memberController A false).controlAt (senderWord past),
        narrowedControl
          (profiledRawJointGuardedLeftPhysicalSiblingMonitor A pair.1.2.1
            false)
          ((pair.1.2).memberController A false).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past input ih =>
      rw [profiledRawJointGuardedCommonLeftFiniteStateAfter,
        List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change leftStepFiniteState A strategy hwin pair
        (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
          pair past) input = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

/-- Receiver output computed at the next right prefix. -/
noncomputable def profiledRawJointGuardedCommonRightPrefixOutput
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A) :=
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let controller := (pair.1.1).memberController A false
  (controller.labelOf state.1).2 state.2 input

/-- Left receiver output. -/
noncomputable def profiledRawJointGuardedCommonLeftPrefixOutput
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A) :=
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let controller := (pair.1.2).memberController A false
  (controller.labelOf state.1).2 state.2 input

private theorem right_treePlay_at_prefix
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let env := omegaOfList (past ++ [input])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) input := by
  dsimp only
  let finiteWord := past ++ [input]
  let env : Nat → In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = input
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hinput, senderWord, env, finiteWord]

private theorem left_treePlay_at_prefix
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let env := omegaOfList (past ++ [input])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) input := by
  dsimp only
  let finiteWord := past ++ [input]
  let env : Nat → In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = input
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hinput, senderWord, env, finiteWord]

/-! ## Literal finite-prefix monitor alignment -/

/-- At an arbitrary infinite right input word, the literal controller play
at time `n` is computed from the finite guarded state after its exact omega
prefix. -/
theorem profiledRawJointGuardedCommonRightLiteralPlay_at
    (pair : CommonPair A strategy hwin) (env : Nat → In₂ × In₁)
    (n : Nat) :
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    play n =
      narrowedRecord monitor
        (controller.labelOf
          (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
            pair (omegaPrefix env n)).1)
        (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
          pair (omegaPrefix env n)).2 (env n) := by
  dsimp only
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    senderWord]

/-- Infinite-word left mirror. -/
theorem profiledRawJointGuardedCommonLeftLiteralPlay_at
    (pair : CommonPair A strategy hwin) (env : Nat → In₁ × In₂)
    (n : Nat) :
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    play n =
      narrowedRecord monitor
        (controller.labelOf
          (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
            pair (omegaPrefix env n)).1)
        (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
          pair (omegaPrefix env n)).2 (env n) := by
  dsimp only
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    senderWord]

/-- Public literal-play form of the right prefix record equation. -/
theorem profiledRawJointGuardedCommonRightLiteralPlay_at_prefix
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    play past.length =
      narrowedRecord monitor
        (controller.labelOf
          (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
            pair past).1)
        (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
          pair past).2 input := by
  dsimp only
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin]
  exact right_treePlay_at_prefix A strategy hwin pair past input

/-- Public left-prefix literal record equation. -/
theorem profiledRawJointGuardedCommonLeftLiteralPlay_at_prefix
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    play past.length =
      narrowedRecord monitor
        (controller.labelOf
          (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
            pair past).1)
        (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
          pair past).2 input := by
  dsimp only
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin]
  exact left_treePlay_at_prefix A strategy hwin pair past input

/-- The guarded right finite state stores exactly the target monitor state
reached by the literal local play through the preceding strict prefix.  The
extra input only makes `omegaOfList` expose the complete finite prefix and is
not consumed by this equality. -/
theorem profiledRawJointGuardedCommonRightFiniteStateAfter_monitorRun
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    monitor.run play past.length =
      (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        past).2 := by
  dsimp only
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin]
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change omegaOfList (past ++ [input]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [input]) n hnPrefix]
      simp [hnRight]
  rw [← monitor.lift_control_branchNode
    (narrowedInducedTree monitor controller.labeledTree) env,
    lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]

/-- Left-prefix mirror of the exact finite monitor-state alignment. -/
theorem profiledRawJointGuardedCommonLeftFiniteStateAfter_monitorRun
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    monitor.run play past.length =
      (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        past).2 := by
  dsimp only
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin]
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change omegaOfList (past ++ [input]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [input]) n hnPrefix]
      simp [hnRight]
  rw [← monitor.lift_control_branchNode
    (narrowedInducedTree monitor controller.labeledTree) env,
    lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]

/-! ## Allowed-and-close certificates at every finite prefix -/

theorem profiledRawJointGuardedCommonRightPrefixTargetSafe
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          (record.2.1.target row)) =
        pairedRightCloseTarget A (state.2.base.2.1) row
          (profiledRawJointTargetRightPhysicalLetter A record) ∧
      profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base
        (record.2.1.target row) := by
  dsimp only
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin]
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hsafe := pair.1.1.memberController_targetSafe A false env past.length row
  dsimp only at hsafe
  change
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play past.length).2.1.target row)) =
        pairedRightCloseTarget A
          ((monitor.run play past.length).base.2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play past.length)) ∧
      profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base
        ((play past.length).2.1.target row) at hsafe
  have hat := right_treePlay_at_prefix A strategy hwin pair past input
  change play past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change omegaOfList (past ++ [input]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run play past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode
      (narrowedInducedTree monitor controller.labeledTree) env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  simpa only [Prod.fst, Prod.snd] using hsafe

theorem profiledRawJointGuardedCommonLeftPrefixTargetSafe
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          (record.2.1.target row)) =
        pairedLeftCloseTarget A (state.2.base.2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A record) ∧
      profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base
        (record.2.1.target row) := by
  dsimp only
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin]
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hsafe := pair.1.2.memberController_targetSafe A false env past.length row
  dsimp only at hsafe
  change
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play past.length).2.1.target row)) =
        pairedLeftCloseTarget A
          ((monitor.run play past.length).base.2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play past.length)) ∧
      profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base
        ((play past.length).2.1.target row) at hsafe
  have hat := left_treePlay_at_prefix A strategy hwin pair past input
  change play past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change omegaOfList (past ++ [input]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run play past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode
      (narrowedInducedTree monitor controller.labeledTree) env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  simpa only [Prod.fst, Prod.snd] using hsafe

/-! ## Prefix handoffs into the indexed recurrent kernel -/

/-- Materialize the checked target at one real guarded-right controller
prefix as the finite dependent handoff key. -/
noncomputable def profiledRawJointGuardedCommonRightPrefixHandoff
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonRightHandoff A strategy hwin := by
  let output := profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin
    pair past input
  have hsafe := profiledRawJointGuardedCommonRightPrefixTargetSafe A strategy
    hwin pair past input row
  exact profiledRawJointGuardedCommonRightHandoffOfSafe A strategy hwin pair
    (output.target row) hsafe.2

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonLeftPrefixHandoff
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin := by
  let output := profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin
    pair past input
  have hsafe := profiledRawJointGuardedCommonLeftPrefixTargetSafe A strategy
    hwin pair past input row
  exact profiledRawJointGuardedCommonLeftHandoffOfSafe A strategy hwin pair
    (output.target row) hsafe.2

@[simp] theorem profiledRawJointGuardedCommonRightPrefixHandoff_pair
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonRightPrefixHandoff A strategy hwin pair past
      input row).1 = pair :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLeftPrefixHandoff_pair
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonLeftPrefixHandoff A strategy hwin pair past
      input row).1 = pair :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonRightPrefixHandoff_target
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonRightPrefixHandoff A strategy hwin pair past
      input row).2.1 =
      (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair
        past input).target row :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLeftPrefixHandoff_target
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonLeftPrefixHandoff A strategy hwin pair past
      input row).2.1 =
      (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
        input).target row :=
  rfl

set_option maxHeartbeats 800000 in
/-- Every real right prefix already supplies the recurrent root package
consumed by the existing target-indexed kernel. -/
theorem
    nonempty_profiledRawJointGuardedCommonRightPrefixHandoffRootPackage
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let handoff := profiledRawJointGuardedCommonRightPrefixHandoff A strategy
      hwin pair past input row
    Nonempty
      (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin
        (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
        (profiledRawJointGuardedCommonPairDirection A strategy hwin handoff.1)
        (profiledRawJointSiblingTargetChildOfRight A strategy
          (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
          (profiledRawJointGuardedCommonPairDirection A strategy hwin
            handoff.1) handoff.2)) := by
  dsimp only
  let handoff := profiledRawJointGuardedCommonRightPrefixHandoff A strategy
    hwin pair past input row
  apply
    nonempty_profiledRawJointGuardedCommonRightHandoffRootPackage_of_close A
      strategy hwin handoff
      (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        past).2.base.2.1 row
      (profiledRawJointTargetRightPhysicalLetter A
        (narrowedRecord
          (profiledRawJointGuardedRightPhysicalSiblingMonitor A pair.1.1.1
            false)
          (((pair.1.1).memberController A false).labelOf
            (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
              pair past).1)
          (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
            pair past).2 input))
  have hsafe := profiledRawJointGuardedCommonRightPrefixTargetSafe A strategy
    hwin pair past input row
  simpa [handoff,
    profiledRawJointGuardedCommonRightPrefixHandoff,
    profiledRawJointGuardedCommonRightPrefixOutput] using hsafe.1

set_option maxHeartbeats 800000 in
/-- Left prefix mirror. -/
theorem
    nonempty_profiledRawJointGuardedCommonLeftPrefixHandoffRootPackage
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let handoff := profiledRawJointGuardedCommonLeftPrefixHandoff A strategy
      hwin pair past input row
    Nonempty
      (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin
        (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
        (profiledRawJointGuardedCommonPairDirection A strategy hwin handoff.1)
        (profiledRawJointSiblingTargetChildOfLeft A strategy
          (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
          (profiledRawJointGuardedCommonPairDirection A strategy hwin
            handoff.1) handoff.2)) := by
  dsimp only
  let handoff := profiledRawJointGuardedCommonLeftPrefixHandoff A strategy hwin
    pair past input row
  apply
    nonempty_profiledRawJointGuardedCommonLeftHandoffRootPackage_of_close A
      strategy hwin handoff
      (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        past).2.base.2.1 row
      (profiledRawJointTargetLeftPhysicalLetter A
        (narrowedRecord
          (profiledRawJointGuardedLeftPhysicalSiblingMonitor A pair.1.2.1
            false)
          (((pair.1.2).memberController A false).labelOf
            (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
              pair past).1)
          (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
            pair past).2 input))
  have hsafe := profiledRawJointGuardedCommonLeftPrefixTargetSafe A strategy
    hwin pair past input row
  simpa [handoff,
    profiledRawJointGuardedCommonLeftPrefixHandoff,
    profiledRawJointGuardedCommonLeftPrefixOutput] using hsafe.1

end

end DetParityAutomaton

end DistributedSynthesis
