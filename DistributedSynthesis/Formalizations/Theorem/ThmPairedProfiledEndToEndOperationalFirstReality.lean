/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalPostInvariant

/-!
# Reality of exceptional first-block controller prefixes

This file turns the universal winning proof of each selected narrowed
first-block controller into the operational fact needed at a reversal: every
real finite prefix stages a certified recurrent successor.  The finite past
is proof-only; the executable summaries retain only the resulting finite
controller and monitor states.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## First-right controller -/

abbrev EndToEndFirstRightFiniteState
    (key : EndToEndInitialLeftBoundaryKey A package) :=
  (endToEndInitialLeftBoundaryController A package key).Control ×
    (endToEndFirstRightMonitor A package key).State

noncomputable def stepEndToEndFirstRightFiniteState
    (key : EndToEndInitialLeftBoundaryKey A package)
    (state : EndToEndFirstRightFiniteState A package key)
    (move : In₂ × In₁) : EndToEndFirstRightFiniteState A package key :=
  let controller := endToEndInitialLeftBoundaryController A package key
  let monitor := endToEndFirstRightMonitor A package key
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def endToEndFirstRightFiniteStateAfter
    (key : EndToEndInitialLeftBoundaryKey A package)
    (past : List (In₂ × In₁)) : EndToEndFirstRightFiniteState A package key :=
  past.foldl (stepEndToEndFirstRightFiniteState A package key)
    ((endToEndInitialLeftBoundaryController A package key).initial,
      (endToEndFirstRightMonitor A package key).initial)

theorem endToEndFirstRightFiniteStateAfter_eq
    (key : EndToEndInitialLeftBoundaryKey A package) :
    ∀ past : List (In₂ × In₁),
    endToEndFirstRightFiniteStateAfter A package key past =
      ((endToEndInitialLeftBoundaryController A package key).controlAt
          (senderWord past),
        narrowedControl (endToEndFirstRightMonitor A package key)
          (endToEndInitialLeftBoundaryController A package key).labeledTree
          past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [endToEndFirstRightFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepEndToEndFirstRightFiniteState A package key
        (endToEndFirstRightFiniteStateAfter A package key past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

private theorem endToEndFirstRight_treePlay_at_prefix
    (key : EndToEndInitialLeftBoundaryKey A package)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let monitor := endToEndFirstRightMonitor A package key
    let controller := endToEndInitialLeftBoundaryController A package key
    let env := omegaOfList (past ++ [move])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) move := by
  dsimp only
  let finiteWord := past ++ [move]
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
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, senderWord, env, finiteWord]

/-- Every real first-right prefix stages a certified recurrent-left macro. -/
theorem endToEndFirstRight_real_close_staged
    (key : EndToEndInitialLeftBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (stepEndToEndGuardedFirstRightReceiverFor A package key
      (endToEndFirstRightFiniteStateAfter A package key past).1 row
      (endToEndFirstRightFiniteStateAfter A package key past).2 move).2.2.isSome := by
  rw [endToEndFirstRightFiniteStateAfter_eq A package key]
  let monitor := endToEndFirstRightMonitor A package key
  let controller := endToEndInitialLeftBoundaryController A package key
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (endToEndInitialLeftBoundaryController_wins A package key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := endToEndGuardedFirstRight_targetsSafe_of_wins A
    key.1.2.2.2
    (endToEndInitialLeftBoundaryActivation A package key).profile
    (endToEndInitialLeftBoundaryActivation A package key).policy
    (endToEndInitialLeftBoundaryShape A package key).code
    (endToEndInitialLeftBoundaryShape A package key).minimum
    (endToEndInitialLeftBoundaryShape A package key).profile
    (treePlay tree env) hwin past.length row
  have hat := endToEndFirstRight_treePlay_at_prefix A package key past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  simp only [stepEndToEndGuardedFirstRightReceiverFor]
  split
  · rfl
  · rename_i hnot
    exfalso
    apply hnot
    simpa [narrowedRecord] using hsafe

/-- The pending profile stored at a real exceptional first-right prefix is
honored on the following physical round. -/
theorem endToEndFirstRight_real_overlap
    (key : EndToEndInitialLeftBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      (endToEndFirstRightFiniteStateAfter A package key past).2.2.2.1 row =
        some expected) :
    pairedRightClosingForRow row
        (((endToEndInitialLeftBoundaryController A package key).labelOf
          (endToEndFirstRightFiniteStateAfter A package key past).1).2
          (endToEndFirstRightFiniteStateAfter A package key past).2
          move).physical =
      expected (move.2, move.1) := by
  rw [endToEndFirstRightFiniteStateAfter_eq A package key] at hpending ⊢
  let monitor := endToEndFirstRightMonitor A package key
  let controller := endToEndInitialLeftBoundaryController A package key
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (endToEndInitialLeftBoundaryController_wins A package key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := endToEndGuardedFirstRight_overlap_of_wins A
    key.1.2.2.2
    (endToEndInitialLeftBoundaryActivation A package key).profile
    (endToEndInitialLeftBoundaryActivation A package key).policy
    (endToEndInitialLeftBoundaryShape A package key).code
    (endToEndInitialLeftBoundaryShape A package key).minimum
    (endToEndInitialLeftBoundaryShape A package key).profile
    (treePlay tree env) hwin past.length row expected
  have hat := endToEndFirstRight_treePlay_at_prefix A package key past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hoverlap
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  apply hoverlap
  rw [hrun]
  exact hpending

/-! ## First-left controller -/

abbrev EndToEndFirstLeftFiniteState
    (key : EndToEndInitialRightBoundaryKey A package) :=
  (endToEndInitialRightBoundaryController A package key).Control ×
    (endToEndFirstLeftMonitor A package key).State

noncomputable def stepEndToEndFirstLeftFiniteState
    (key : EndToEndInitialRightBoundaryKey A package)
    (state : EndToEndFirstLeftFiniteState A package key)
    (move : In₁ × In₂) : EndToEndFirstLeftFiniteState A package key :=
  let controller := endToEndInitialRightBoundaryController A package key
  let monitor := endToEndFirstLeftMonitor A package key
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def endToEndFirstLeftFiniteStateAfter
    (key : EndToEndInitialRightBoundaryKey A package)
    (past : List (In₁ × In₂)) : EndToEndFirstLeftFiniteState A package key :=
  past.foldl (stepEndToEndFirstLeftFiniteState A package key)
    ((endToEndInitialRightBoundaryController A package key).initial,
      (endToEndFirstLeftMonitor A package key).initial)

theorem endToEndFirstLeftFiniteStateAfter_eq
    (key : EndToEndInitialRightBoundaryKey A package) :
    ∀ past : List (In₁ × In₂),
    endToEndFirstLeftFiniteStateAfter A package key past =
      ((endToEndInitialRightBoundaryController A package key).controlAt
          (senderWord past),
        narrowedControl (endToEndFirstLeftMonitor A package key)
          (endToEndInitialRightBoundaryController A package key).labeledTree
          past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [endToEndFirstLeftFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepEndToEndFirstLeftFiniteState A package key
        (endToEndFirstLeftFiniteStateAfter A package key past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

private theorem endToEndFirstLeft_treePlay_at_prefix
    (key : EndToEndInitialRightBoundaryKey A package)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let monitor := endToEndFirstLeftMonitor A package key
    let controller := endToEndInitialRightBoundaryController A package key
    let env := omegaOfList (past ++ [move])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) move := by
  dsimp only
  let finiteWord := past ++ [move]
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
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, senderWord, env, finiteWord]

/-- Every real first-left prefix stages a certified recurrent-right macro. -/
theorem endToEndFirstLeft_real_close_staged
    (key : EndToEndInitialRightBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (stepEndToEndGuardedFirstLeftReceiverFor A package key
      (endToEndFirstLeftFiniteStateAfter A package key past).1 row
      (endToEndFirstLeftFiniteStateAfter A package key past).2 move).2.2.isSome := by
  rw [endToEndFirstLeftFiniteStateAfter_eq A package key]
  let monitor := endToEndFirstLeftMonitor A package key
  let controller := endToEndInitialRightBoundaryController A package key
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (endToEndInitialRightBoundaryController_wins A package key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := endToEndGuardedFirstLeft_targetsSafe_of_wins A
    key.1.2.2.2
    (endToEndInitialRightBoundaryActivation A package key).profile
    (endToEndInitialRightBoundaryActivation A package key).policy
    (endToEndInitialRightBoundaryShape A package key).code
    (endToEndInitialRightBoundaryShape A package key).minimum
    (endToEndInitialRightBoundaryShape A package key).profile
    (treePlay tree env) hwin past.length row
  have hat := endToEndFirstLeft_treePlay_at_prefix A package key past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  simp only [stepEndToEndGuardedFirstLeftReceiverFor]
  split
  · rfl
  · rename_i hnot
    exfalso
    apply hnot
    simpa [narrowedRecord] using hsafe

/-- Left-oriented mirror of `endToEndFirstRight_real_overlap`. -/
theorem endToEndFirstLeft_real_overlap
    (key : EndToEndInitialRightBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      (endToEndFirstLeftFiniteStateAfter A package key past).2.2.2.1 row =
        some expected) :
    pairedLeftClosingForRow row
        (((endToEndInitialRightBoundaryController A package key).labelOf
          (endToEndFirstLeftFiniteStateAfter A package key past).1).2
          (endToEndFirstLeftFiniteStateAfter A package key past).2
          move).physical =
      expected (move.2, move.1) := by
  rw [endToEndFirstLeftFiniteStateAfter_eq A package key] at hpending ⊢
  let monitor := endToEndFirstLeftMonitor A package key
  let controller := endToEndInitialRightBoundaryController A package key
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (endToEndInitialRightBoundaryController_wins A package key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := endToEndGuardedFirstLeft_overlap_of_wins A
    key.1.2.2.2
    (endToEndInitialRightBoundaryActivation A package key).profile
    (endToEndInitialRightBoundaryActivation A package key).policy
    (endToEndInitialRightBoundaryShape A package key).code
    (endToEndInitialRightBoundaryShape A package key).minimum
    (endToEndInitialRightBoundaryShape A package key).profile
    (treePlay tree env) hwin past.length row expected
  have hat := endToEndFirstLeft_treePlay_at_prefix A package key past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hoverlap
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  apply hoverlap
  rw [hrun]
  exact hpending

end

end DetParityAutomaton

end DistributedSynthesis
