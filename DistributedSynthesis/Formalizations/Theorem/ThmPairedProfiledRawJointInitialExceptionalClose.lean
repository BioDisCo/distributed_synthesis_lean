/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialControllerBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyHandoff

/-!
# The physical exceptional close enters the ordinary raw-joint policy

The initial controller bank is executable in finite local state, while the
guarded-first handoff is stated for the induced infinite tree play.  This
file identifies the two descriptions at an arbitrary finite prefix.  Hence
the literal child emitted by the actual exceptional controller indexes the
fresh ordinary policy, its next macro is rooted at `run []`, and the
post-close monitor state stores the profile of that same macro slot.

Both orientations are proved symmetrically.  No graph, orientation, or
strict-leader signal is an argument of the controller state.
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

/-! ## Finite-prefix/tree-play identification -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At a concrete initial-left prefix, the induced exceptional-right tree
play reads exactly the label and monitor state stored by the finite
controller bank. -/
theorem profiledRawJointInitialLeft_treePlay_at_prefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let activation := (bank.initialLeft key).activation
    let monitor := profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y,
      s, max u v x y s} A strategy activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      activation.pinned (bank.initialLeft key).package.source
    let controller := (bank.initialLeft key).controller
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
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, senderWord, env, finiteWord]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirror finite-prefix/tree-play identification. -/
theorem profiledRawJointInitialRight_treePlay_at_prefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let activation := (bank.initialRight key).activation
    let monitor := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y,
      s, max u v x y s} A strategy activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      activation.pinned (bank.initialRight key).package.source
    let controller := (bank.initialRight key).controller
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
      have hnPrefix : n < finiteWord.length := by
        simp [finiteWord]
        omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, senderWord, env, finiteWord]

/-! ## Actual exceptional close to the fresh ordinary root -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Closing the actual initial-left exceptional controller emits a literal
child and starts the corresponding ordinary left-policy macro at its exact
root.  The post-step monitor remembers that same macro slot profile. -/
theorem exists_profiledRawJointInitialLeft_real_close_policyRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    let chosen := bank.initialLeft key
    let activation := chosen.activation
    let controller := chosen.controller
    let state := profiledRawJointInitialLeftFiniteStateAfter A strategy bank
      key past
    let output := (controller.labelOf state.1).2 state.2 move
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      activation.source (ProfiledRawJointInitialLeftRootPredicate A strategy
        key) activation.pinned
    let policyBank := activation.childPolicyBank A hstrategy
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitLeftPolicyMacro A strategy child.1
          (policyBank child)),
      child = output.target row ∧
      target.state = (policyBank child).run [] ∧
      (stepProfiledRawJointInitialLeftFiniteState A strategy bank key state
        move).2.2.2.1 row = some target.slot.2 := by
  dsimp only
  let chosen := bank.initialLeft key
  let activation := chosen.activation
  let monitor := profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y,
    s, max u v x y s} A strategy activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    activation.pinned chosen.package.source
  let controller := chosen.controller
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  obtain ⟨child, target, hchild, hroot, hpending⟩ :=
    exists_profiledRawJointGuardedFirstLeftPolicyRoot_of_rightController
      A strategy hstrategy activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        activation.pinned chosen.package.source controller chosen.wins env
        past.length row
  have hat := profiledRawJointInitialLeft_treePlay_at_prefix A strategy bank
    key past move
  change play past.length = _ at hat
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
  have hrun : monitor.run play past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  have hnext : monitor.run play (past.length + 1) =
      monitor.step (narrowedControl monitor controller.labeledTree past)
        (narrowedRecord monitor
          (controller.labelOf (controller.controlAt (senderWord past)))
          (narrowedControl monitor controller.labeledTree past) move) := by
    rw [BlockRecordMonitor.run, hrun, hat]
  change child = (play past.length).2.1.target row at hchild
  rw [hat] at hchild
  change (monitor.run play (past.length + 1)).2.2.1 row =
    some target.slot.2 at hpending
  rw [hnext] at hpending
  refine ⟨child, target, ?_, hroot, ?_⟩
  · rw [profiledRawJointInitialLeftFiniteStateAfter_eq A strategy bank key]
    exact hchild
  · rw [profiledRawJointInitialLeftFiniteStateAfter_eq A strategy bank key]
    simpa [stepProfiledRawJointInitialLeftFiniteState, monitor, controller,
      chosen, activation] using hpending

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirror exceptional close: an actual initial-right controller enters the
fresh ordinary right-policy root, with its slot profile installed in the
post-step monitor state. -/
theorem exists_profiledRawJointInitialRight_real_close_policyRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    let chosen := bank.initialRight key
    let activation := chosen.activation
    let controller := chosen.controller
    let state := profiledRawJointInitialRightFiniteStateAfter A strategy bank
      key past
    let output := (controller.labelOf state.1).2 state.2 move
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      activation.source (ProfiledRawJointInitialRightRootPredicate A strategy
        key) activation.pinned
    let policyBank := activation.childPolicyBank A hstrategy
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitRightPolicyMacro A strategy child.1
          (policyBank child)),
      child = output.target row ∧
      target.state = (policyBank child).run [] ∧
      (stepProfiledRawJointInitialRightFiniteState A strategy bank key state
        move).2.2.2.1 row = some target.slot.2 := by
  dsimp only
  let chosen := bank.initialRight key
  let activation := chosen.activation
  let monitor := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y,
    s, max u v x y s} A strategy activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    activation.pinned chosen.package.source
  let controller := chosen.controller
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  obtain ⟨child, target, hchild, hroot, hpending⟩ :=
    exists_profiledRawJointGuardedFirstRightPolicyRoot_of_leftController
      A strategy hstrategy activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        activation.pinned chosen.package.source controller chosen.wins env
        past.length row
  have hat := profiledRawJointInitialRight_treePlay_at_prefix A strategy bank
    key past move
  change play past.length = _ at hat
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
  have hrun : monitor.run play past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  have hnext : monitor.run play (past.length + 1) =
      monitor.step (narrowedControl monitor controller.labeledTree past)
        (narrowedRecord monitor
          (controller.labelOf (controller.controlAt (senderWord past)))
          (narrowedControl monitor controller.labeledTree past) move) := by
    rw [BlockRecordMonitor.run, hrun, hat]
  change child = (play past.length).2.1.target row at hchild
  rw [hat] at hchild
  change (monitor.run play (past.length + 1)).2.2.1 row =
    some target.slot.2 at hpending
  rw [hnext] at hpending
  refine ⟨child, target, ?_, hroot, ?_⟩
  · rw [profiledRawJointInitialRightFiniteStateAfter_eq A strategy bank key]
    exact hchild
  · rw [profiledRawJointInitialRightFiniteStateAfter_eq A strategy bank key]
    simpa [stepProfiledRawJointInitialRightFiniteState, monitor, controller,
      chosen, activation] using hpending

end

end DetParityAutomaton

end DistributedSynthesis
