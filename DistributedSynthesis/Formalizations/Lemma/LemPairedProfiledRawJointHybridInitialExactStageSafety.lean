/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialExactTaggedChildFamily
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyHandoff

/-!
# Reachable exact-stage safety for the pinned initial block

`StageOfChild` is total: malformed unreachable targets fall back to a
canonical exact root child.  On every branch of the selected all-thread
winning controller, however, the exceptional monitor forces the emitted
target to expose the required opposite live slot.  Consequently the total
constructor retains the controller target exactly.

This file packages that reachable fact for both orientations and exposes the
exact tag, root-state, root-slot, and active-slot equations used by the finite
front adapter.  No runtime control is strengthened and no graph, side, or
strict-leader bit is introduced.
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

/-! ## Selected controller plays and their staged targets -/

noncomputable def profiledRawJointHybridInitialImmediateRightControllerPlay
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) :=
  let monitor :=
    profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

noncomputable def profiledRawJointHybridInitialImmediateLeftControllerPlay
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) :=
  let monitor :=
    profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

abbrev ProfiledRawJointHybridInitialImmediateRightControllerChild
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :=
  (profiledRawJointHybridInitialImmediateRightControllerPlay A strategy hwin
    first env n).2.1.target row

abbrev ProfiledRawJointHybridInitialImmediateLeftControllerChild
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :=
  (profiledRawJointHybridInitialImmediateLeftControllerPlay A strategy hwin
    first env n).2.1.target row

noncomputable def profiledRawJointHybridInitialImmediateRightControllerStage
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :=
  profiledRawJointHybridInitialImmediateRightStageOfChild A strategy hwin first
    (ProfiledRawJointHybridInitialImmediateRightControllerChild A strategy hwin
      first env n row)

noncomputable def profiledRawJointHybridInitialImmediateLeftControllerStage
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :=
  profiledRawJointHybridInitialImmediateLeftStageOfChild A strategy hwin first
    (ProfiledRawJointHybridInitialImmediateLeftControllerChild A strategy hwin
      first env n row)

/-! ## All-thread safety forces the live branch -/

theorem
    exists_profiledRawJointHybridInitialImmediateRightControllerChild_active
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      (ProfiledRawJointHybridInitialImmediateRightControllerChild A strategy
        hwin first env n row).1.family.left () = some slot := by
  let initial :=
    ProfiledRawJointHybridInitialImmediateRightSource A strategy first
  let RootPred :=
    profiledRawJointHybridInitialImmediateRightRootPredicate A strategy first
  let package :=
    profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first
  let source :=
    (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procOneSlot A
  let monitor :=
    profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (profiledRawJointHybridInitialImmediateRightController_wins A strategy
        hwin first)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  have hbasePlay :
      (ProfiledRawJointHybridInitialImmediateRightBaseMonitor A strategy hwin
        first).WinsPlay play := by
    apply
      (ProfiledRawJointHybridInitialImmediateRightBaseMonitor A strategy hwin
        first).rootPinned_base_wins_of_wins
        (profiledRawJointHybridInitialImmediateRightRootRecord A strategy hwin
          first) play
    simpa only [profiledRawJointHybridInitialImmediateRightMonitor] using hplay
  simpa only [ProfiledRawJointHybridInitialImmediateRightControllerChild,
    profiledRawJointHybridInitialImmediateRightControllerPlay] using
    (exists_profiledRawJointGuardedFirstRight_target_active_slot_of_wins A
      strategy initial RootPred package source play hbasePlay n row)

theorem
    exists_profiledRawJointHybridInitialImmediateLeftControllerChild_active
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      (ProfiledRawJointHybridInitialImmediateLeftControllerChild A strategy
        hwin first env n row).1.family.right () = some slot := by
  let initial :=
    ProfiledRawJointHybridInitialImmediateLeftSource A strategy first
  let RootPred :=
    profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first
  let package :=
    profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first
  let source :=
    (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procTwoSlot A
  let monitor :=
    profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (profiledRawJointHybridInitialImmediateLeftController_wins A strategy
        hwin first)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  have hbasePlay :
      (ProfiledRawJointHybridInitialImmediateLeftBaseMonitor A strategy hwin
        first).WinsPlay play := by
    apply
      (ProfiledRawJointHybridInitialImmediateLeftBaseMonitor A strategy hwin
        first).rootPinned_base_wins_of_wins
        (profiledRawJointHybridInitialImmediateLeftRootRecord A strategy hwin
          first) play
    simpa only [profiledRawJointHybridInitialImmediateLeftMonitor] using hplay
  simpa only [ProfiledRawJointHybridInitialImmediateLeftControllerChild,
    profiledRawJointHybridInitialImmediateLeftControllerPlay] using
    (exists_profiledRawJointGuardedFirstLeft_target_active_slot_of_wins A
      strategy initial RootPred package source play hbasePlay n row)

/-- On every reachable right-controller letter, total staging retains the
emitted target exactly. -/
@[simp] theorem
    profiledRawJointHybridInitialImmediateRightStageOfControllerChild_exact
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialImmediateRightControllerStage A strategy hwin
      first env n row).child =
      ProfiledRawJointHybridInitialImmediateRightControllerChild A strategy
        hwin first env n row := by
  exact
    profiledRawJointHybridInitialImmediateRightStageOfChild_child_of_active A
      strategy hwin first _
      (exists_profiledRawJointHybridInitialImmediateRightControllerChild_active
        A strategy hwin first env n row)

/-- Left-controller mirror. -/
@[simp] theorem
    profiledRawJointHybridInitialImmediateLeftStageOfControllerChild_exact
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialImmediateLeftControllerStage A strategy hwin
      first env n row).child =
      ProfiledRawJointHybridInitialImmediateLeftControllerChild A strategy hwin
        first env n row := by
  exact
    profiledRawJointHybridInitialImmediateLeftStageOfChild_child_of_active A
      strategy hwin first _
      (exists_profiledRawJointHybridInitialImmediateLeftControllerChild_active
        A strategy hwin first env n row)

theorem
    profiledRawJointHybridInitialImmediateRightControllerStage_active_slot
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    (ProfiledRawJointHybridInitialImmediateRightControllerChild A strategy hwin
      first env n row).1.family.left () =
      some (profiledRawJointHybridInitialImmediateRightControllerStage A
        strategy hwin first env n row).slot := by
  rw [← profiledRawJointHybridInitialImmediateRightStageOfControllerChild_exact
    A strategy hwin first env n row]
  exact
    (profiledRawJointHybridInitialImmediateRightControllerStage A strategy hwin
      first env n row).active_slot

theorem
    profiledRawJointHybridInitialImmediateLeftControllerStage_active_slot
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    (ProfiledRawJointHybridInitialImmediateLeftControllerChild A strategy hwin
      first env n row).1.family.right () =
      some (profiledRawJointHybridInitialImmediateLeftControllerStage A
        strategy hwin first env n row).slot := by
  rw [← profiledRawJointHybridInitialImmediateLeftStageOfControllerChild_exact
    A strategy hwin first env n row]
  exact
    (profiledRawJointHybridInitialImmediateLeftControllerStage A strategy hwin
      first env n row).active_slot

/-! ## Exact tags and recurrent roots exposed to the front adapter -/

def profiledRawJointHybridInitialExactRightControllerTargetTag
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inl ⟨first,
    ProfiledRawJointHybridInitialImmediateRightControllerChild A strategy hwin
      first env n row⟩

def profiledRawJointHybridInitialExactLeftControllerTargetTag
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inr ⟨first,
    ProfiledRawJointHybridInitialImmediateLeftControllerChild A strategy hwin
      first env n row⟩

def profiledRawJointHybridInitialExactRightControllerStageTag
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inl ⟨first,
    (profiledRawJointHybridInitialImmediateRightControllerStage A strategy hwin
      first env n row).child⟩

def profiledRawJointHybridInitialExactLeftControllerStageTag
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inr ⟨first,
    (profiledRawJointHybridInitialImmediateLeftControllerStage A strategy hwin
      first env n row).child⟩

@[simp] theorem
    profiledRawJointHybridInitialExactRightControllerStageTag_eq_target
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    profiledRawJointHybridInitialExactRightControllerStageTag A strategy hwin
        first env n row =
      profiledRawJointHybridInitialExactRightControllerTargetTag A strategy hwin
        first env n row := by
  rw [profiledRawJointHybridInitialExactRightControllerStageTag,
    profiledRawJointHybridInitialExactRightControllerTargetTag,
    profiledRawJointHybridInitialImmediateRightStageOfControllerChild_exact A
      strategy hwin first env n row]

@[simp] theorem
    profiledRawJointHybridInitialExactLeftControllerStageTag_eq_target
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    profiledRawJointHybridInitialExactLeftControllerStageTag A strategy hwin
        first env n row =
      profiledRawJointHybridInitialExactLeftControllerTargetTag A strategy hwin
        first env n row := by
  rw [profiledRawJointHybridInitialExactLeftControllerStageTag,
    profiledRawJointHybridInitialExactLeftControllerTargetTag,
    profiledRawJointHybridInitialImmediateLeftStageOfControllerChild_exact A
      strategy hwin first env n row]

noncomputable def
    profiledRawJointHybridInitialExactRightControllerStageRoot
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let tag :=
      profiledRawJointHybridInitialExactRightControllerStageTag A strategy hwin
        first env n row
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        tag).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        tag) :=
  profiledRawJointHybridInitialExactRightStageChildRootMacro A strategy hwin
    first
    (profiledRawJointHybridInitialImmediateRightControllerStage A strategy hwin
      first env n row)

noncomputable def
    profiledRawJointHybridInitialExactLeftControllerStageRoot
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let tag :=
      profiledRawJointHybridInitialExactLeftControllerStageTag A strategy hwin
        first env n row
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        tag).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        tag) :=
  profiledRawJointHybridInitialExactLeftStageChildRootMacro A strategy hwin first
    (profiledRawJointHybridInitialImmediateLeftControllerStage A strategy hwin
      first env n row)

@[simp] theorem
    profiledRawJointHybridInitialExactRightControllerStageRoot_state
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialExactRightControllerStageRoot A strategy hwin
      first env n row).state =
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridInitialExactRightControllerStageTag A strategy
          hwin first env n row)).run [] :=
  rfl

@[simp] theorem
    profiledRawJointHybridInitialExactLeftControllerStageRoot_state
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialExactLeftControllerStageRoot A strategy hwin
      first env n row).state =
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridInitialExactLeftControllerStageTag A strategy
          hwin first env n row)).run [] :=
  rfl

@[simp] theorem
    profiledRawJointHybridInitialExactRightControllerStageRoot_slot
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialExactRightControllerStageRoot A strategy hwin
      first env n row).slot =
      (profiledRawJointHybridInitialImmediateRightControllerStage A strategy
        hwin first env n row).slot :=
  rfl

@[simp] theorem
    profiledRawJointHybridInitialExactLeftControllerStageRoot_slot
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    (profiledRawJointHybridInitialExactLeftControllerStageRoot A strategy hwin
      first env n row).slot =
      (profiledRawJointHybridInitialImmediateLeftControllerStage A strategy hwin
        first env n row).slot :=
  rfl

theorem profiledRawJointHybridInitialExactRightControllerStageRoot_active_slot
    (first : In₁ × In₂) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    ((profiledRawJointHybridInitialExactRightControllerStageRoot A strategy hwin
      first env n row).state).1.family.left () =
      some (profiledRawJointHybridInitialExactRightControllerStageRoot A
        strategy hwin first env n row).slot :=
  (profiledRawJointHybridInitialExactRightControllerStageRoot A strategy hwin
    first env n row).active_slot

theorem profiledRawJointHybridInitialExactLeftControllerStageRoot_active_slot
    (first : In₁ × In₂) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    ((profiledRawJointHybridInitialExactLeftControllerStageRoot A strategy hwin
      first env n row).state).1.family.right () =
      some (profiledRawJointHybridInitialExactLeftControllerStageRoot A strategy
        hwin first env n row).slot :=
  (profiledRawJointHybridInitialExactLeftControllerStageRoot A strategy hwin
    first env n row).active_slot

end

end DetParityAutomaton

end DistributedSynthesis
