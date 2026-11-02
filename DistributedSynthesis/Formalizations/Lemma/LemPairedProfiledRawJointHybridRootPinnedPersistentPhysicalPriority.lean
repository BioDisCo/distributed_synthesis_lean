/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentLocalHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointTargetPhysicalPriority

/-!
# Literal physical minima at root-pinned persistent handoffs

The target-parametric block theorem identifies the priority of a narrowed
controller's emitted target with the minimum priority of its literal physical
prefix.  The fixed-first handoff then inverts that same emitted target into an
opposite live macro of the original guarded policy.

The result below is stated on that exact staged slot.  It does not replace the
emitted target by the activation's target table or by a canonical close key.
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
  (first : In₁ × In₂)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A right narrowed-controller letter stages its literal emitted left macro,
and the root priority of that exact left slot is the physical block minimum. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentRight_narrowedTargetThreadPriority_eq_blockMin
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
        hwin first source
    let controller := (bank.right source).1
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ target :
        ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
          hwin first,
      target.key.state = (play n).2.1.target row ∧
        ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
          first source.key.state target.key.state ∧
        profiledRawJointThreadRootPriority A (.inr target.slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.slot.1.1)
              (profiledRawJointTargetRightPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  dsimp only
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
      hwin first source
  let controller := (bank.right source).1
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  obtain ⟨target, htarget, hallowed⟩ :=
    profiledRawJointHybridInitialRootPinnedPersistentRight_narrowedTargetMacro
      A strategy hwin first bank source env n row
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (bank.right source).2
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hpriority :=
    profiledRawJointTargetRight_targetPriority_eq_blockMin_of_wins A
      (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A)
      (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first source.key.state)
      source.slot play hplay n row
  have htargetProfile :
      profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A
          ((play n).2.1.target row) =
        .inr (.inr target.slot) := by
    rw [← htarget]
    exact
      profiledRawJointHybridInitialRootPinnedRightTargetProfiledState_eq A
        target.key.state target.key.incidenceCode target.slot
          target.key.state_code target.active_slot
  refine ⟨target, htarget, hallowed, ?_⟩
  calc
    profiledRawJointThreadRootPriority A (.inr target.slot) =
        pairedProfiledEntryPriority A
          (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A
            ((play n).2.1.target row)) := by rw [htargetProfile]; rfl
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointTargetRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := hpriority

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left narrowed-controller mirror. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentLeft_narrowedTargetThreadPriority_eq_blockMin
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
        hwin first source
    let controller := (bank.left source).1
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ target :
        ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
          hwin first,
      target.key.state = (play n).2.1.target row ∧
        ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
          first source.key.state target.key.state ∧
        profiledRawJointThreadRootPriority A (.inl target.slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.slot.1.1)
              (profiledRawJointTargetLeftPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  dsimp only
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
      hwin first source
  let controller := (bank.left source).1
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  obtain ⟨target, htarget, hallowed⟩ :=
    profiledRawJointHybridInitialRootPinnedPersistentLeft_narrowedTargetMacro A
      strategy hwin first bank source env n row
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (bank.left source).2
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hpriority :=
    profiledRawJointTargetLeft_targetPriority_eq_blockMin_of_wins A
      (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A)
      (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first source.key.state)
      source.slot play hplay n row
  have htargetProfile :
      profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A
          ((play n).2.1.target row) =
        .inr (.inl target.slot) := by
    rw [← htarget]
    exact
      profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState_eq A
        target.key.state target.key.incidenceCode target.slot
          target.key.state_code target.active_slot
  refine ⟨target, htarget, hallowed, ?_⟩
  calc
    profiledRawJointThreadRootPriority A (.inl target.slot) =
        pairedProfiledEntryPriority A
          (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A
            ((play n).2.1.target row)) := by rw [htargetProfile]; rfl
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointTargetLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := hpriority

end

end DetParityAutomaton

end DistributedSynthesis
