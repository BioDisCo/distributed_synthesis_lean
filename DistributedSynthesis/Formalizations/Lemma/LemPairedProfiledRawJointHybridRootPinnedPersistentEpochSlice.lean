/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenAutomaticRecutEpochCoupling

/-!
# Cut slices for root-pinned persistent handoffs

This is the smallest bridge from a local narrowed block to the global parity
cuts.  The generic slice-alignment theorem turns literal entry-state, length,
and record-slice equalities into a `cutBlockMin`; the root-pinned physical
priority theorem identifies that minimum with the exact slot of the literal
emitted target macro.

No singleton-policy close-query or parallel slice structure is needed.
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
/-- A right narrowed block aligned with one global cut stages its exact
emitted left macro, whose slot priority is that cut's physical minimum. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentRight_narrowedTarget_cutBlockMin_eq_threadPriority
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.slot.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix
          (treePlay
            (narrowedInducedTree
              (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A
                strategy hwin first source)
              ((bank.right source).1).labeledTree) env)
          n)).length = cuts (k + 1) - cuts k - 1)
    (hslice :
      omegaPrefix (OmegaWord.drop word (start + cuts k))
          (profiledRawJointTargetRightPhysicalPrefixRecords A row
            (omegaPrefix
              (treePlay
                (narrowedInducedTree
                  (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor
                    A strategy hwin first source)
                  ((bank.right source).1).labeledTree) env)
              n)).length =
        profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix
            (treePlay
              (narrowedInducedTree
                (profiledRawJointHybridInitialRootPinnedPersistentRightMonitor
                  A strategy hwin first source)
                ((bank.right source).1).labeledTree) env)
            n)) :
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
        cutBlockMin (fun j ↦ A.priority (A.run word (start + j))) cuts k =
          profiledRawJointThreadRootPriority A (.inr target.slot) := by
  dsimp only
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentRightMonitor A strategy
      hwin first source
  let controller := (bank.right source).1
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  obtain ⟨target, htarget, hallowed, hpriority⟩ :=
    profiledRawJointHybridInitialRootPinnedPersistentRight_narrowedTargetThreadPriority_eq_blockMin
      A strategy hwin first bank source env n row
  have hcut := cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word
    start cuts k (pairedCodeStateForRow A row source.slot.1.1)
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n)) hstate hlength hslice
  exact ⟨target, htarget, hallowed, hcut.trans hpriority.symm⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right cut-slice mirror. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentLeft_narrowedTarget_cutBlockMin_eq_threadPriority
    (bank :
      ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first)
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.slot.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix
          (treePlay
            (narrowedInducedTree
              (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A
                strategy hwin first source)
              ((bank.left source).1).labeledTree) env)
          n)).length = cuts (k + 1) - cuts k - 1)
    (hslice :
      omegaPrefix (OmegaWord.drop word (start + cuts k))
          (profiledRawJointTargetLeftPhysicalPrefixRecords A row
            (omegaPrefix
              (treePlay
                (narrowedInducedTree
                  (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor
                    A strategy hwin first source)
                  ((bank.left source).1).labeledTree) env)
              n)).length =
        profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (treePlay
              (narrowedInducedTree
                (profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A
                  strategy hwin first source)
                ((bank.left source).1).labeledTree) env)
            n)) :
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
        cutBlockMin (fun j ↦ A.priority (A.run word (start + j))) cuts k =
          profiledRawJointThreadRootPriority A (.inl target.slot) := by
  dsimp only
  let monitor :=
    profiledRawJointHybridInitialRootPinnedPersistentLeftMonitor A strategy
      hwin first source
  let controller := (bank.left source).1
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  obtain ⟨target, htarget, hallowed, hpriority⟩ :=
    profiledRawJointHybridInitialRootPinnedPersistentLeft_narrowedTargetThreadPriority_eq_blockMin
      A strategy hwin first bank source env n row
  have hcut := cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word
    start cuts k (pairedCodeStateForRow A row source.slot.1.1)
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n)) hstate hlength hslice
  exact ⟨target, htarget, hallowed, hcut.trans hpriority.symm⟩

end

end DetParityAutomaton

end DistributedSynthesis
