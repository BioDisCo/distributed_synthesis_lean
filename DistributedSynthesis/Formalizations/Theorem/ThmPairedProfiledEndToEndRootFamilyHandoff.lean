/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyOverlay
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRecurrentHandoff

/-!
# Certified children of an end-to-end restart-root family

The local family overlay is useful recursively only when each of its hidden
members still emits a certified opposite-orientation macro below the same
guarded child and fixed rational policy.  This file proves that closure for
all three EndToEnd monitor sources: the exceptional first block and the two
possible recurrent origins.

The family index remains proof-only.  The sender controller is the one shared
controller of the simultaneous family table; neither process receives the
index, an orientation, or a strict-leader bit.
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

/-! ## Restarted safety inversion -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

private theorem endToEndFirstRight_targetsSafe_of_restartAt_wins
    (key : EndToEndInitialLeftBoundaryKey A package)
    (start : (endToEndFirstRightMonitor A package key).State)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : ((endToEndFirstRightMonitor A package key).restartAt start).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            ((((endToEndFirstRightMonitor A package key).restartAt start).run
              play n).2.1) row (profiledRightPhysicalLetter A (play n)) ∧
        ProfiledGuardedRightPolicyAllows A key.1.2.2.2
          (endToEndInitialLeftBoundaryActivation A package key).profile
          (endToEndInitialLeftBoundaryActivation A package key).policy
          ((play n).2.1.target row) := by
  classical
  let base := endToEndFirstRightMonitor A package key
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change (((((state.2.2.2.2 && _) && _) && decide _) && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt, endToEndFirstRightMonitor,
    endToEndGuardedFirstRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.2

private theorem endToEndFirstLeft_targetsSafe_of_restartAt_wins
    (key : EndToEndInitialRightBoundaryKey A package)
    (start : (endToEndFirstLeftMonitor A package key).State)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : ((endToEndFirstLeftMonitor A package key).restartAt start).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            ((((endToEndFirstLeftMonitor A package key).restartAt start).run
              play n).2.1) row (profiledLeftPhysicalLetter A (play n)) ∧
        ProfiledGuardedLeftPolicyAllows A key.1.2.2.2
          (endToEndInitialRightBoundaryActivation A package key).profile
          (endToEndInitialRightBoundaryActivation A package key).policy
          ((play n).2.1.target row) := by
  classical
  let base := endToEndFirstLeftMonitor A package key
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change (((((state.2.2.2.2 && _) && _) && decide _) && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt, endToEndFirstLeftMonitor,
    endToEndGuardedFirstLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.2

private theorem profiledPolicyRight_targetsSafe_of_restartAt_wins
    {initialState : PairedProfiledTreeState A}
    (policy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (source : ProfiledPolicyRightMacro A policy)
    (start : (profiledPolicyRightMonitor A policy source).State)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : ((profiledPolicyRightMonitor A policy source).restartAt start).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            ((((profiledPolicyRightMonitor A policy source).restartAt start).run
              play n).2.1) row (profiledRightPhysicalLetter A (play n)) ∧
        PairedProfiledRationalPolicy.Allowed A policy
          (.inr (.inl source.1)) ((play n).2.1.target row) := by
  classical
  let base := profiledPolicyRightMonitor A policy source
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt, profiledPolicyRightMonitor,
    profiledRightBlockMonitor, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  exact hsafe.2

private theorem profiledPolicyLeft_targetsSafe_of_restartAt_wins
    {initialState : PairedProfiledTreeState A}
    (policy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (source : ProfiledPolicyLeftMacro A policy)
    (start : (profiledPolicyLeftMonitor A policy source).State)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : ((profiledPolicyLeftMonitor A policy source).restartAt start).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            ((((profiledPolicyLeftMonitor A policy source).restartAt start).run
              play n).2.1) row (profiledLeftPhysicalLetter A (play n)) ∧
        PairedProfiledRationalPolicy.Allowed A policy
          (.inr (.inr source.1)) ((play n).2.1.target row) := by
  classical
  let base := profiledPolicyLeftMonitor A policy source
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt, profiledPolicyLeftMonitor,
    profiledLeftBlockMonitor, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  exact hsafe.2

end

/-! ## Opposite-orientation children -/

/-- Every member of a winning right restart family emits a certified left
macro.  The result records its original boundary summand, so the guarded child
and its fixed policy cannot change at this handoff. -/
noncomputable def endToEndRightFamilyRootChild
    (source : Bool → EndToEndRightRestartRoot A package)
    (family : TransitionRationalTree In₁
      (NarrowedBlockLabel (Bool × In₂) In₁ (ProfiledRightReceiverOutput A) Out₁
        (finiteRootFamilyMonitor
          (endToEndRightFamilyRootMonitors A package source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (endToEndRightFamilyRootMonitors A package source))
      family.labeledTree)
    (index : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) : EndToEndRecurrentLeftMacro A package := by
  let monitor := endToEndRightRestartRootMonitor A package (source index)
  let member := finiteRootMemberController
    (endToEndRightFamilyRootMonitors A package source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (endToEndRightFamilyRootMonitors A package source) family hfamily index
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  let letter := profiledRightPhysicalLetter A (treePlay tree env n)
  rcases hsource : source index with ⟨kind, start⟩
  dsimp [monitor, endToEndRightRestartRootMonitor] at hwin
  rw [hsource] at hwin
  cases kind with
  | first key =>
      have hwin' : ((endToEndFirstRightMonitor A package key).restartAt
          start).WinsPlay (treePlay tree env) := by
        simpa [monitor, endToEndRightRestartRootMonitor,
          EndToEndRightMonitorSource.monitor] using hwin
      have hsafe := endToEndFirstRight_targetsSafe_of_restartAt_wins A package
        key start (treePlay tree env) hwin' n row
      let child : EndToEndGuardedRightChild A key.1.2.2.2
          (endToEndInitialLeftBoundaryActivation A package key).profile
          (endToEndInitialLeftBoundaryActivation A package key).policy :=
        ⟨output.target row, hsafe.2⟩
      exact .inl ⟨key,
        child.recurrentLeftMacroOfClose A
          ((((endToEndFirstRightMonitor A package key).restartAt start).run
            (treePlay tree env) n).2.1) row letter hsafe.1⟩
  | rightOrigin recurrent =>
      have hwin' : ((endToEndGuardedRightRecurrentRightMonitor A
          recurrent.2).restartAt start).WinsPlay (treePlay tree env) := by
        simpa [monitor, endToEndRightRestartRootMonitor,
          EndToEndRightMonitorSource.monitor] using hwin
      have hsafe := profiledPolicyRight_targetsSafe_of_restartAt_wins A
        (recurrent.2.1.policy A) recurrent.2.2 start (treePlay tree env) hwin' n row
      exact .inl ⟨recurrent.1,
        endToEndGuardedRightRecurrentLeftOfRightCertificate A recurrent.2
          (output.target row)
          ((((endToEndGuardedRightRecurrentRightMonitor A
            recurrent.2).restartAt start).run (treePlay tree env) n).2.1)
          row letter hsafe.1 hsafe.2⟩
  | leftOrigin recurrent =>
      have hwin' : ((endToEndGuardedLeftRecurrentRightMonitor A
          recurrent.2).restartAt start).WinsPlay (treePlay tree env) := by
        simpa [monitor, endToEndRightRestartRootMonitor,
          EndToEndRightMonitorSource.monitor] using hwin
      have hsafe := profiledPolicyRight_targetsSafe_of_restartAt_wins A
        (recurrent.2.1.policy A) recurrent.2.2 start (treePlay tree env) hwin' n row
      exact .inr ⟨recurrent.1,
        endToEndGuardedLeftRecurrentLeftOfRightCertificate A recurrent.2
          (output.target row)
          ((((endToEndGuardedLeftRecurrentRightMonitor A
            recurrent.2).restartAt start).run (treePlay tree env) n).2.1)
          row letter hsafe.1 hsafe.2⟩

/-- Left-family mirror. -/
noncomputable def endToEndLeftFamilyRootChild
    (source : Bool → EndToEndLeftRestartRoot A package)
    (family : TransitionRationalTree In₂
      (NarrowedBlockLabel (Bool × In₁) In₂ (ProfiledLeftReceiverOutput A) Out₂
        (finiteRootFamilyMonitor
          (endToEndLeftFamilyRootMonitors A package source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (endToEndLeftFamilyRootMonitors A package source))
      family.labeledTree)
    (index : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) : EndToEndRecurrentRightMacro A package := by
  let monitor := endToEndLeftRestartRootMonitor A package (source index)
  let member := finiteRootMemberController
    (endToEndLeftFamilyRootMonitors A package source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (endToEndLeftFamilyRootMonitors A package source) family hfamily index
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  let letter := profiledLeftPhysicalLetter A (treePlay tree env n)
  rcases hsource : source index with ⟨kind, start⟩
  dsimp [monitor, endToEndLeftRestartRootMonitor] at hwin
  rw [hsource] at hwin
  cases kind with
  | first key =>
      have hwin' : ((endToEndFirstLeftMonitor A package key).restartAt
          start).WinsPlay (treePlay tree env) := by
        simpa [monitor, endToEndLeftRestartRootMonitor,
          EndToEndLeftMonitorSource.monitor] using hwin
      have hsafe := endToEndFirstLeft_targetsSafe_of_restartAt_wins A package
        key start (treePlay tree env) hwin' n row
      let child : EndToEndGuardedLeftChild A key.1.2.2.2
          (endToEndInitialRightBoundaryActivation A package key).profile
          (endToEndInitialRightBoundaryActivation A package key).policy :=
        ⟨output.target row, hsafe.2⟩
      exact .inr ⟨key,
        child.recurrentRightMacroOfClose A
          ((((endToEndFirstLeftMonitor A package key).restartAt start).run
            (treePlay tree env) n).2.1) row letter hsafe.1⟩
  | rightOrigin recurrent =>
      have hwin' : ((endToEndGuardedRightRecurrentLeftMonitor A
          recurrent.2).restartAt start).WinsPlay (treePlay tree env) := by
        simpa [monitor, endToEndLeftRestartRootMonitor,
          EndToEndLeftMonitorSource.monitor] using hwin
      have hsafe := profiledPolicyLeft_targetsSafe_of_restartAt_wins A
        (recurrent.2.1.policy A) recurrent.2.2 start (treePlay tree env) hwin' n row
      exact .inl ⟨recurrent.1,
        endToEndGuardedRightRecurrentRightOfLeftCertificate A recurrent.2
          (output.target row)
          ((((endToEndGuardedRightRecurrentLeftMonitor A
            recurrent.2).restartAt start).run (treePlay tree env) n).2.1)
          row letter hsafe.1 hsafe.2⟩
  | leftOrigin recurrent =>
      have hwin' : ((endToEndGuardedLeftRecurrentLeftMonitor A
          recurrent.2).restartAt start).WinsPlay (treePlay tree env) := by
        simpa [monitor, endToEndLeftRestartRootMonitor,
          EndToEndLeftMonitorSource.monitor] using hwin
      have hsafe := profiledPolicyLeft_targetsSafe_of_restartAt_wins A
        (recurrent.2.1.policy A) recurrent.2.2 start (treePlay tree env) hwin' n row
      exact .inr ⟨recurrent.1,
        endToEndGuardedLeftRecurrentRightOfLeftCertificate A recurrent.2
          (output.target row)
          ((((endToEndGuardedLeftRecurrentLeftMonitor A
            recurrent.2).restartAt start).run (treePlay tree env) n).2.1)
          row letter hsafe.1 hsafe.2⟩

end

end DetParityAutomaton

end DistributedSynthesis
