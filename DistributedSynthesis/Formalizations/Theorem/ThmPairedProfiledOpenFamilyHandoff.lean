/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenFamilyMove

/-!
# Certified handoff for pre-policy root families

A winning simultaneous open-family table emits exact profiled children whose
input-free languages have rational runs.  This file reads those certificates
back as finite opposite-orientation open roots.  No inner transition policy is
selected during the handoff.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited I] [Fintype I] [DecidableEq I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

noncomputable abbrev profiledOpenRightRootMonitors
    (source : I → ProfiledOpenRightRoot A) :=
  fun index => profiledOpenRightRootMonitor A (source index)

noncomputable abbrev profiledOpenLeftRootMonitors
    (source : I → ProfiledOpenLeftRoot A) :=
  fun index => profiledOpenLeftRootMonitor A (source index)

/-- Correct erasure plus rational nonemptiness retypes a right close as an
open left root. -/
noncomputable def profiledOpenLeftRootOfRightCertificate
    (target : PairedProfiledTreeState A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hrational : (pairedProfiledEntryRunAutomaton A target).HasRationalRun) :
    ProfiledOpenLeftRoot A := by
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive => exact ⟨leftLive, hrational⟩

/-- Left-to-right mirror. -/
noncomputable def profiledOpenRightRootOfLeftCertificate
    (target : PairedProfiledTreeState A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hrational : (pairedProfiledEntryRunAutomaton A target).HasRationalRun) :
    ProfiledOpenRightRoot A := by
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive => exact ⟨rightLive, hrational⟩
      | inr leftLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
private theorem profiledOpenRight_targetsSafe_of_wins
    (root : ProfiledOpenRightRoot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledOpenRightRootMonitor A root).WinsPlay play)
    (n : Nat) : ∀ row, ∃ live :
      (((A.State × A.State) × A.State) ×
        LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)),
      (play n).2.1.target row = .inr (.inr live) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  let base := profiledOpenRightRootMonitor A root
  have hwin' : (base.restartAt base.initial).WinsPlay play := by
    simpa [base, BlockRecordMonitor.restartAt] using hwin
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
    base.initial play hwin' (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, profiledOpenRightRootMonitor,
    BlockRecordMonitor.restartAt, profiledOpenRightBlockMonitor,
    Bool.and_eq_true, decide_eq_true_eq] at hsafe
  intro row
  have hrow := hsafe.2 row
  generalize htarget : (play n).2.1.target row = target at hrow ⊢
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at hrow
  | inr live =>
      cases live with
      | inl rightLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at hrow
      | inr leftLive => exact ⟨leftLive, rfl, hrow.2⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
private theorem profiledOpenLeft_targetsSafe_of_wins
    (root : ProfiledOpenLeftRoot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledOpenLeftRootMonitor A root).WinsPlay play)
    (n : Nat) : ∀ row, ∃ live :
      (((A.State × A.State) × A.State) ×
        RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)),
      (play n).2.1.target row = .inr (.inl live) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  let base := profiledOpenLeftRootMonitor A root
  have hwin' : (base.restartAt base.initial).WinsPlay play := by
    simpa [base, BlockRecordMonitor.restartAt] using hwin
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
    base.initial play hwin' (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, profiledOpenLeftRootMonitor,
    BlockRecordMonitor.restartAt, profiledOpenLeftBlockMonitor,
    Bool.and_eq_true, decide_eq_true_eq] at hsafe
  intro row
  have hrow := hsafe.2 row
  generalize htarget : (play n).2.1.target row = target at hrow ⊢
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at hrow
  | inr live =>
      cases live with
      | inl rightLive => exact ⟨rightLive, rfl, hrow.2⟩
      | inr leftLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at hrow

/-- Every projected certificate of a winning right-family table is a genuine
open left root. -/
noncomputable def profiledOpenRightFamilyChild
    (source : I → ProfiledOpenRightRoot A)
    (family : TransitionRationalTree In₁
      (NarrowedBlockLabel (I × In₂) In₁ (ProfiledRightReceiverOutput A)
        Out₁ (finiteRootFamilyMonitor
          (profiledOpenRightRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledOpenRightRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) : ProfiledOpenLeftRoot A := by
  let monitor := profiledOpenRightRootMonitor A (source index)
  let member := finiteRootMemberController
    (profiledOpenRightRootMonitors A source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (profiledOpenRightRootMonitors A source) family hfamily index
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  have hsafe := profiledOpenRight_targetsSafe_of_wins A (source index)
    (treePlay tree env) hwin n row
  exact ⟨hsafe.choose, by
    rw [hsafe.choose_spec.1] at hsafe
    exact hsafe.choose_spec.2⟩

/-- Left-family mirror. -/
noncomputable def profiledOpenLeftFamilyChild
    (source : I → ProfiledOpenLeftRoot A)
    (family : TransitionRationalTree In₂
      (NarrowedBlockLabel (I × In₁) In₂ (ProfiledLeftReceiverOutput A)
        Out₂ (finiteRootFamilyMonitor
          (profiledOpenLeftRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledOpenLeftRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) : ProfiledOpenRightRoot A := by
  let monitor := profiledOpenLeftRootMonitor A (source index)
  let member := finiteRootMemberController
    (profiledOpenLeftRootMonitors A source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (profiledOpenLeftRootMonitors A source) family hfamily index
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  have hsafe := profiledOpenLeft_targetsSafe_of_wins A (source index)
    (treePlay tree env) hwin n row
  exact ⟨hsafe.choose, by
    rw [hsafe.choose_spec.1] at hsafe
    exact hsafe.choose_spec.2⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
