/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBankLocalHandoff

/-!
# Local handoff from the profiled exceptional block

The first recurrent block is governed by the guarded controller selected at
the initial boundary.  Its receiver carries the local entry row and stages
the certified child as a root of the ordinary profiled bank.  The child
certificate contains all data needed for this switch; no global leader bit is
introduced.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

abbrev ProfiledGuardedFirstRightActiveReceiverControl :=
  Σ key : ProfiledGuardedFirstRightMacro A,
    PairedEntryRow × (profiledGuardedFirstRightMonitorAt A key).State ×
      Option (ProfiledBankLeftMacro A)

abbrev ProfiledGuardedFirstLeftActiveReceiverControl :=
  Σ key : ProfiledGuardedFirstLeftMacro A,
    PairedEntryRow × (profiledGuardedFirstLeftMonitorAt A key).State ×
      Option (ProfiledBankRightMacro A)

noncomputable instance :
    Fintype (ProfiledGuardedFirstRightActiveReceiverControl A) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledGuardedFirstLeftActiveReceiverControl A) := by
  classical
  infer_instance

noncomputable def initialProfiledGuardedFirstRightActiveReceiver
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow) :
    ProfiledGuardedFirstRightActiveReceiverControl A :=
  ⟨key, row, (profiledGuardedFirstRightMonitorAt A key).initial, none⟩

noncomputable def initialProfiledGuardedFirstLeftActiveReceiver
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow) :
    ProfiledGuardedFirstLeftActiveReceiverControl A :=
  ⟨key, row, (profiledGuardedFirstLeftMonitorAt A key).initial, none⟩

noncomputable def stepProfiledGuardedFirstRightOwner
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank) (input : In₁) :
    Out₁ × ProfiledGuardedFirstRightOwnerControl A firstBank :=
  let controller := firstBank.rightController owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepProfiledGuardedFirstLeftOwner
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank) (input : In₂) :
    Out₂ × ProfiledGuardedFirstLeftOwnerControl A firstBank :=
  let controller := firstBank.leftController owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledGuardedFirstRightOwner_key
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank) (input : In₁) :
    (stepProfiledGuardedFirstRightOwner A firstBank owner input).2.1 =
      owner.1 := rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledGuardedFirstLeftOwner_key
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank) (input : In₂) :
    (stepProfiledGuardedFirstLeftOwner A firstBank owner input).2.1 =
      owner.1 := rfl

/-- Turn a checked exceptional right child into the exact left bank root. -/
def profiledBankLeftRootOfFirstRightCertificate
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hrun : (pairedProfiledEntryRunAutomaton A target).HasRationalRun) :
    ProfiledBankLeftMacro A := by
  let feasible : FeasibleProfiledPairedState A := ⟨target, hrun⟩
  cases htarget : target with
  | inl trivial =>
      rw [htarget] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rw [htarget] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          exact profiledBankLeftRoot A feasible leftLive (by simpa [htarget])

/-- Left-to-right mirror. -/
def profiledBankRightRootOfFirstLeftCertificate
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hrun : (pairedProfiledEntryRunAutomaton A target).HasRationalRun) :
    ProfiledBankRightMacro A := by
  let feasible : FeasibleProfiledPairedState A := ⟨target, hrun⟩
  cases htarget : target with
  | inl trivial =>
      rw [htarget] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          exact profiledBankRightRoot A feasible rightLive (by simpa [htarget])
      | inr leftLive =>
          rw [htarget] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledBankLeftRootOfFirstRightCertificate_profile_of_eq
    (target : PairedProfiledTreeState A)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : target = .inr (.inr live))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hrun : (pairedProfiledEntryRunAutomaton A target).HasRationalRun) :
    (profiledBankLeftRootOfFirstRightCertificate A target scan row letter
      herase hrun).2.1.2 = live.2 := by
  subst target
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledBankRightRootOfFirstLeftCertificate_profile_of_eq
    (target : PairedProfiledTreeState A)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : target = .inr (.inl live))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hrun : (pairedProfiledEntryRunAutomaton A target).HasRationalRun) :
    (profiledBankRightRootOfFirstLeftCertificate A target scan row letter
      herase hrun).2.1.2 = live.2 := by
  subst target
  rfl

abbrev ProfiledGuardedFirstRightRoundResult
    (key : ProfiledGuardedFirstRightMacro A) :=
  ProfiledRightReceiverOutput A ×
    (profiledGuardedFirstRightMonitorAt A key).State ×
      Option (ProfiledBankLeftMacro A)

abbrev ProfiledGuardedFirstLeftRoundResult
    (key : ProfiledGuardedFirstLeftMacro A) :=
  ProfiledLeftReceiverOutput A ×
    (profiledGuardedFirstLeftMonitorAt A key).State ×
      Option (ProfiledBankRightMacro A)

noncomputable def stepProfiledGuardedFirstRightReceiverFor
    (key : ProfiledGuardedFirstRightMacro A)
    (ownerControl : (firstBank.rightController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstRightMonitorAt A key).State)
    (move : In₂ × In₁) : ProfiledGuardedFirstRightRoundResult A key := by
  classical
  let controller := firstBank.rightController key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledGuardedFirstRightMonitorAt A key).step
    monitorState (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      (pairedProfiledEntryRunAutomaton A (output.target row)).HasRationalRun then
    exact (output, nextMonitor,
      some (profiledBankLeftRootOfFirstRightCertificate A
        (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

noncomputable def stepProfiledGuardedFirstLeftReceiverFor
    (key : ProfiledGuardedFirstLeftMacro A)
    (ownerControl : (firstBank.leftController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstLeftMonitorAt A key).State)
    (move : In₁ × In₂) : ProfiledGuardedFirstLeftRoundResult A key := by
  classical
  let controller := firstBank.leftController key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledGuardedFirstLeftMonitorAt A key).step
    monitorState (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      (pairedProfiledEntryRunAutomaton A (output.target row)).HasRationalRun then
    exact (output, nextMonitor,
      some (profiledBankRightRootOfFirstLeftCertificate A
        (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem stepProfiledGuardedFirstRightReceiverFor_output
    (key : ProfiledGuardedFirstRightMacro A)
    (ownerControl : (firstBank.rightController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstRightMonitorAt A key).State)
    (move : In₂ × In₁) :
    (stepProfiledGuardedFirstRightReceiverFor A firstBank key ownerControl row
      monitorState move).1 =
      ((firstBank.rightController key).labelOf ownerControl).2
        monitorState move := by
  classical
  simp only [stepProfiledGuardedFirstRightReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledGuardedFirstRightReceiverFor_monitor
    (key : ProfiledGuardedFirstRightMacro A)
    (ownerControl : (firstBank.rightController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstRightMonitorAt A key).State)
    (move : In₂ × In₁) :
    (stepProfiledGuardedFirstRightReceiverFor A firstBank key ownerControl row
      monitorState move).2.1 =
      (profiledGuardedFirstRightMonitorAt A key).step monitorState
        (narrowedRecord (profiledGuardedFirstRightMonitorAt A key)
          ((firstBank.rightController key).labelOf ownerControl)
          monitorState move) := by
  classical
  simp only [stepProfiledGuardedFirstRightReceiverFor, narrowedRecord]
  split <;> rfl

@[simp] theorem stepProfiledGuardedFirstLeftReceiverFor_output
    (key : ProfiledGuardedFirstLeftMacro A)
    (ownerControl : (firstBank.leftController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstLeftMonitorAt A key).State)
    (move : In₁ × In₂) :
    (stepProfiledGuardedFirstLeftReceiverFor A firstBank key ownerControl row
      monitorState move).1 =
      ((firstBank.leftController key).labelOf ownerControl).2
        monitorState move := by
  classical
  simp only [stepProfiledGuardedFirstLeftReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledGuardedFirstLeftReceiverFor_monitor
    (key : ProfiledGuardedFirstLeftMacro A)
    (ownerControl : (firstBank.leftController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstLeftMonitorAt A key).State)
    (move : In₁ × In₂) :
    (stepProfiledGuardedFirstLeftReceiverFor A firstBank key ownerControl row
      monitorState move).2.1 =
      (profiledGuardedFirstLeftMonitorAt A key).step monitorState
        (narrowedRecord (profiledGuardedFirstLeftMonitorAt A key)
          ((firstBank.leftController key).labelOf ownerControl)
          monitorState move) := by
  classical
  simp only [stepProfiledGuardedFirstLeftReceiverFor, narrowedRecord]
  split <;> rfl

theorem stepProfiledGuardedFirstRightReceiverFor_staged_of_safe
    (key : ProfiledGuardedFirstRightMacro A)
    (ownerControl : (firstBank.rightController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstRightMonitorAt A key).State)
    (move : In₂ × In₁)
    (hsafe : erasePairedProfiledState A
          (((firstBank.rightController key).labelOf ownerControl).2
            monitorState move |>.target row) =
        pairedRightCloseTarget A monitorState.2.1 row
          (profiledRightPhysicalLetter A
            (move, ((firstBank.rightController key).labelOf ownerControl).2
              monitorState move,
              ((firstBank.rightController key).labelOf ownerControl).1 move.2)) ∧
      (pairedProfiledEntryRunAutomaton A
        (((firstBank.rightController key).labelOf ownerControl).2
          monitorState move |>.target row)).HasRationalRun) :
    (stepProfiledGuardedFirstRightReceiverFor A firstBank key ownerControl row
      monitorState move).2.2.isSome := by
  classical
  simp [stepProfiledGuardedFirstRightReceiverFor, hsafe]

theorem stepProfiledGuardedFirstLeftReceiverFor_staged_of_safe
    (key : ProfiledGuardedFirstLeftMacro A)
    (ownerControl : (firstBank.leftController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstLeftMonitorAt A key).State)
    (move : In₁ × In₂)
    (hsafe : erasePairedProfiledState A
          (((firstBank.leftController key).labelOf ownerControl).2
            monitorState move |>.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row
          (profiledLeftPhysicalLetter A
            (move, ((firstBank.leftController key).labelOf ownerControl).2
              monitorState move,
              ((firstBank.leftController key).labelOf ownerControl).1 move.2)) ∧
      (pairedProfiledEntryRunAutomaton A
        (((firstBank.leftController key).labelOf ownerControl).2
          monitorState move |>.target row)).HasRationalRun) :
    (stepProfiledGuardedFirstLeftReceiverFor A firstBank key ownerControl row
      monitorState move).2.2.isSome := by
  classical
  simp [stepProfiledGuardedFirstLeftReceiverFor, hsafe]

theorem stepProfiledGuardedFirstRightReceiverFor_pending_of_staged
    (key : ProfiledGuardedFirstRightMacro A)
    (ownerControl : (firstBank.rightController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstRightMonitorAt A key).State)
    (move : In₂ × In₁) (target : ProfiledBankLeftMacro A)
    (hstage : (stepProfiledGuardedFirstRightReceiverFor A firstBank key
      ownerControl row monitorState move).2.2 = some target) :
    (stepProfiledGuardedFirstRightReceiverFor A firstBank key ownerControl row
      monitorState move).2.1.2.2.1 row = some target.2.1.2 := by
  classical
  let controller := firstBank.rightController key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledGuardedFirstRightMonitorAt A key).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      (pairedProfiledEntryRunAutomaton A (output.target row)).HasRationalRun
  · cases htarget : output.target row with
    | inl trivial =>
        rw [htarget] at hsafe
        cases row <;>
          simp [erasePairedProfiledState, pairedRightCloseTarget] at hsafe
    | inr live =>
        cases live with
        | inl rightLive =>
            rw [htarget] at hsafe
            cases row <;>
              simp [erasePairedProfiledState, pairedRightCloseTarget] at hsafe
        | inr leftLive =>
            have hstep :
                stepProfiledGuardedFirstRightReceiverFor A firstBank key
                    ownerControl row monitorState move =
                  (output, nextMonitor,
                    some (profiledBankLeftRootOfFirstRightCertificate A
                      (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledGuardedFirstRightReceiverFor, controller,
                label, output, physical, nextMonitor, hsafe]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.2.1.2 = leftLive.2 := by
              rw [← hstage]
              exact
                profiledBankLeftRootOfFirstRightCertificate_profile_of_eq A
                  (output.target row) leftLive monitorState.2.1 row physical
                    htarget hsafe.1 hsafe.2
            change leftProfileOfProfiledState A (output.target row) =
              some target.2.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
  · have hstep :
        stepProfiledGuardedFirstRightReceiverFor A firstBank key ownerControl
            row monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledGuardedFirstRightReceiverFor, controller, label,
        output, physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

theorem stepProfiledGuardedFirstLeftReceiverFor_pending_of_staged
    (key : ProfiledGuardedFirstLeftMacro A)
    (ownerControl : (firstBank.leftController key).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledGuardedFirstLeftMonitorAt A key).State)
    (move : In₁ × In₂) (target : ProfiledBankRightMacro A)
    (hstage : (stepProfiledGuardedFirstLeftReceiverFor A firstBank key
      ownerControl row monitorState move).2.2 = some target) :
    (stepProfiledGuardedFirstLeftReceiverFor A firstBank key ownerControl row
      monitorState move).2.1.2.2.1 row = some target.2.1.2 := by
  classical
  let controller := firstBank.leftController key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledGuardedFirstLeftMonitorAt A key).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      (pairedProfiledEntryRunAutomaton A (output.target row)).HasRationalRun
  · cases htarget : output.target row with
    | inl trivial =>
        rw [htarget] at hsafe
        cases row <;>
          simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
    | inr live =>
        cases live with
        | inl rightLive =>
            have hstep :
                stepProfiledGuardedFirstLeftReceiverFor A firstBank key
                    ownerControl row monitorState move =
                  (output, nextMonitor,
                    some (profiledBankRightRootOfFirstLeftCertificate A
                      (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledGuardedFirstLeftReceiverFor, controller,
                label, output, physical, nextMonitor, hsafe]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.2.1.2 = rightLive.2 := by
              rw [← hstage]
              exact
                profiledBankRightRootOfFirstLeftCertificate_profile_of_eq A
                  (output.target row) rightLive monitorState.2.1 row physical
                    htarget hsafe.1 hsafe.2
            change rightProfileOfProfiledState A (output.target row) =
              some target.2.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
        | inr leftLive =>
            rw [htarget] at hsafe
            cases row <;>
              simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
  · have hstep :
        stepProfiledGuardedFirstLeftReceiverFor A firstBank key ownerControl
            row monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledGuardedFirstLeftReceiverFor, controller, label,
        output, physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

end

/-! ## Exact finite-state replay -/

abbrev ProfiledGuardedFirstRightFiniteState
    (key : ProfiledGuardedFirstRightMacro A) :=
  (firstBank.rightController key).Control ×
    (profiledGuardedFirstRightMonitorAt A key).State

abbrev ProfiledGuardedFirstLeftFiniteState
    (key : ProfiledGuardedFirstLeftMacro A) :=
  (firstBank.leftController key).Control ×
    (profiledGuardedFirstLeftMonitorAt A key).State

noncomputable def stepProfiledGuardedFirstRightFiniteState
    (key : ProfiledGuardedFirstRightMacro A)
    (state : ProfiledGuardedFirstRightFiniteState A firstBank key)
    (move : In₂ × In₁) :
    ProfiledGuardedFirstRightFiniteState A firstBank key :=
  let controller := firstBank.rightController key
  let monitor := profiledGuardedFirstRightMonitorAt A key
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def stepProfiledGuardedFirstLeftFiniteState
    (key : ProfiledGuardedFirstLeftMacro A)
    (state : ProfiledGuardedFirstLeftFiniteState A firstBank key)
    (move : In₁ × In₂) :
    ProfiledGuardedFirstLeftFiniteState A firstBank key :=
  let controller := firstBank.leftController key
  let monitor := profiledGuardedFirstLeftMonitorAt A key
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledGuardedFirstRightFiniteStateAfter
    (key : ProfiledGuardedFirstRightMacro A) (past : List (In₂ × In₁)) :
    ProfiledGuardedFirstRightFiniteState A firstBank key :=
  past.foldl (stepProfiledGuardedFirstRightFiniteState A firstBank key)
    ((firstBank.rightController key).initial,
      (profiledGuardedFirstRightMonitorAt A key).initial)

noncomputable def profiledGuardedFirstLeftFiniteStateAfter
    (key : ProfiledGuardedFirstLeftMacro A) (past : List (In₁ × In₂)) :
    ProfiledGuardedFirstLeftFiniteState A firstBank key :=
  past.foldl (stepProfiledGuardedFirstLeftFiniteState A firstBank key)
    ((firstBank.leftController key).initial,
      (profiledGuardedFirstLeftMonitorAt A key).initial)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstRightFiniteStateAfter_eq
    (key : ProfiledGuardedFirstRightMacro A) : ∀ past : List (In₂ × In₁),
    profiledGuardedFirstRightFiniteStateAfter A firstBank key past =
      ((firstBank.rightController key).controlAt (senderWord past),
        narrowedControl (profiledGuardedFirstRightMonitorAt A key)
          (firstBank.rightController key).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledGuardedFirstRightFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledGuardedFirstRightFiniteState A firstBank key
        (profiledGuardedFirstRightFiniteStateAfter A firstBank key past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstLeftFiniteStateAfter_eq
    (key : ProfiledGuardedFirstLeftMacro A) : ∀ past : List (In₁ × In₂),
    profiledGuardedFirstLeftFiniteStateAfter A firstBank key past =
      ((firstBank.leftController key).controlAt (senderWord past),
        narrowedControl (profiledGuardedFirstLeftMonitorAt A key)
          (firstBank.leftController key).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledGuardedFirstLeftFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledGuardedFirstLeftFiniteState A firstBank key
        (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

section
omit [Inhabited Out₁] [Inhabited Out₂]

private theorem profiledGuardedFirstRight_treePlay_at_prefix
    (key : ProfiledGuardedFirstRightMacro A) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    let monitor := profiledGuardedFirstRightMonitorAt A key
    let controller := firstBank.rightController key
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

private theorem profiledGuardedFirstLeft_treePlay_at_prefix
    (key : ProfiledGuardedFirstLeftMacro A) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    let monitor := profiledGuardedFirstLeftMonitorAt A key
    let controller := firstBank.leftController key
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

/-- Every real exceptional right-controller round stages its certified
ordinary-bank child. -/
theorem profiledGuardedFirstRight_real_close_staged
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (stepProfiledGuardedFirstRightReceiverFor A firstBank key
      (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1 row
      (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2
      move).2.2.isSome := by
  rw [profiledGuardedFirstRightFiniteStateAfter_eq A firstBank key]
  let monitor := profiledGuardedFirstRightMonitorAt A key
  let controller := firstBank.rightController key
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (firstBank.rightWins key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledGuardedFirstRight_targetsSafe_of_wins A key.1
    key.2.1.1.1 key.2.1.1.2 key.2.1.2
    (treePlay tree env) hwin past.length row
  have hat := profiledGuardedFirstRight_treePlay_at_prefix A firstBank key
    past move
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
  exact stepProfiledGuardedFirstRightReceiverFor_staged_of_safe A firstBank
    key (controller.controlAt (senderWord past)) row
    (narrowedControl monitor controller.labeledTree past) move hsafe

/-- Left mirror. -/
theorem profiledGuardedFirstLeft_real_close_staged
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (stepProfiledGuardedFirstLeftReceiverFor A firstBank key
      (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1 row
      (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2
      move).2.2.isSome := by
  rw [profiledGuardedFirstLeftFiniteStateAfter_eq A firstBank key]
  let monitor := profiledGuardedFirstLeftMonitorAt A key
  let controller := firstBank.leftController key
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (firstBank.leftWins key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledGuardedFirstLeft_targetsSafe_of_wins A key.1
    key.2.1.1.1 key.2.1.1.2 key.2.1.2
    (treePlay tree env) hwin past.length row
  have hat := profiledGuardedFirstLeft_treePlay_at_prefix A firstBank key
    past move
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
  exact stepProfiledGuardedFirstLeftReceiverFor_staged_of_safe A firstBank
    key (controller.controlAt (senderWord past)) row
    (narrowedControl monitor controller.labeledTree past) move hsafe

end

/-! ## Delayed overlap along real exceptional prefixes -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstRight_real_overlap
    (key : ProfiledGuardedFirstRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      (profiledGuardedFirstRightFiniteStateAfter A firstBank key
        past).2.2.2.1 row = some expected) :
    pairedRightClosingForRow row
        (((firstBank.rightController key).labelOf
          (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).1).2
          (profiledGuardedFirstRightFiniteStateAfter A firstBank key past).2
            move).physical = expected (move.2, move.1) := by
  rw [profiledGuardedFirstRightFiniteStateAfter_eq A firstBank key] at hpending ⊢
  let monitor := profiledGuardedFirstRightMonitorAt A key
  let controller := firstBank.rightController key
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (firstBank.rightWins key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := profiledGuardedFirstRight_overlap_of_wins A key.1
    key.2.1.1.1 key.2.1.1.2 key.2.1.2 (treePlay tree env) hwin past.length
    row expected
  have hat := profiledGuardedFirstRight_treePlay_at_prefix A firstBank key
    past move
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

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstLeft_real_overlap
    (key : ProfiledGuardedFirstLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      (profiledGuardedFirstLeftFiniteStateAfter A firstBank key
        past).2.2.2.1 row = some expected) :
    pairedLeftClosingForRow row
        (((firstBank.leftController key).labelOf
          (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).1).2
          (profiledGuardedFirstLeftFiniteStateAfter A firstBank key past).2
            move).physical = expected (move.2, move.1) := by
  rw [profiledGuardedFirstLeftFiniteStateAfter_eq A firstBank key] at hpending ⊢
  let monitor := profiledGuardedFirstLeftMonitorAt A key
  let controller := firstBank.leftController key
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (firstBank.leftWins key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := profiledGuardedFirstLeft_overlap_of_wins A key.1
    key.2.1.1.1 key.2.1.1.2 key.2.1.2 (treePlay tree env) hwin past.length
    row expected
  have hat := profiledGuardedFirstLeft_treePlay_at_prefix A firstBank key
    past move
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


end


end DetParityAutomaton

end DistributedSynthesis
