/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedInitialHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledFeasiblePolicyBank

/-!
# Finite local handoff in the profiled recurrent bank

This is the operational layer of the profiled recurrent construction.  A
blind owner stores only its finite controller state.  The receiver stores the
same finite bank key, its locally observed entry row, the certificate-monitor
state, and an optional opposite-orientation key staged by the current
certificate.

The target certificate is checked against the physical close and the fixed
rational policy before it is converted into the next bank key.  No transition
tests which process is the strict leader.
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

/-! ## Finite local controls -/

abbrev ProfiledBankRightOwnerControl :=
  Σ source : ProfiledBankRightMacro A,
    (profiledBankRightController A source).Control

abbrev ProfiledBankLeftOwnerControl :=
  Σ source : ProfiledBankLeftMacro A,
    (profiledBankLeftController A source).Control

abbrev ProfiledBankRightReceiverControl :=
  Σ source : ProfiledBankRightMacro A,
    PairedEntryRow × (profiledBankRightMonitor A source).State ×
      Option (ProfiledBankLeftMacro A)

abbrev ProfiledBankLeftReceiverControl :=
  Σ source : ProfiledBankLeftMacro A,
    PairedEntryRow × (profiledBankLeftMonitor A source).State ×
      Option (ProfiledBankRightMacro A)

noncomputable instance : Fintype (ProfiledBankRightOwnerControl A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledBankLeftOwnerControl A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledBankRightReceiverControl A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledBankLeftReceiverControl A) := by
  classical
  infer_instance

noncomputable def initialProfiledBankRightOwner
    (source : ProfiledBankRightMacro A) : ProfiledBankRightOwnerControl A :=
  ⟨source, (profiledBankRightController A source).initial⟩

noncomputable def initialProfiledBankLeftOwner
    (source : ProfiledBankLeftMacro A) : ProfiledBankLeftOwnerControl A :=
  ⟨source, (profiledBankLeftController A source).initial⟩

noncomputable def initialProfiledBankRightReceiver
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow) :
    ProfiledBankRightReceiverControl A :=
  ⟨source, row, (profiledBankRightMonitor A source).initial, none⟩

noncomputable def initialProfiledBankLeftReceiver
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow) :
    ProfiledBankLeftReceiverControl A :=
  ⟨source, row, (profiledBankLeftMonitor A source).initial, none⟩

noncomputable def stepProfiledBankRightOwner
    (owner : ProfiledBankRightOwnerControl A) (input : In₁) :
    Out₁ × ProfiledBankRightOwnerControl A :=
  let controller := profiledBankRightController A owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepProfiledBankLeftOwner
    (owner : ProfiledBankLeftOwnerControl A) (input : In₂) :
    Out₂ × ProfiledBankLeftOwnerControl A :=
  let controller := profiledBankLeftController A owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem stepProfiledBankRightOwner_source
    (owner : ProfiledBankRightOwnerControl A) (input : In₁) :
    (stepProfiledBankRightOwner A owner input).2.1 = owner.1 := rfl

@[simp] theorem stepProfiledBankLeftOwner_source
    (owner : ProfiledBankLeftOwnerControl A) (input : In₂) :
    (stepProfiledBankLeftOwner A owner input).2.1 = owner.1 := rfl

/-! ## Certified target inversion and staging -/

/-- A checked right-block certificate has the left-live shape and therefore
defines the next bank macro. -/
def profiledBankLeftMacroOfRightCertificate
    (source : ProfiledBankRightMacro A)
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1)) target) :
    ProfiledBankLeftMacro A := by
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
          exact profiledBankStageLeftOfAllowed A source leftLive
            (by simpa [htarget] using hallowed)

/-- Left-to-right mirror. -/
def profiledBankRightMacroOfLeftCertificate
    (source : ProfiledBankLeftMacro A)
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1)) target) :
    ProfiledBankRightMacro A := by
  cases htarget : target with
  | inl trivial =>
      rw [htarget] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          exact profiledBankStageRightOfAllowed A source rightLive
            (by simpa [htarget] using hallowed)
      | inr leftLive =>
          rw [htarget] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂]

@[simp] theorem profiledBankLeftMacroOfRightCertificate_profile
    (source : ProfiledBankRightMacro A)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A (.inr (.inr live)) =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1))
        (.inr (.inr live))) :
    (profiledBankLeftMacroOfRightCertificate A source (.inr (.inr live))
      scan row letter herase hallowed).2.1.2 = live.2 := by
  rfl

theorem profiledBankLeftMacroOfRightCertificate_profile_of_eq
    (source : ProfiledBankRightMacro A) (target : PairedProfiledTreeState A)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : target = .inr (.inr live))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1)) target) :
    (profiledBankLeftMacroOfRightCertificate A source target scan row letter
      herase hallowed).2.1.2 = live.2 := by
  subst target
  rfl

@[simp] theorem profiledBankRightMacroOfLeftCertificate_profile
    (source : ProfiledBankLeftMacro A)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A (.inr (.inl live)) =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1))
        (.inr (.inl live))) :
    (profiledBankRightMacroOfLeftCertificate A source (.inr (.inl live))
      scan row letter herase hallowed).2.1.2 = live.2 := by
  rfl

theorem profiledBankRightMacroOfLeftCertificate_profile_of_eq
    (source : ProfiledBankLeftMacro A) (target : PairedProfiledTreeState A)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : target = .inr (.inl live))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1)) target) :
    (profiledBankRightMacroOfLeftCertificate A source target scan row letter
      herase hallowed).2.1.2 = live.2 := by
  subst target
  rfl

end

abbrev ProfiledBankRightReceiverRoundResult
    (source : ProfiledBankRightMacro A) :=
  ProfiledRightReceiverOutput A ×
    (profiledBankRightMonitor A source).State ×
      Option (ProfiledBankLeftMacro A)

abbrev ProfiledBankLeftReceiverRoundResult
    (source : ProfiledBankLeftMacro A) :=
  ProfiledLeftReceiverOutput A ×
    (profiledBankLeftMonitor A source).State ×
      Option (ProfiledBankRightMacro A)

/-- One full-information receiver computation.  The certificate test is
finite and depends only on the current local monitor state and received owner
summary. -/
noncomputable def stepProfiledBankRightReceiverFor
    (source : ProfiledBankRightMacro A)
    (ownerControl : (profiledBankRightController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankRightMonitor A source).State)
    (move : In₂ × In₁) : ProfiledBankRightReceiverRoundResult A source := by
  classical
  let controller := profiledBankRightController A source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledBankRightMonitor A source).step monitorState
    (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1))
        (output.target row) then
    exact (output, nextMonitor,
      some (profiledBankLeftMacroOfRightCertificate A source
        (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

/-- Process-one/left-block mirror. -/
noncomputable def stepProfiledBankLeftReceiverFor
    (source : ProfiledBankLeftMacro A)
    (ownerControl : (profiledBankLeftController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankLeftMonitor A source).State)
    (move : In₁ × In₂) : ProfiledBankLeftReceiverRoundResult A source := by
  classical
  let controller := profiledBankLeftController A source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledBankLeftMonitor A source).step monitorState
    (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1))
        (output.target row) then
    exact (output, nextMonitor,
      some (profiledBankRightMacroOfLeftCertificate A source
        (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

@[simp] theorem stepProfiledBankRightReceiverFor_output
    (source : ProfiledBankRightMacro A)
    (ownerControl : (profiledBankRightController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankRightMonitor A source).State)
    (move : In₂ × In₁) :
    (stepProfiledBankRightReceiverFor A source ownerControl row monitorState
      move).1 =
      ((profiledBankRightController A source).labelOf ownerControl).2
        monitorState move := by
  classical
  simp only [stepProfiledBankRightReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledBankRightReceiverFor_monitor
    (source : ProfiledBankRightMacro A)
    (ownerControl : (profiledBankRightController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankRightMonitor A source).State)
    (move : In₂ × In₁) :
    (stepProfiledBankRightReceiverFor A source ownerControl row monitorState
      move).2.1 =
      (profiledBankRightMonitor A source).step monitorState
        (narrowedRecord (profiledBankRightMonitor A source)
          ((profiledBankRightController A source).labelOf ownerControl)
          monitorState move) := by
  classical
  simp only [stepProfiledBankRightReceiverFor, narrowedRecord]
  split <;> rfl

@[simp] theorem stepProfiledBankLeftReceiverFor_output
    (source : ProfiledBankLeftMacro A)
    (ownerControl : (profiledBankLeftController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankLeftMonitor A source).State)
    (move : In₁ × In₂) :
    (stepProfiledBankLeftReceiverFor A source ownerControl row monitorState
      move).1 =
      ((profiledBankLeftController A source).labelOf ownerControl).2
        monitorState move := by
  classical
  simp only [stepProfiledBankLeftReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledBankLeftReceiverFor_monitor
    (source : ProfiledBankLeftMacro A)
    (ownerControl : (profiledBankLeftController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankLeftMonitor A source).State)
    (move : In₁ × In₂) :
    (stepProfiledBankLeftReceiverFor A source ownerControl row monitorState
      move).2.1 =
      (profiledBankLeftMonitor A source).step monitorState
        (narrowedRecord (profiledBankLeftMonitor A source)
          ((profiledBankLeftController A source).labelOf ownerControl)
          monitorState move) := by
  classical
  simp only [stepProfiledBankLeftReceiverFor, narrowedRecord]
  split <;> rfl

theorem stepProfiledBankRightReceiverFor_staged_of_safe
    (source : ProfiledBankRightMacro A)
    (ownerControl : (profiledBankRightController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankRightMonitor A source).State)
    (move : In₂ × In₁)
    (hsafe : erasePairedProfiledState A
          (((profiledBankRightController A source).labelOf ownerControl).2
            monitorState move |>.target row) =
        pairedRightCloseTarget A monitorState.2.1 row
          (profiledRightPhysicalLetter A
            (move,
              ((profiledBankRightController A source).labelOf ownerControl).2
                monitorState move,
              ((profiledBankRightController A source).labelOf ownerControl).1
                move.2)) ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1))
        (((profiledBankRightController A source).labelOf ownerControl).2
          monitorState move |>.target row)) :
    (stepProfiledBankRightReceiverFor A source ownerControl row monitorState
      move).2.2.isSome := by
  classical
  simp [stepProfiledBankRightReceiverFor, hsafe]

theorem stepProfiledBankLeftReceiverFor_staged_of_safe
    (source : ProfiledBankLeftMacro A)
    (ownerControl : (profiledBankLeftController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankLeftMonitor A source).State)
    (move : In₁ × In₂)
    (hsafe : erasePairedProfiledState A
          (((profiledBankLeftController A source).labelOf ownerControl).2
            monitorState move |>.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row
          (profiledLeftPhysicalLetter A
            (move,
              ((profiledBankLeftController A source).labelOf ownerControl).2
                monitorState move,
              ((profiledBankLeftController A source).labelOf ownerControl).1
                move.2)) ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1))
        (((profiledBankLeftController A source).labelOf ownerControl).2
          monitorState move |>.target row)) :
    (stepProfiledBankLeftReceiverFor A source ownerControl row monitorState
      move).2.2.isSome := by
  classical
  simp [stepProfiledBankLeftReceiverFor, hsafe]

/-- A staged left macro carries exactly the profile installed in the next
right-monitor pending slot. -/
theorem stepProfiledBankRightReceiverFor_pending_of_staged
    (source : ProfiledBankRightMacro A)
    (ownerControl : (profiledBankRightController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankRightMonitor A source).State)
    (move : In₂ × In₁) (target : ProfiledBankLeftMacro A)
    (hstage : (stepProfiledBankRightReceiverFor A source ownerControl row
      monitorState move).2.2 = some target) :
    (stepProfiledBankRightReceiverFor A source ownerControl row monitorState
      move).2.1.2.2.1 row = some target.2.1.2 := by
  classical
  let controller := profiledBankRightController A source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledBankRightMonitor A source).step monitorState
    (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1))
        (output.target row)
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
                stepProfiledBankRightReceiverFor A source ownerControl row
                    monitorState move =
                  (output, nextMonitor,
                    some (profiledBankLeftMacroOfRightCertificate A source
                      (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledBankRightReceiverFor, controller, label,
                output, physical, nextMonitor, hsafe]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.2.1.2 = leftLive.2 := by
              rw [← hstage]
              exact profiledBankLeftMacroOfRightCertificate_profile_of_eq A
                source (output.target row) leftLive monitorState.2.1 row
                  physical htarget hsafe.1 hsafe.2
            change leftProfileOfProfiledState A (output.target row) =
              some target.2.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
  · have hstep :
        stepProfiledBankRightReceiverFor A source ownerControl row
            monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledBankRightReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-- Left-to-right mirror of
`stepProfiledBankRightReceiverFor_pending_of_staged`. -/
theorem stepProfiledBankLeftReceiverFor_pending_of_staged
    (source : ProfiledBankLeftMacro A)
    (ownerControl : (profiledBankLeftController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankLeftMonitor A source).State)
    (move : In₁ × In₂) (target : ProfiledBankRightMacro A)
    (hstage : (stepProfiledBankLeftReceiverFor A source ownerControl row
      monitorState move).2.2 = some target) :
    (stepProfiledBankLeftReceiverFor A source ownerControl row monitorState
      move).2.1.2.2.1 row = some target.2.1.2 := by
  classical
  let controller := profiledBankLeftController A source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledBankLeftMonitor A source).step monitorState
    (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1))
        (output.target row)
  · cases htarget : output.target row with
    | inl trivial =>
        rw [htarget] at hsafe
        cases row <;>
          simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
    | inr live =>
        cases live with
        | inl rightLive =>
            have hstep :
                stepProfiledBankLeftReceiverFor A source ownerControl row
                    monitorState move =
                  (output, nextMonitor,
                    some (profiledBankRightMacroOfLeftCertificate A source
                      (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledBankLeftReceiverFor, controller, label,
                output, physical, nextMonitor, hsafe]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.2.1.2 = rightLive.2 := by
              rw [← hstage]
              exact profiledBankRightMacroOfLeftCertificate_profile_of_eq A
                source (output.target row) rightLive monitorState.2.1 row
                  physical htarget hsafe.1 hsafe.2
            change rightProfileOfProfiledState A (output.target row) =
              some target.2.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
        | inr leftLive =>
            rw [htarget] at hsafe
            cases row <;>
              simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
  · have hstep :
        stepProfiledBankLeftReceiverFor A source ownerControl row
            monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledBankLeftReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-! ## Exact finite readback -/

abbrev ProfiledBankRightFiniteState (source : ProfiledBankRightMacro A) :=
  (profiledBankRightController A source).Control ×
    (profiledBankRightMonitor A source).State

abbrev ProfiledBankLeftFiniteState (source : ProfiledBankLeftMacro A) :=
  (profiledBankLeftController A source).Control ×
    (profiledBankLeftMonitor A source).State

noncomputable def initialProfiledBankRightFiniteState
    (source : ProfiledBankRightMacro A) : ProfiledBankRightFiniteState A source :=
  ((profiledBankRightController A source).initial,
    (profiledBankRightMonitor A source).initial)

noncomputable def initialProfiledBankLeftFiniteState
    (source : ProfiledBankLeftMacro A) : ProfiledBankLeftFiniteState A source :=
  ((profiledBankLeftController A source).initial,
    (profiledBankLeftMonitor A source).initial)

noncomputable def stepProfiledBankRightFiniteState
    (source : ProfiledBankRightMacro A)
    (state : ProfiledBankRightFiniteState A source) (move : In₂ × In₁) :
    ProfiledBankRightFiniteState A source :=
  let controller := profiledBankRightController A source
  let monitor := profiledBankRightMonitor A source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def stepProfiledBankLeftFiniteState
    (source : ProfiledBankLeftMacro A)
    (state : ProfiledBankLeftFiniteState A source) (move : In₁ × In₂) :
    ProfiledBankLeftFiniteState A source :=
  let controller := profiledBankLeftController A source
  let monitor := profiledBankLeftMonitor A source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledBankRightFiniteStateAfter
    (source : ProfiledBankRightMacro A) (past : List (In₂ × In₁)) :
    ProfiledBankRightFiniteState A source :=
  past.foldl (stepProfiledBankRightFiniteState A source)
    (initialProfiledBankRightFiniteState A source)

noncomputable def profiledBankLeftFiniteStateAfter
    (source : ProfiledBankLeftMacro A) (past : List (In₁ × In₂)) :
    ProfiledBankLeftFiniteState A source :=
  past.foldl (stepProfiledBankLeftFiniteState A source)
    (initialProfiledBankLeftFiniteState A source)

theorem profiledBankRightFiniteStateAfter_eq
    (source : ProfiledBankRightMacro A) : ∀ past : List (In₂ × In₁),
    profiledBankRightFiniteStateAfter A source past =
      ((profiledBankRightController A source).controlAt (senderWord past),
        narrowedControl (profiledBankRightMonitor A source)
          (profiledBankRightController A source).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledBankRightFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledBankRightFiniteState A source
        (profiledBankRightFiniteStateAfter A source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

theorem profiledBankLeftFiniteStateAfter_eq
    (source : ProfiledBankLeftMacro A) : ∀ past : List (In₁ × In₂),
    profiledBankLeftFiniteStateAfter A source past =
      ((profiledBankLeftController A source).controlAt (senderWord past),
        narrowedControl (profiledBankLeftMonitor A source)
          (profiledBankLeftController A source).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledBankLeftFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledBankLeftFiniteState A source
        (profiledBankLeftFiniteStateAfter A source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

/-! ## Certificate staging along every real controller prefix -/

private theorem profiledBankRight_treePlay_at_prefix
    (source : ProfiledBankRightMacro A) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    let monitor := profiledBankRightMonitor A source
    let controller := profiledBankRightController A source
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
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hmove, senderWord, env, finiteWord]

private theorem profiledBankLeft_treePlay_at_prefix
    (source : ProfiledBankLeftMacro A) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    let monitor := profiledBankLeftMonitor A source
    let controller := profiledBankLeftController A source
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
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hmove, senderWord, env, finiteWord]

/-- Every actual recurrent right-controller round produces a checked and
therefore staged left key, for either locally stored entry row. -/
theorem profiledBankRight_real_close_staged
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (stepProfiledBankRightReceiverFor A source
      (profiledBankRightFiniteStateAfter A source past).1 row
      (profiledBankRightFiniteStateAfter A source past).2 move).2.2.isSome := by
  rw [profiledBankRightFiniteStateAfter_eq A source]
  let monitor := profiledBankRightMonitor A source
  let controller := profiledBankRightController A source
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledBankRightController_wins A source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledRight_targetsSafe_of_wins A
    (feasibleProfiledPolicy A source.1) source.2.1.1.1
    source.2.1.1.2 source.2.1.2 (treePlay tree env) hwin past.length row
  have hat := profiledBankRight_treePlay_at_prefix A source past move
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
  exact stepProfiledBankRightReceiverFor_staged_of_safe A source
    (controller.controlAt (senderWord past)) row
    (narrowedControl monitor controller.labeledTree past) move hsafe

/-- Left mirror. -/
theorem profiledBankLeft_real_close_staged
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (stepProfiledBankLeftReceiverFor A source
      (profiledBankLeftFiniteStateAfter A source past).1 row
      (profiledBankLeftFiniteStateAfter A source past).2 move).2.2.isSome := by
  rw [profiledBankLeftFiniteStateAfter_eq A source]
  let monitor := profiledBankLeftMonitor A source
  let controller := profiledBankLeftController A source
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledBankLeftController_wins A source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledLeft_targetsSafe_of_wins A
    (feasibleProfiledPolicy A source.1) source.2.1.1.1
    source.2.1.1.2 source.2.1.2 (treePlay tree env) hwin past.length row
  have hat := profiledBankLeft_treePlay_at_prefix A source past move
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
  exact stepProfiledBankLeftReceiverFor_staged_of_safe A source
    (controller.controlAt (senderWord past)) row
    (narrowedControl monitor controller.labeledTree past) move hsafe

/-! ## Delayed overlap along real finite-controller prefixes -/

/-- A pending left initial profile stored by a real right-bank prefix is
honored by the old right receiver on the following physical round. -/
theorem profiledBankRight_real_overlap
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      (profiledBankRightFiniteStateAfter A source past).2.2.2.1 row =
        some expected) :
    pairedRightClosingForRow row
        (((profiledBankRightController A source).labelOf
          (profiledBankRightFiniteStateAfter A source past).1).2
          (profiledBankRightFiniteStateAfter A source past).2 move).physical =
      expected (move.2, move.1) := by
  rw [profiledBankRightFiniteStateAfter_eq A source] at hpending ⊢
  let monitor := profiledBankRightMonitor A source
  let controller := profiledBankRightController A source
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledBankRightController_wins A source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := profiledRight_overlap_of_wins A
    (feasibleProfiledPolicy A source.1) source.2.1.1.1
    source.2.1.1.2 source.2.1.2 (treePlay tree env) hwin past.length row
    expected
  have hat := profiledBankRight_treePlay_at_prefix A source past move
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

/-- Left-to-right mirror of `profiledBankRight_real_overlap`. -/
theorem profiledBankLeft_real_overlap
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      (profiledBankLeftFiniteStateAfter A source past).2.2.2.1 row =
        some expected) :
    pairedLeftClosingForRow row
        (((profiledBankLeftController A source).labelOf
          (profiledBankLeftFiniteStateAfter A source past).1).2
          (profiledBankLeftFiniteStateAfter A source past).2 move).physical =
      expected (move.2, move.1) := by
  rw [profiledBankLeftFiniteStateAfter_eq A source] at hpending ⊢
  let monitor := profiledBankLeftMonitor A source
  let controller := profiledBankLeftController A source
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledBankLeftController_wins A source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := profiledLeft_overlap_of_wins A
    (feasibleProfiledPolicy A source.1) source.2.1.1.1
    source.2.1.1.2 source.2.1.2 (treePlay tree env) hwin past.length row
    expected
  have hat := profiledBankLeft_treePlay_at_prefix A source past move
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

/-! ## Stored profiles at recurrent roots -/

/-- The selected right-bank controller realizes the right initial profile
stored in its source on its first physical round. -/
theorem profiledBankRight_root_profile
    (source : ProfiledBankRightMacro A) (move : In₂ × In₁) :
    pairedRightInformedForRow .first
        (((profiledBankRightController A source).labelOf
          (profiledBankRightController A source).initial).2
          (profiledBankRightMonitor A source).initial move).physical =
      source.2.1.2 move := by
  let monitor := profiledBankRightMonitor A source
  let controller := profiledBankRightController A source
  let env : Nat → In₂ × In₁ := fun _ => move
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledBankRightController_wins A source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hroot := profiledRight_rootProfile_of_wins A
    (feasibleProfiledPolicy A source.1) source.2.1.1.1
    source.2.1.1.2 source.2.1.2 (treePlay tree env) hwin
  simpa [treePlay, tree, env, narrowedInducedTree, blockLabelApply,
    narrowedRecord, TransitionRationalTree.labeledTree, narrowedControl,
    narrowedControlAux, controller, monitor] using hroot

/-- Left mirror of `profiledBankRight_root_profile`. -/
theorem profiledBankLeft_root_profile
    (source : ProfiledBankLeftMacro A) (move : In₁ × In₂) :
    pairedLeftInformedForRow .first
        (((profiledBankLeftController A source).labelOf
          (profiledBankLeftController A source).initial).2
          (profiledBankLeftMonitor A source).initial move).physical =
      source.2.1.2 move := by
  let monitor := profiledBankLeftMonitor A source
  let controller := profiledBankLeftController A source
  let env : Nat → In₁ × In₂ := fun _ => move
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledBankLeftController_wins A source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hroot := profiledLeft_rootProfile_of_wins A
    (feasibleProfiledPolicy A source.1) source.2.1.1.1
    source.2.1.1.2 source.2.1.2 (treePlay tree env) hwin
  simpa [treePlay, tree, env, narrowedInducedTree, blockLabelApply,
    narrowedRecord, TransitionRationalTree.labeledTree, narrowedControl,
    narrowedControlAux, controller, monitor] using hroot

end

end


end DetParityAutomaton

end DistributedSynthesis
