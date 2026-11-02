/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledPolicyBank

/-!
# Finite local handoff under one fixed profiled policy

This is the policy-parametric operational core of the recurrent local
handoff.  The owner stores a finite controller state.  The receiver stores
the finite macro, its local row, the finite monitor state, and an optional
opposite-orientation macro.  A successor is staged only after checking the
physical close and the fixed policy's `Allowed` relation.
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
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-! ## Finite local controls -/

abbrev ProfiledPolicyRightOwnerControl :=
  Σ source : ProfiledPolicyRightMacro A policy,
    (profiledPolicyRightController A policy source).Control

abbrev ProfiledPolicyLeftOwnerControl :=
  Σ source : ProfiledPolicyLeftMacro A policy,
    (profiledPolicyLeftController A policy source).Control

abbrev ProfiledPolicyRightReceiverControl :=
  Σ source : ProfiledPolicyRightMacro A policy,
    PairedEntryRow × (profiledPolicyRightMonitor A policy source).State ×
      Option (ProfiledPolicyLeftMacro A policy)

abbrev ProfiledPolicyLeftReceiverControl :=
  Σ source : ProfiledPolicyLeftMacro A policy,
    PairedEntryRow × (profiledPolicyLeftMonitor A policy source).State ×
      Option (ProfiledPolicyRightMacro A policy)

noncomputable instance : Fintype (ProfiledPolicyRightOwnerControl A policy) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledPolicyLeftOwnerControl A policy) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledPolicyRightReceiverControl A policy) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledPolicyLeftReceiverControl A policy) := by
  classical
  infer_instance

noncomputable def initialProfiledPolicyRightOwner
    (source : ProfiledPolicyRightMacro A policy) :
    ProfiledPolicyRightOwnerControl A policy :=
  ⟨source, (profiledPolicyRightController A policy source).initial⟩

noncomputable def initialProfiledPolicyLeftOwner
    (source : ProfiledPolicyLeftMacro A policy) :
    ProfiledPolicyLeftOwnerControl A policy :=
  ⟨source, (profiledPolicyLeftController A policy source).initial⟩

noncomputable def initialProfiledPolicyRightReceiver
    (source : ProfiledPolicyRightMacro A policy) (row : PairedEntryRow) :
    ProfiledPolicyRightReceiverControl A policy :=
  ⟨source, row, (profiledPolicyRightMonitor A policy source).initial, none⟩

noncomputable def initialProfiledPolicyLeftReceiver
    (source : ProfiledPolicyLeftMacro A policy) (row : PairedEntryRow) :
    ProfiledPolicyLeftReceiverControl A policy :=
  ⟨source, row, (profiledPolicyLeftMonitor A policy source).initial, none⟩

noncomputable def stepProfiledPolicyRightOwner
    (owner : ProfiledPolicyRightOwnerControl A policy) (input : In₁) :
    Out₁ × ProfiledPolicyRightOwnerControl A policy :=
  let controller := profiledPolicyRightController A policy owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepProfiledPolicyLeftOwner
    (owner : ProfiledPolicyLeftOwnerControl A policy) (input : In₂) :
    Out₂ × ProfiledPolicyLeftOwnerControl A policy :=
  let controller := profiledPolicyLeftController A policy owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem stepProfiledPolicyRightOwner_source
    (owner : ProfiledPolicyRightOwnerControl A policy) (input : In₁) :
    (stepProfiledPolicyRightOwner A policy owner input).2.1 = owner.1 := rfl

@[simp] theorem stepProfiledPolicyLeftOwner_source
    (owner : ProfiledPolicyLeftOwnerControl A policy) (input : In₂) :
    (stepProfiledPolicyLeftOwner A policy owner input).2.1 = owner.1 := rfl

/-! ## Receiver computation and certified staging -/

abbrev ProfiledPolicyRightReceiverRoundResult
    (source : ProfiledPolicyRightMacro A policy) :=
  ProfiledRightReceiverOutput A ×
    (profiledPolicyRightMonitor A policy source).State ×
      Option (ProfiledPolicyLeftMacro A policy)

abbrev ProfiledPolicyLeftReceiverRoundResult
    (source : ProfiledPolicyLeftMacro A policy) :=
  ProfiledLeftReceiverOutput A ×
    (profiledPolicyLeftMonitor A policy source).State ×
      Option (ProfiledPolicyRightMacro A policy)

noncomputable def stepProfiledPolicyRightReceiverFor
    (source : ProfiledPolicyRightMacro A policy)
    (ownerControl : (profiledPolicyRightController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyRightMonitor A policy source).State)
    (move : In₂ × In₁) :
    ProfiledPolicyRightReceiverRoundResult A policy source := by
  classical
  let controller := profiledPolicyRightController A policy source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledPolicyRightMonitor A policy source).step
    monitorState (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inl source.1)) (output.target row) then
    exact (output, nextMonitor,
      some (profiledPolicyLeftMacroOfRightCertificate A policy source
        (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

noncomputable def stepProfiledPolicyLeftReceiverFor
    (source : ProfiledPolicyLeftMacro A policy)
    (ownerControl : (profiledPolicyLeftController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyLeftMonitor A policy source).State)
    (move : In₁ × In₂) :
    ProfiledPolicyLeftReceiverRoundResult A policy source := by
  classical
  let controller := profiledPolicyLeftController A policy source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledPolicyLeftMonitor A policy source).step
    monitorState (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inr source.1)) (output.target row) then
    exact (output, nextMonitor,
      some (profiledPolicyRightMacroOfLeftCertificate A policy source
        (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2))
  else
    exact (output, nextMonitor, none)

@[simp] theorem stepProfiledPolicyRightReceiverFor_output
    (source : ProfiledPolicyRightMacro A policy)
    (ownerControl : (profiledPolicyRightController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyRightMonitor A policy source).State)
    (move : In₂ × In₁) :
    (stepProfiledPolicyRightReceiverFor A policy source ownerControl row
      monitorState move).1 =
      ((profiledPolicyRightController A policy source).labelOf ownerControl).2
        monitorState move := by
  classical
  simp only [stepProfiledPolicyRightReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledPolicyRightReceiverFor_monitor
    (source : ProfiledPolicyRightMacro A policy)
    (ownerControl : (profiledPolicyRightController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyRightMonitor A policy source).State)
    (move : In₂ × In₁) :
    (stepProfiledPolicyRightReceiverFor A policy source ownerControl row
      monitorState move).2.1 =
      (profiledPolicyRightMonitor A policy source).step monitorState
        (narrowedRecord (profiledPolicyRightMonitor A policy source)
          ((profiledPolicyRightController A policy source).labelOf ownerControl)
          monitorState move) := by
  classical
  simp only [stepProfiledPolicyRightReceiverFor, narrowedRecord]
  split <;> rfl

@[simp] theorem stepProfiledPolicyLeftReceiverFor_output
    (source : ProfiledPolicyLeftMacro A policy)
    (ownerControl : (profiledPolicyLeftController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyLeftMonitor A policy source).State)
    (move : In₁ × In₂) :
    (stepProfiledPolicyLeftReceiverFor A policy source ownerControl row
      monitorState move).1 =
      ((profiledPolicyLeftController A policy source).labelOf ownerControl).2
        monitorState move := by
  classical
  simp only [stepProfiledPolicyLeftReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledPolicyLeftReceiverFor_monitor
    (source : ProfiledPolicyLeftMacro A policy)
    (ownerControl : (profiledPolicyLeftController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyLeftMonitor A policy source).State)
    (move : In₁ × In₂) :
    (stepProfiledPolicyLeftReceiverFor A policy source ownerControl row
      monitorState move).2.1 =
      (profiledPolicyLeftMonitor A policy source).step monitorState
        (narrowedRecord (profiledPolicyLeftMonitor A policy source)
          ((profiledPolicyLeftController A policy source).labelOf ownerControl)
          monitorState move) := by
  classical
  simp only [stepProfiledPolicyLeftReceiverFor, narrowedRecord]
  split <;> rfl

theorem stepProfiledPolicyRightReceiverFor_staged_of_safe
    (source : ProfiledPolicyRightMacro A policy)
    (ownerControl : (profiledPolicyRightController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyRightMonitor A policy source).State)
    (move : In₂ × In₁)
    (hsafe : erasePairedProfiledState A
          (((profiledPolicyRightController A policy source).labelOf
            ownerControl).2 monitorState move |>.target row) =
        pairedRightCloseTarget A monitorState.2.1 row
          (profiledRightPhysicalLetter A
            (move,
              ((profiledPolicyRightController A policy source).labelOf
                ownerControl).2 monitorState move,
              ((profiledPolicyRightController A policy source).labelOf
                ownerControl).1 move.2)) ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inl source.1))
        (((profiledPolicyRightController A policy source).labelOf
          ownerControl).2 monitorState move |>.target row)) :
    (stepProfiledPolicyRightReceiverFor A policy source ownerControl row
      monitorState move).2.2.isSome := by
  classical
  simp [stepProfiledPolicyRightReceiverFor, hsafe]

theorem stepProfiledPolicyLeftReceiverFor_staged_of_safe
    (source : ProfiledPolicyLeftMacro A policy)
    (ownerControl : (profiledPolicyLeftController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyLeftMonitor A policy source).State)
    (move : In₁ × In₂)
    (hsafe : erasePairedProfiledState A
          (((profiledPolicyLeftController A policy source).labelOf
            ownerControl).2 monitorState move |>.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row
          (profiledLeftPhysicalLetter A
            (move,
              ((profiledPolicyLeftController A policy source).labelOf
                ownerControl).2 monitorState move,
              ((profiledPolicyLeftController A policy source).labelOf
                ownerControl).1 move.2)) ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inr source.1))
        (((profiledPolicyLeftController A policy source).labelOf
          ownerControl).2 monitorState move |>.target row)) :
    (stepProfiledPolicyLeftReceiverFor A policy source ownerControl row
      monitorState move).2.2.isSome := by
  classical
  simp [stepProfiledPolicyLeftReceiverFor, hsafe]

/-! ## Recovering the fixed-policy edge from a staged target -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Re-embedding a left macro built from a checked right certificate recovers
the certificate's exact profiled target state. -/
theorem profiledPolicyLeftMacroOfRightCertificate_state
    (source : ProfiledPolicyRightMacro A policy)
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inl source.1)) target) :
    (.inr (.inr
      (profiledPolicyLeftMacroOfRightCertificate A policy source target scan
        row letter herase hallowed).1) : PairedProfiledTreeState A) = target := by
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Left-to-right mirror of
`profiledPolicyLeftMacroOfRightCertificate_state`. -/
theorem profiledPolicyRightMacroOfLeftCertificate_state
    (source : ProfiledPolicyLeftMacro A policy)
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inr source.1)) target) :
    (.inr (.inl
      (profiledPolicyRightMacroOfLeftCertificate A policy source target scan
        row letter herase hallowed).1) : PairedProfiledTreeState A) = target := by
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rfl
      | inr leftLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

/-- If the recurrent right receiver stages a concrete left macro, that macro
is the target of an `Allowed` edge of the same fixed policy.  Unlike mere
reachability, this is the adjacency fact consumed by epoch parity. -/
theorem stepProfiledPolicyRightReceiverFor_allowed_of_staged
    (source : ProfiledPolicyRightMacro A policy)
    (ownerControl : (profiledPolicyRightController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyRightMonitor A policy source).State)
    (move : In₂ × In₁) (target : ProfiledPolicyLeftMacro A policy)
    (hstage : (stepProfiledPolicyRightReceiverFor A policy source ownerControl
      row monitorState move).2.2 = some target) :
    PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inl source.1)) (.inr (.inr target.1)) := by
  classical
  let controller := profiledPolicyRightController A policy source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledPolicyRightMonitor A policy source).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inl source.1)) (output.target row)
  · have hstep :
        stepProfiledPolicyRightReceiverFor A policy source ownerControl row
            monitorState move =
          (output, nextMonitor,
            some (profiledPolicyLeftMacroOfRightCertificate A policy source
              (output.target row) monitorState.2.1 row physical hsafe.1
                hsafe.2)) := by
      simp [stepProfiledPolicyRightReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp only [Option.some.injEq] at hstage
    rw [← hstage]
    rw [profiledPolicyLeftMacroOfRightCertificate_state A policy source
      (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2]
    exact hsafe.2
  · have hstep :
        stepProfiledPolicyRightReceiverFor A policy source ownerControl row
            monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledPolicyRightReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-- A staged recurrent right macro is likewise the exact target of an
`Allowed` edge of the unchanged fixed policy. -/
theorem stepProfiledPolicyLeftReceiverFor_allowed_of_staged
    (source : ProfiledPolicyLeftMacro A policy)
    (ownerControl : (profiledPolicyLeftController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyLeftMonitor A policy source).State)
    (move : In₁ × In₂) (target : ProfiledPolicyRightMacro A policy)
    (hstage : (stepProfiledPolicyLeftReceiverFor A policy source ownerControl
      row monitorState move).2.2 = some target) :
    PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inr source.1)) (.inr (.inl target.1)) := by
  classical
  let controller := profiledPolicyLeftController A policy source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledPolicyLeftMonitor A policy source).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inr source.1)) (output.target row)
  · have hstep :
        stepProfiledPolicyLeftReceiverFor A policy source ownerControl row
            monitorState move =
          (output, nextMonitor,
            some (profiledPolicyRightMacroOfLeftCertificate A policy source
              (output.target row) monitorState.2.1 row physical hsafe.1
                hsafe.2)) := by
      simp [stepProfiledPolicyLeftReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp only [Option.some.injEq] at hstage
    rw [← hstage]
    rw [profiledPolicyRightMacroOfLeftCertificate_state A policy source
      (output.target row) monitorState.2.1 row physical hsafe.1 hsafe.2]
    exact hsafe.2
  · have hstep :
        stepProfiledPolicyLeftReceiverFor A policy source ownerControl row
            monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledPolicyLeftReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledPolicyLeftMacroOfRightCertificate_profile_of_eq
    (source : ProfiledPolicyRightMacro A policy)
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
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inl source.1)) target) :
    (profiledPolicyLeftMacroOfRightCertificate A policy source target scan row
      letter herase hallowed).1.2 = live.2 := by
  subst target
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledPolicyRightMacroOfLeftCertificate_profile_of_eq
    (source : ProfiledPolicyLeftMacro A policy)
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
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inr source.1)) target) :
    (profiledPolicyRightMacroOfLeftCertificate A policy source target scan row
      letter herase hallowed).1.2 = live.2 := by
  subst target
  rfl

/-- A staged left macro carries exactly the profile installed in the next
right-monitor pending slot. -/
theorem stepProfiledPolicyRightReceiverFor_pending_of_staged
    (source : ProfiledPolicyRightMacro A policy)
    (ownerControl : (profiledPolicyRightController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyRightMonitor A policy source).State)
    (move : In₂ × In₁) (target : ProfiledPolicyLeftMacro A policy)
    (hstage : (stepProfiledPolicyRightReceiverFor A policy source ownerControl
      row monitorState move).2.2 = some target) :
    (stepProfiledPolicyRightReceiverFor A policy source ownerControl row
      monitorState move).2.1.2.2.1 row = some target.1.2 := by
  classical
  let controller := profiledPolicyRightController A policy source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledPolicyRightMonitor A policy source).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inl source.1)) (output.target row)
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
                stepProfiledPolicyRightReceiverFor A policy source
                    ownerControl row monitorState move =
                  (output, nextMonitor,
                    some (profiledPolicyLeftMacroOfRightCertificate A policy
                      source (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledPolicyRightReceiverFor, controller, label,
                output, physical, nextMonitor, hsafe]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.1.2 = leftLive.2 := by
              rw [← hstage]
              exact profiledPolicyLeftMacroOfRightCertificate_profile_of_eq
                A policy source (output.target row) leftLive monitorState.2.1
                  row physical htarget hsafe.1 hsafe.2
            change leftProfileOfProfiledState A (output.target row) =
              some target.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
  · have hstep :
        stepProfiledPolicyRightReceiverFor A policy source ownerControl row
            monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledPolicyRightReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-- Left-to-right mirror of
`stepProfiledPolicyRightReceiverFor_pending_of_staged`. -/
theorem stepProfiledPolicyLeftReceiverFor_pending_of_staged
    (source : ProfiledPolicyLeftMacro A policy)
    (ownerControl : (profiledPolicyLeftController A policy source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledPolicyLeftMonitor A policy source).State)
    (move : In₁ × In₂) (target : ProfiledPolicyRightMacro A policy)
    (hstage : (stepProfiledPolicyLeftReceiverFor A policy source ownerControl
      row monitorState move).2.2 = some target) :
    (stepProfiledPolicyLeftReceiverFor A policy source ownerControl row
      monitorState move).2.1.2.2.1 row = some target.1.2 := by
  classical
  let controller := profiledPolicyLeftController A policy source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (profiledPolicyLeftMonitor A policy source).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inr source.1)) (output.target row)
  · cases htarget : output.target row with
    | inl trivial =>
        rw [htarget] at hsafe
        cases row <;>
          simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
    | inr live =>
        cases live with
        | inl rightLive =>
            have hstep :
                stepProfiledPolicyLeftReceiverFor A policy source ownerControl
                    row monitorState move =
                  (output, nextMonitor,
                    some (profiledPolicyRightMacroOfLeftCertificate A policy
                      source (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledPolicyLeftReceiverFor, controller, label,
                output, physical, nextMonitor, hsafe]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.1.2 = rightLive.2 := by
              rw [← hstage]
              exact profiledPolicyRightMacroOfLeftCertificate_profile_of_eq
                A policy source (output.target row) rightLive monitorState.2.1
                  row physical htarget hsafe.1 hsafe.2
            change rightProfileOfProfiledState A (output.target row) =
              some target.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
        | inr leftLive =>
            rw [htarget] at hsafe
            cases row <;>
              simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
  · have hstep :
        stepProfiledPolicyLeftReceiverFor A policy source ownerControl row
            monitorState move = (output, nextMonitor, none) := by
      simp [stepProfiledPolicyLeftReceiverFor, controller, label, output,
        physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

end


end DetParityAutomaton

end DistributedSynthesis
