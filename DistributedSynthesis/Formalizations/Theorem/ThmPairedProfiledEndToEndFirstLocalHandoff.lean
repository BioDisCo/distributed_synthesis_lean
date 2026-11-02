/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndControllerBank

/-!
# Operational first-block handoff for the one-policy bank

The finite boundary bank is turned into local transition functions.  The
receiver checks the physical close and membership in its key's supplied
guarded policy, then stages the already-typed recurrent macro.  Thus the
strict reversal itself merely consumes a finite local value.
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

/-! ## First-right block -/

noncomputable abbrev endToEndFirstRightMonitor
    (key : EndToEndInitialLeftBoundaryKey A package) :=
  endToEndGuardedFirstRightBlockMonitor A key.1.2.2.2
    (endToEndInitialLeftBoundaryActivation A package key).profile
    (endToEndInitialLeftBoundaryActivation A package key).policy
    (endToEndInitialLeftBoundaryShape A package key).code
    (endToEndInitialLeftBoundaryShape A package key).minimum
    (endToEndInitialLeftBoundaryShape A package key).profile

abbrev EndToEndFirstRightRoundResult
    (key : EndToEndInitialLeftBoundaryKey A package) :=
  ProfiledRightReceiverOutput A ×
    (endToEndFirstRightMonitor A package key).State ×
      Option (EndToEndGuardedRightRecurrentLeftMacro A
        (rightGuarded :=
          (endToEndInitialLeftBoundaryActivation A package key).policy))

noncomputable def initialEndToEndGuardedFirstRightOwner
    (key : EndToEndInitialLeftBoundaryKey A package) :
    EndToEndGuardedFirstRightOwnerControl A package :=
  ⟨key, (endToEndInitialLeftBoundaryController A package key).initial⟩

noncomputable def initialEndToEndGuardedFirstRightReceiver
    (key : EndToEndInitialLeftBoundaryKey A package) (row : PairedEntryRow) :
    EndToEndGuardedFirstRightReceiverControl A package :=
  ⟨key, row, (endToEndFirstRightMonitor A package key).initial, none⟩

noncomputable def stepEndToEndGuardedFirstRightOwner
    (owner : EndToEndGuardedFirstRightOwnerControl A package) (input : In₁) :
    Out₁ × EndToEndGuardedFirstRightOwnerControl A package :=
  let controller := endToEndInitialLeftBoundaryController A package owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem stepEndToEndGuardedFirstRightOwner_key
    (owner : EndToEndGuardedFirstRightOwnerControl A package) (input : In₁) :
    (stepEndToEndGuardedFirstRightOwner A package owner input).2.1 = owner.1 :=
  rfl

noncomputable def stepEndToEndGuardedFirstRightReceiverFor
    (key : EndToEndInitialLeftBoundaryKey A package)
    (ownerControl : (endToEndInitialLeftBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstRightMonitor A package key).State)
    (move : In₂ × In₁) : EndToEndFirstRightRoundResult A package key := by
  classical
  let activation := endToEndInitialLeftBoundaryActivation A package key
  let controller := endToEndInitialLeftBoundaryController A package key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (endToEndFirstRightMonitor A package key).step monitorState
    (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      ProfiledGuardedRightPolicyAllows A key.1.2.2.2 activation.profile
        activation.policy (output.target row) then
    let child : EndToEndGuardedRightChild A key.1.2.2.2 activation.profile
        activation.policy := ⟨output.target row, hsafe.2⟩
    exact (output, nextMonitor,
      some (child.recurrentLeftMacroOfClose A monitorState.2.1 row physical
        hsafe.1))
  else
    exact (output, nextMonitor, none)

noncomputable def endToEndGuardedFirstRightOwnerControlFor
    (receiver : EndToEndGuardedFirstRightReceiverControl A package)
    (owner : EndToEndGuardedFirstRightOwnerControl A package) :
    (endToEndInitialLeftBoundaryController A package receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (endToEndInitialLeftBoundaryController A package receiver.1).initial

noncomputable def continueEndToEndGuardedFirstRightReceiver
    (receiver : EndToEndGuardedFirstRightReceiverControl A package)
    (owner : EndToEndGuardedFirstRightOwnerControl A package)
    (move : In₂ × In₁) :
    Out₂ × EndToEndGuardedFirstRightReceiverControl A package :=
  let result := stepEndToEndGuardedFirstRightReceiverFor A package receiver.1
    (endToEndGuardedFirstRightOwnerControlFor A package receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

@[simp] theorem continueEndToEndGuardedFirstRightReceiver_key
    (receiver : EndToEndGuardedFirstRightReceiverControl A package)
    (owner : EndToEndGuardedFirstRightOwnerControl A package)
    (move : In₂ × In₁) :
    (continueEndToEndGuardedFirstRightReceiver A package receiver owner
      move).2.1 = receiver.1 := rfl

@[simp] theorem stepEndToEndGuardedFirstRightReceiverFor_output
    (key : EndToEndInitialLeftBoundaryKey A package)
    (ownerControl : (endToEndInitialLeftBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstRightMonitor A package key).State)
    (move : In₂ × In₁) :
    (stepEndToEndGuardedFirstRightReceiverFor A package key ownerControl row
      monitorState move).1 =
      ((endToEndInitialLeftBoundaryController A package key).labelOf
        ownerControl).2 monitorState move := by
  classical
  simp only [stepEndToEndGuardedFirstRightReceiverFor]
  split <;> rfl

@[simp] theorem stepEndToEndGuardedFirstRightReceiverFor_monitor
    (key : EndToEndInitialLeftBoundaryKey A package)
    (ownerControl : (endToEndInitialLeftBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstRightMonitor A package key).State)
    (move : In₂ × In₁) :
    (stepEndToEndGuardedFirstRightReceiverFor A package key ownerControl row
      monitorState move).2.1 =
      (endToEndFirstRightMonitor A package key).step monitorState
        (narrowedRecord (endToEndFirstRightMonitor A package key)
          ((endToEndInitialLeftBoundaryController A package key).labelOf
            ownerControl) monitorState move) := by
  classical
  simp only [stepEndToEndGuardedFirstRightReceiverFor, narrowedRecord]
  split <;> rfl

/-- A successful exceptional right close installs exactly the profile stored
in the monitor's pending slot. -/
theorem stepEndToEndGuardedFirstRightReceiverFor_pending_of_staged
    (key : EndToEndInitialLeftBoundaryKey A package)
    (ownerControl : (endToEndInitialLeftBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstRightMonitor A package key).State)
    (move : In₂ × In₁)
    (target : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy))
    (hstage : (stepEndToEndGuardedFirstRightReceiverFor A package key
      ownerControl row monitorState move).2.2 = some target) :
    (stepEndToEndGuardedFirstRightReceiverFor A package key ownerControl row
      monitorState move).2.1.2.2.1 row = some target.2.1.2 := by
  classical
  let activation := endToEndInitialLeftBoundaryActivation A package key
  let controller := endToEndInitialLeftBoundaryController A package key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (endToEndFirstRightMonitor A package key).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      ProfiledGuardedRightPolicyAllows A key.1.2.2.2 activation.profile
        activation.policy (output.target row)
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
            let child : EndToEndGuardedRightChild A key.1.2.2.2
                activation.profile activation.policy :=
              ⟨output.target row, hsafe.2⟩
            have hstep :
                stepEndToEndGuardedFirstRightReceiverFor A package key
                    ownerControl row monitorState move =
                  (output, nextMonitor,
                    some (child.recurrentLeftMacroOfClose A monitorState.2.1
                      row physical hsafe.1)) := by
              simp [stepEndToEndGuardedFirstRightReceiverFor, activation,
                controller, label, output, physical, nextMonitor, hsafe,
                child]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.2.1.2 = leftLive.2 := by
              rw [← hstage]
              exact child.recurrentLeftMacroOfClose_profile_of_eq A leftLive
                monitorState.2.1 row physical htarget hsafe.1
            change leftProfileOfProfiledState A (output.target row) =
              some target.2.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
  · have hstep :
        stepEndToEndGuardedFirstRightReceiverFor A package key ownerControl
            row monitorState move = (output, nextMonitor, none) := by
      simp [stepEndToEndGuardedFirstRightReceiverFor, activation, controller,
        label, output, physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-- A successful exceptional right close starts the recurrent child policy at
exactly the staged left-oriented macro.  This is the parity seam: the finite
exceptional prefix is discarded, and the ordinary fixed-policy thread starts
at its policy root. -/
theorem stepEndToEndGuardedFirstRightReceiverFor_initial_of_staged
    (key : EndToEndInitialLeftBoundaryKey A package)
    (ownerControl : (endToEndInitialLeftBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstRightMonitor A package key).State)
    (move : In₂ × In₁)
    (target : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy))
    (hstage : (stepEndToEndGuardedFirstRightReceiverFor A package key
      ownerControl row monitorState move).2.2 = some target) :
    (.inr (.inr target.2.1) : PairedProfiledTreeState A) =
      (target.1.policy A).run [] := by
  classical
  let activation := endToEndInitialLeftBoundaryActivation A package key
  let controller := endToEndInitialLeftBoundaryController A package key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (endToEndFirstRightMonitor A package key).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedRightCloseTarget A monitorState.2.1 row physical ∧
      ProfiledGuardedRightPolicyAllows A key.1.2.2.2 activation.profile
        activation.policy (output.target row)
  · let child : EndToEndGuardedRightChild A key.1.2.2.2
        activation.profile activation.policy :=
      ⟨output.target row, hsafe.2⟩
    have hstep :
        stepEndToEndGuardedFirstRightReceiverFor A package key ownerControl
            row monitorState move =
          (output, nextMonitor,
            some (child.recurrentLeftMacroOfClose A monitorState.2.1 row
              physical hsafe.1)) := by
      simp [stepEndToEndGuardedFirstRightReceiverFor, activation, controller,
        label, output, physical, nextMonitor, hsafe, child]
    rw [hstep] at hstage
    simp only [Option.some.injEq] at hstage
    rw [← hstage]
    exact child.recurrentLeftMacroOfClose_initial A monitorState.2.1 row
      physical hsafe.1
  · have hstep :
        stepEndToEndGuardedFirstRightReceiverFor A package key ownerControl
            row monitorState move = (output, nextMonitor, none) := by
      simp [stepEndToEndGuardedFirstRightReceiverFor, activation, controller,
        label, output, physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-! ## First-left mirror -/

noncomputable abbrev endToEndFirstLeftMonitor
    (key : EndToEndInitialRightBoundaryKey A package) :=
  endToEndGuardedFirstLeftBlockMonitor A key.1.2.2.2
    (endToEndInitialRightBoundaryActivation A package key).profile
    (endToEndInitialRightBoundaryActivation A package key).policy
    (endToEndInitialRightBoundaryShape A package key).code
    (endToEndInitialRightBoundaryShape A package key).minimum
    (endToEndInitialRightBoundaryShape A package key).profile

abbrev EndToEndFirstLeftRoundResult
    (key : EndToEndInitialRightBoundaryKey A package) :=
  ProfiledLeftReceiverOutput A ×
    (endToEndFirstLeftMonitor A package key).State ×
      Option (EndToEndGuardedLeftRecurrentRightMacro A
        (leftGuarded :=
          (endToEndInitialRightBoundaryActivation A package key).policy))

noncomputable def initialEndToEndGuardedFirstLeftOwner
    (key : EndToEndInitialRightBoundaryKey A package) :
    EndToEndGuardedFirstLeftOwnerControl A package :=
  ⟨key, (endToEndInitialRightBoundaryController A package key).initial⟩

noncomputable def initialEndToEndGuardedFirstLeftReceiver
    (key : EndToEndInitialRightBoundaryKey A package) (row : PairedEntryRow) :
    EndToEndGuardedFirstLeftReceiverControl A package :=
  ⟨key, row, (endToEndFirstLeftMonitor A package key).initial, none⟩

noncomputable def stepEndToEndGuardedFirstLeftOwner
    (owner : EndToEndGuardedFirstLeftOwnerControl A package) (input : In₂) :
    Out₂ × EndToEndGuardedFirstLeftOwnerControl A package :=
  let controller := endToEndInitialRightBoundaryController A package owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem stepEndToEndGuardedFirstLeftOwner_key
    (owner : EndToEndGuardedFirstLeftOwnerControl A package) (input : In₂) :
    (stepEndToEndGuardedFirstLeftOwner A package owner input).2.1 = owner.1 :=
  rfl

noncomputable def stepEndToEndGuardedFirstLeftReceiverFor
    (key : EndToEndInitialRightBoundaryKey A package)
    (ownerControl : (endToEndInitialRightBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstLeftMonitor A package key).State)
    (move : In₁ × In₂) : EndToEndFirstLeftRoundResult A package key := by
  classical
  let activation := endToEndInitialRightBoundaryActivation A package key
  let controller := endToEndInitialRightBoundaryController A package key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (endToEndFirstLeftMonitor A package key).step monitorState
    (move, output, label.1 move.2)
  if hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      ProfiledGuardedLeftPolicyAllows A key.1.2.2.2 activation.profile
        activation.policy (output.target row) then
    let child : EndToEndGuardedLeftChild A key.1.2.2.2 activation.profile
        activation.policy := ⟨output.target row, hsafe.2⟩
    exact (output, nextMonitor,
      some (child.recurrentRightMacroOfClose A monitorState.2.1 row physical
        hsafe.1))
  else
    exact (output, nextMonitor, none)

noncomputable def endToEndGuardedFirstLeftOwnerControlFor
    (receiver : EndToEndGuardedFirstLeftReceiverControl A package)
    (owner : EndToEndGuardedFirstLeftOwnerControl A package) :
    (endToEndInitialRightBoundaryController A package receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (endToEndInitialRightBoundaryController A package receiver.1).initial

noncomputable def continueEndToEndGuardedFirstLeftReceiver
    (receiver : EndToEndGuardedFirstLeftReceiverControl A package)
    (owner : EndToEndGuardedFirstLeftOwnerControl A package)
    (move : In₁ × In₂) :
    Out₁ × EndToEndGuardedFirstLeftReceiverControl A package :=
  let result := stepEndToEndGuardedFirstLeftReceiverFor A package receiver.1
    (endToEndGuardedFirstLeftOwnerControlFor A package receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

@[simp] theorem continueEndToEndGuardedFirstLeftReceiver_key
    (receiver : EndToEndGuardedFirstLeftReceiverControl A package)
    (owner : EndToEndGuardedFirstLeftOwnerControl A package)
    (move : In₁ × In₂) :
    (continueEndToEndGuardedFirstLeftReceiver A package receiver owner
      move).2.1 = receiver.1 := rfl

@[simp] theorem stepEndToEndGuardedFirstLeftReceiverFor_output
    (key : EndToEndInitialRightBoundaryKey A package)
    (ownerControl : (endToEndInitialRightBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstLeftMonitor A package key).State)
    (move : In₁ × In₂) :
    (stepEndToEndGuardedFirstLeftReceiverFor A package key ownerControl row
      monitorState move).1 =
      ((endToEndInitialRightBoundaryController A package key).labelOf
        ownerControl).2 monitorState move := by
  classical
  simp only [stepEndToEndGuardedFirstLeftReceiverFor]
  split <;> rfl

@[simp] theorem stepEndToEndGuardedFirstLeftReceiverFor_monitor
    (key : EndToEndInitialRightBoundaryKey A package)
    (ownerControl : (endToEndInitialRightBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstLeftMonitor A package key).State)
    (move : In₁ × In₂) :
    (stepEndToEndGuardedFirstLeftReceiverFor A package key ownerControl row
      monitorState move).2.1 =
      (endToEndFirstLeftMonitor A package key).step monitorState
        (narrowedRecord (endToEndFirstLeftMonitor A package key)
          ((endToEndInitialRightBoundaryController A package key).labelOf
            ownerControl) monitorState move) := by
  classical
  simp only [stepEndToEndGuardedFirstLeftReceiverFor, narrowedRecord]
  split <;> rfl

/-- Process-swapped pending-profile identity for the exceptional left close. -/
theorem stepEndToEndGuardedFirstLeftReceiverFor_pending_of_staged
    (key : EndToEndInitialRightBoundaryKey A package)
    (ownerControl : (endToEndInitialRightBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstLeftMonitor A package key).State)
    (move : In₁ × In₂)
    (target : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy))
    (hstage : (stepEndToEndGuardedFirstLeftReceiverFor A package key
      ownerControl row monitorState move).2.2 = some target) :
    (stepEndToEndGuardedFirstLeftReceiverFor A package key ownerControl row
      monitorState move).2.1.2.2.1 row = some target.2.1.2 := by
  classical
  let activation := endToEndInitialRightBoundaryActivation A package key
  let controller := endToEndInitialRightBoundaryController A package key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (endToEndFirstLeftMonitor A package key).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      ProfiledGuardedLeftPolicyAllows A key.1.2.2.2 activation.profile
        activation.policy (output.target row)
  · cases htarget : output.target row with
    | inl trivial =>
        rw [htarget] at hsafe
        cases row <;>
          simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
    | inr live =>
        cases live with
        | inl rightLive =>
            let child : EndToEndGuardedLeftChild A key.1.2.2.2
                activation.profile activation.policy :=
              ⟨output.target row, hsafe.2⟩
            have hstep :
                stepEndToEndGuardedFirstLeftReceiverFor A package key
                    ownerControl row monitorState move =
                  (output, nextMonitor,
                    some (child.recurrentRightMacroOfClose A monitorState.2.1
                      row physical hsafe.1)) := by
              simp [stepEndToEndGuardedFirstLeftReceiverFor, activation,
                controller, label, output, physical, nextMonitor, hsafe,
                child]
            rw [hstep] at hstage ⊢
            simp only [Option.some.injEq] at hstage
            have htargetProfile : target.2.1.2 = rightLive.2 := by
              rw [← hstage]
              exact child.recurrentRightMacroOfClose_profile_of_eq A rightLive
                monitorState.2.1 row physical htarget hsafe.1
            change rightProfileOfProfiledState A (output.target row) =
              some target.2.1.2
            rw [htarget]
            exact congrArg some htargetProfile.symm
        | inr leftLive =>
            rw [htarget] at hsafe
            cases row <;>
              simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
  · have hstep :
        stepEndToEndGuardedFirstLeftReceiverFor A package key ownerControl
            row monitorState move = (output, nextMonitor, none) := by
      simp [stepEndToEndGuardedFirstLeftReceiverFor, activation, controller,
        label, output, physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-- Process-swapped parity seam for an exceptional left close. -/
theorem stepEndToEndGuardedFirstLeftReceiverFor_initial_of_staged
    (key : EndToEndInitialRightBoundaryKey A package)
    (ownerControl : (endToEndInitialRightBoundaryController A package key).Control)
    (row : PairedEntryRow)
    (monitorState : (endToEndFirstLeftMonitor A package key).State)
    (move : In₁ × In₂)
    (target : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy))
    (hstage : (stepEndToEndGuardedFirstLeftReceiverFor A package key
      ownerControl row monitorState move).2.2 = some target) :
    (.inr (.inl target.2.1) : PairedProfiledTreeState A) =
      (target.1.policy A).run [] := by
  classical
  let activation := endToEndInitialRightBoundaryActivation A package key
  let controller := endToEndInitialRightBoundaryController A package key
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (endToEndFirstLeftMonitor A package key).step
    monitorState (move, output, label.1 move.2)
  by_cases hsafe : erasePairedProfiledState A (output.target row) =
        pairedLeftCloseTarget A monitorState.2.1 row physical ∧
      ProfiledGuardedLeftPolicyAllows A key.1.2.2.2 activation.profile
        activation.policy (output.target row)
  · let child : EndToEndGuardedLeftChild A key.1.2.2.2
        activation.profile activation.policy :=
      ⟨output.target row, hsafe.2⟩
    have hstep :
        stepEndToEndGuardedFirstLeftReceiverFor A package key ownerControl
            row monitorState move =
          (output, nextMonitor,
            some (child.recurrentRightMacroOfClose A monitorState.2.1 row
              physical hsafe.1)) := by
      simp [stepEndToEndGuardedFirstLeftReceiverFor, activation, controller,
        label, output, physical, nextMonitor, hsafe, child]
    rw [hstep] at hstage
    simp only [Option.some.injEq] at hstage
    rw [← hstage]
    exact child.recurrentRightMacroOfClose_initial A monitorState.2.1 row
      physical hsafe.1
  · have hstep :
        stepEndToEndGuardedFirstLeftReceiverFor A package key ownerControl
            row monitorState move = (output, nextMonitor, none) := by
      simp [stepEndToEndGuardedFirstLeftReceiverFor, activation, controller,
        label, output, physical, nextMonitor, hsafe]
    rw [hstep] at hstage
    simp at hstage

end


end DetParityAutomaton

end DistributedSynthesis
