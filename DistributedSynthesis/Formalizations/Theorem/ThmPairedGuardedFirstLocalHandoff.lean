/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedFirstControllerBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedBankLocalHandoff

/-!
# Local handoff from the guarded first block to the ordinary bank

The guarded controller is used for exactly one recurrent block.  At its close,
the receiving process packages the concrete paired child and its checked
`HasRationalRun` fact as a `FeasiblePairedState`; from then on the ordinary
finite controller bank applies unchanged.  The latent row is the locally
observable receipt row, not a test for the global strict leader.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (bank : FiniteGuardedFirstControllerBank A)

noncomputable def guardedFirstRightControllerAt
    (key : GuardedFirstRightMacro A) := bank.rightController key

noncomputable def guardedFirstLeftControllerAt
    (key : GuardedFirstLeftMacro A) := bank.leftController key

abbrev GuardedFirstRightOwnerControl :=
  Σ key : GuardedFirstRightMacro A,
    (guardedFirstRightControllerAt A bank key).Control

abbrev GuardedFirstLeftOwnerControl :=
  Σ key : GuardedFirstLeftMacro A,
    (guardedFirstLeftControllerAt A bank key).Control

noncomputable instance : Fintype (GuardedFirstRightOwnerControl A bank) := by
  classical
  infer_instance

noncomputable instance : Fintype (GuardedFirstLeftOwnerControl A bank) := by
  classical
  infer_instance

abbrev GuardedFirstRightReceiverControl :=
  Σ key : GuardedFirstRightMacro A,
    PairedEntryRow × (GuardedFirstRightMonitor A key.1 key.2.1.1).State ×
      Option (BankLeftMacro A)

abbrev GuardedFirstLeftReceiverControl :=
  Σ key : GuardedFirstLeftMacro A,
    PairedEntryRow × (GuardedFirstLeftMonitor A key.1 key.2.1.1).State ×
      Option (BankRightMacro A)

noncomputable instance : Fintype (GuardedFirstRightReceiverControl A) := by
  classical
  infer_instance

noncomputable instance : Fintype (GuardedFirstLeftReceiverControl A) := by
  classical
  infer_instance

noncomputable def initialGuardedFirstRightOwner
    (key : GuardedFirstRightMacro A) : GuardedFirstRightOwnerControl A bank :=
  ⟨key, (guardedFirstRightControllerAt A bank key).initial⟩

noncomputable def initialGuardedFirstLeftOwner
    (key : GuardedFirstLeftMacro A) : GuardedFirstLeftOwnerControl A bank :=
  ⟨key, (guardedFirstLeftControllerAt A bank key).initial⟩

noncomputable def initialGuardedFirstRightReceiver
    (key : GuardedFirstRightMacro A) (row : PairedEntryRow) :
    GuardedFirstRightReceiverControl A :=
  ⟨key, row, (GuardedFirstRightMonitor A key.1 key.2.1.1).initial, none⟩

noncomputable def initialGuardedFirstLeftReceiver
    (key : GuardedFirstLeftMacro A) (row : PairedEntryRow) :
    GuardedFirstLeftReceiverControl A :=
  ⟨key, row, (GuardedFirstLeftMonitor A key.1 key.2.1.1).initial, none⟩

noncomputable def stepGuardedFirstRightOwner
    (owner : GuardedFirstRightOwnerControl A bank) (input : In₁) :
    Out₁ × GuardedFirstRightOwnerControl A bank :=
  let controller := guardedFirstRightControllerAt A bank owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepGuardedFirstLeftOwner
    (owner : GuardedFirstLeftOwnerControl A bank) (input : In₂) :
    Out₂ × GuardedFirstLeftOwnerControl A bank :=
  let controller := guardedFirstLeftControllerAt A bank owner.1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepGuardedFirstRightOwner_key
    (owner : GuardedFirstRightOwnerControl A bank) (input : In₁) :
    (stepGuardedFirstRightOwner A bank owner input).2.1 = owner.1 := rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepGuardedFirstLeftOwner_key
    (owner : GuardedFirstLeftOwnerControl A bank) (input : In₂) :
    (stepGuardedFirstLeftOwner A bank owner input).2.1 = owner.1 := rfl

/-- Concrete ordinary-bank macro selected by a close of the exceptional
right block. -/
def guardedFirstRightCloseMacro
    (key : GuardedFirstRightMacro A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  match pairedRightCloseTarget A scan row letter with
  | Sum.inr (Sum.inr target) => target
  | _ => key.2.1

def guardedFirstLeftCloseMacro
    (key : GuardedFirstLeftMacro A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (A.State × A.State) × A.State :=
  match pairedLeftCloseTarget A scan row letter with
  | Sum.inr (Sum.inl target) => target
  | _ => key.2.1

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem guardedFirstRightCloseMacro_state
    (key : GuardedFirstRightMacro A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    Sum.inr (Sum.inr (guardedFirstRightCloseMacro A key scan row letter)) =
      pairedRightCloseTarget A scan row letter := by
  cases row <;> rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem guardedFirstLeftCloseMacro_state
    (key : GuardedFirstLeftMacro A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    Sum.inr (Sum.inl (guardedFirstLeftCloseMacro A key scan row letter)) =
      pairedLeftCloseTarget A scan row letter := by
  cases row <;> rfl

abbrev GuardedFirstRightReceiverRoundResult (key : GuardedFirstRightMacro A) :=
  PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    (GuardedFirstRightMonitor A key.1 key.2.1.1).State × Option (BankLeftMacro A)

abbrev GuardedFirstLeftReceiverRoundResult (key : GuardedFirstLeftMacro A) :=
  PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂) ×
    (GuardedFirstLeftMonitor A key.1 key.2.1.1).State × Option (BankRightMacro A)

/-- Full-information receiver computation for the exceptional right block.
The optional handoff is populated exactly when the concrete child is a
feasible ordinary-bank root. -/
noncomputable def stepGuardedFirstRightReceiverFor
    (key : GuardedFirstRightMacro A)
    (ownerControl : (guardedFirstRightControllerAt A bank key).Control)
    (row : PairedEntryRow)
    (monitorState : (GuardedFirstRightMonitor A key.1 key.2.1.1).State)
    (move : In₂ × In₁) : GuardedFirstRightReceiverRoundResult A key := by
  classical
  let controller := guardedFirstRightControllerAt A bank key
  let label := controller.labelOf ownerControl
  let receiverOutput := label.2 monitorState move
  let letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, receiverOutput, label.1 move.2)
  let nextMonitor := (GuardedFirstRightMonitor A key.1 key.2.1.1).step
    monitorState letter
  let targetData := guardedFirstRightCloseMacro A key monitorState.2.1 row letter
  if hfeasible : (pairedEntryRunAutomaton A
      (Sum.inr (Sum.inr targetData))).HasRationalRun then
    let target : FeasiblePairedState A :=
      ⟨Sum.inr (Sum.inr targetData), hfeasible⟩
    exact (receiverOutput, nextMonitor,
      some (bankLeftRoot A target targetData rfl))
  else
    exact (receiverOutput, nextMonitor, none)

/-- Process-two mirror. -/
noncomputable def stepGuardedFirstLeftReceiverFor
    (key : GuardedFirstLeftMacro A)
    (ownerControl : (guardedFirstLeftControllerAt A bank key).Control)
    (row : PairedEntryRow)
    (monitorState : (GuardedFirstLeftMonitor A key.1 key.2.1.1).State)
    (move : In₁ × In₂) : GuardedFirstLeftReceiverRoundResult A key := by
  classical
  let controller := guardedFirstLeftControllerAt A bank key
  let label := controller.labelOf ownerControl
  let receiverOutput := label.2 monitorState move
  let letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, receiverOutput, label.1 move.2)
  let nextMonitor := (GuardedFirstLeftMonitor A key.1 key.2.1.1).step
    monitorState letter
  let targetData := guardedFirstLeftCloseMacro A key monitorState.2.1 row letter
  if hfeasible : (pairedEntryRunAutomaton A
      (Sum.inr (Sum.inl targetData))).HasRationalRun then
    let target : FeasiblePairedState A :=
      ⟨Sum.inr (Sum.inl targetData), hfeasible⟩
    exact (receiverOutput, nextMonitor,
      some (bankRightRoot A target targetData rfl))
  else
    exact (receiverOutput, nextMonitor, none)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem stepGuardedFirstRightReceiverFor_staged_of_feasible
    (key : GuardedFirstRightMacro A)
    (ownerControl : (guardedFirstRightControllerAt A bank key).Control)
    (row : PairedEntryRow)
    (monitorState : (GuardedFirstRightMonitor A key.1 key.2.1.1).State)
    (move : In₂ × In₁)
    (hfeasible : (pairedEntryRunAutomaton A
      (Sum.inr (Sum.inr (guardedFirstRightCloseMacro A key monitorState.2.1 row
        (move,
          (guardedFirstRightControllerAt A bank key).labelOf ownerControl |>.2
            monitorState move,
          (guardedFirstRightControllerAt A bank key).labelOf ownerControl |>.1
            move.2))))).HasRationalRun) :
    (stepGuardedFirstRightReceiverFor A bank key ownerControl row monitorState move).2.2.isSome := by
  classical
  simp [stepGuardedFirstRightReceiverFor, hfeasible]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem stepGuardedFirstLeftReceiverFor_staged_of_feasible
    (key : GuardedFirstLeftMacro A)
    (ownerControl : (guardedFirstLeftControllerAt A bank key).Control)
    (row : PairedEntryRow)
    (monitorState : (GuardedFirstLeftMonitor A key.1 key.2.1.1).State)
    (move : In₁ × In₂)
    (hfeasible : (pairedEntryRunAutomaton A
      (Sum.inr (Sum.inl (guardedFirstLeftCloseMacro A key monitorState.2.1 row
        (move,
          (guardedFirstLeftControllerAt A bank key).labelOf ownerControl |>.2
            monitorState move,
          (guardedFirstLeftControllerAt A bank key).labelOf ownerControl |>.1
            move.2))))).HasRationalRun) :
    (stepGuardedFirstLeftReceiverFor A bank key ownerControl row monitorState move).2.2.isSome := by
  classical
  simp [stepGuardedFirstLeftReceiverFor, hfeasible]

/-! ## Finite readback along a real exceptional block -/

abbrev GuardedFirstRightFiniteState (key : GuardedFirstRightMacro A) :=
  (guardedFirstRightControllerAt A bank key).Control ×
    (GuardedFirstRightMonitor A key.1 key.2.1.1).State

abbrev GuardedFirstLeftFiniteState (key : GuardedFirstLeftMacro A) :=
  (guardedFirstLeftControllerAt A bank key).Control ×
    (GuardedFirstLeftMonitor A key.1 key.2.1.1).State

noncomputable def initialGuardedFirstRightFiniteState
    (key : GuardedFirstRightMacro A) : GuardedFirstRightFiniteState A bank key :=
  ((guardedFirstRightControllerAt A bank key).initial,
    (GuardedFirstRightMonitor A key.1 key.2.1.1).initial)

noncomputable def initialGuardedFirstLeftFiniteState
    (key : GuardedFirstLeftMacro A) : GuardedFirstLeftFiniteState A bank key :=
  ((guardedFirstLeftControllerAt A bank key).initial,
    (GuardedFirstLeftMonitor A key.1 key.2.1.1).initial)

noncomputable def stepGuardedFirstRightFiniteState
    (key : GuardedFirstRightMacro A)
    (state : GuardedFirstRightFiniteState A bank key)
    (move : In₂ × In₁) : GuardedFirstRightFiniteState A bank key :=
  let controller := guardedFirstRightControllerAt A bank key
  let monitor := GuardedFirstRightMonitor A key.1 key.2.1.1
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def stepGuardedFirstLeftFiniteState
    (key : GuardedFirstLeftMacro A)
    (state : GuardedFirstLeftFiniteState A bank key)
    (move : In₁ × In₂) : GuardedFirstLeftFiniteState A bank key :=
  let controller := guardedFirstLeftControllerAt A bank key
  let monitor := GuardedFirstLeftMonitor A key.1 key.2.1.1
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def guardedFirstRightFiniteStateAfter
    (key : GuardedFirstRightMacro A) (past : List (In₂ × In₁)) :
    GuardedFirstRightFiniteState A bank key :=
  past.foldl (stepGuardedFirstRightFiniteState A bank key)
    (initialGuardedFirstRightFiniteState A bank key)

noncomputable def guardedFirstLeftFiniteStateAfter
    (key : GuardedFirstLeftMacro A) (past : List (In₁ × In₂)) :
    GuardedFirstLeftFiniteState A bank key :=
  past.foldl (stepGuardedFirstLeftFiniteState A bank key)
    (initialGuardedFirstLeftFiniteState A bank key)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem guardedFirstRightFiniteStateAfter_eq
    (key : GuardedFirstRightMacro A) : ∀ past : List (In₂ × In₁),
    guardedFirstRightFiniteStateAfter A bank key past =
      ((guardedFirstRightControllerAt A bank key).controlAt (senderWord past),
        narrowedControl (GuardedFirstRightMonitor A key.1 key.2.1.1)
          (guardedFirstRightControllerAt A bank key).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [guardedFirstRightFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepGuardedFirstRightFiniteState A bank key
        (guardedFirstRightFiniteStateAfter A bank key past) move = _
      rw [ih, senderWord_append,
        TransitionRationalTree.controlAt_append, narrowedControl_append]
      rfl

theorem guardedFirstLeftFiniteStateAfter_eq
    (key : GuardedFirstLeftMacro A) : ∀ past : List (In₁ × In₂),
    guardedFirstLeftFiniteStateAfter A bank key past =
      ((guardedFirstLeftControllerAt A bank key).controlAt (senderWord past),
        narrowedControl (GuardedFirstLeftMonitor A key.1 key.2.1.1)
          (guardedFirstLeftControllerAt A bank key).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [guardedFirstLeftFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepGuardedFirstLeftFiniteState A bank key
        (guardedFirstLeftFiniteStateAfter A bank key past) move = _
      rw [ih, senderWord_append,
        TransitionRationalTree.controlAt_append, narrowedControl_append]
      rfl

theorem guardedFirstRight_narrowedControl_scan
    (key : GuardedFirstRightMacro A) : ∀ past : List (In₂ × In₁),
    (narrowedControl (GuardedFirstRightMonitor A key.1 key.2.1.1)
      (guardedFirstRightControllerAt A bank key).labeledTree past).2.1 =
      pairedRightScanAfter A key.2.1.1
        (guardedFirstRightLambdaOfNarrowed A key.1 key.2.1.1
          (guardedFirstRightControllerAt A bank key).labeledTree) past := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, pairedRightScanAfter_append]
      change pairedRightScanStep A
        (narrowedControl (GuardedFirstRightMonitor A key.1 key.2.1.1)
          (guardedFirstRightControllerAt A bank key).labeledTree past).2.1
        (pairedRightBlockLetterAt
          (guardedFirstRightLambdaOfNarrowed A key.1 key.2.1.1
            (guardedFirstRightControllerAt A bank key).labeledTree)
          past move) = _
      rw [ih]

theorem guardedFirstLeft_narrowedControl_scan
    (key : GuardedFirstLeftMacro A) : ∀ past : List (In₁ × In₂),
    (narrowedControl (GuardedFirstLeftMonitor A key.1 key.2.1.1)
      (guardedFirstLeftControllerAt A bank key).labeledTree past).2.1 =
      pairedLeftScanAfter A key.2.1.1
        (guardedFirstLeftLambdaOfNarrowed A key.1 key.2.1.1
          (guardedFirstLeftControllerAt A bank key).labeledTree) past := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, pairedLeftScanAfter_append]
      change pairedLeftScanStep A
        (narrowedControl (GuardedFirstLeftMonitor A key.1 key.2.1.1)
          (guardedFirstLeftControllerAt A bank key).labeledTree past).2.1
        (pairedLeftBlockLetterAt
          (guardedFirstLeftLambdaOfNarrowed A key.1 key.2.1.1
            (guardedFirstLeftControllerAt A bank key).labeledTree)
          past move) = _
      rw [ih]

end

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Along a real controller path, every right-block close populates the
ordinary-bank handoff. -/
theorem guardedFirstRight_real_close_staged
    (key : GuardedFirstRightMacro A)
    (row : PairedEntryRow) (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (stepGuardedFirstRightReceiverFor A bank key
      (guardedFirstRightFiniteStateAfter A bank key past).1 row
      (guardedFirstRightFiniteStateAfter A bank key past).2 move).2.2.isSome := by
  apply stepGuardedFirstRightReceiverFor_staged_of_feasible A bank
  rw [guardedFirstRightFiniteStateAfter_eq A bank key]
  let lambda := guardedFirstRightLambdaOfNarrowed A key.1 key.2.1.1
    (guardedFirstRightControllerAt A bank key).labeledTree
  have hchild := (bank.rightActivation A key).childFeasible row past move
  let monitorState := narrowedControl
    (GuardedFirstRightMonitor A key.1 key.2.1.1)
    (guardedFirstRightControllerAt A bank key).labeledTree past
  let controller := guardedFirstRightControllerAt A bank key
  let letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move,
      (controller.labelOf (controller.controlAt (senderWord past))).2
        monitorState move,
      (controller.labelOf (controller.controlAt (senderWord past))).1 move.2)
  change (pairedEntryRunAutomaton A
    (Sum.inr (Sum.inr
      (guardedFirstRightCloseMacro A key monitorState.2.1 row letter)))).HasRationalRun
  rw [guardedFirstRightCloseMacro_state]
  rw [guardedFirstRight_narrowedControl_scan A bank key]
  change (pairedEntryRunAutomaton A
    (pairedRightCloseTarget A
      (pairedRightScanAfter A key.2.1.1 lambda past) row
      (pairedRightBlockLetterAt lambda past move))).HasRationalRun
  rw [pairedRightCloseTarget_scanAfter A key.2.1.1 lambda past move row]
  simpa [lambda, guardedFirstRightLambdaOfNarrowed,
    guardedFirstRightControllerAt, monitorState, controller, letter,
    FiniteGuardedFirstControllerBank.rightActivation,
    guardedFirstRightController_sound] using hchild

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem guardedFirstLeft_real_close_staged
    (key : GuardedFirstLeftMacro A)
    (row : PairedEntryRow) (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (stepGuardedFirstLeftReceiverFor A bank key
      (guardedFirstLeftFiniteStateAfter A bank key past).1 row
      (guardedFirstLeftFiniteStateAfter A bank key past).2 move).2.2.isSome := by
  apply stepGuardedFirstLeftReceiverFor_staged_of_feasible A bank
  rw [guardedFirstLeftFiniteStateAfter_eq A bank key]
  let lambda := guardedFirstLeftLambdaOfNarrowed A key.1 key.2.1.1
    (guardedFirstLeftControllerAt A bank key).labeledTree
  have hchild := (bank.leftActivation A key).childFeasible row past move
  let monitorState := narrowedControl
    (GuardedFirstLeftMonitor A key.1 key.2.1.1)
    (guardedFirstLeftControllerAt A bank key).labeledTree past
  let controller := guardedFirstLeftControllerAt A bank key
  let letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move,
      (controller.labelOf (controller.controlAt (senderWord past))).2
        monitorState move,
      (controller.labelOf (controller.controlAt (senderWord past))).1 move.2)
  change (pairedEntryRunAutomaton A
    (Sum.inr (Sum.inl
      (guardedFirstLeftCloseMacro A key monitorState.2.1 row letter)))).HasRationalRun
  rw [guardedFirstLeftCloseMacro_state]
  rw [guardedFirstLeft_narrowedControl_scan A bank key]
  change (pairedEntryRunAutomaton A
    (pairedLeftCloseTarget A
      (pairedLeftScanAfter A key.2.1.1 lambda past) row
      (pairedLeftBlockLetterAt lambda past move))).HasRationalRun
  rw [pairedLeftCloseTarget_scanAfter A key.2.1.1 lambda past move row]
  simpa [lambda, guardedFirstLeftLambdaOfNarrowed,
    guardedFirstLeftControllerAt, monitorState, controller, letter,
    FiniteGuardedFirstControllerBank.leftActivation,
    guardedFirstLeftController_sound] using hchild

end

end DetParityAutomaton

end DistributedSynthesis
