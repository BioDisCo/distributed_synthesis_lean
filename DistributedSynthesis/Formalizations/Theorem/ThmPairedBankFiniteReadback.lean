/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedPhaseCarrier

/-!
# Finite readback and total staging in the ordinary recurrent bank

This is the recurrent counterpart of the exceptional first-block readback.
The product of controller and monitor controls is finite, computes the exact
semantic scan, and stages an opposite-orientation bank key at every reachable
close.  The proof consumes the `ProcessOneCloseSafe`/`ProcessTwoCloseSafe`
field already extracted from each winning bank controller.
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

abbrev BankRightFiniteState (source : BankRightMacro A) :=
  (bankRightControllerAt A source).Control ×
    (bankRightMonitorAt A source).State

abbrev BankLeftFiniteState (source : BankLeftMacro A) :=
  (bankLeftControllerAt A source).Control ×
    (bankLeftMonitorAt A source).State

noncomputable def initialBankRightFiniteState
    (source : BankRightMacro A) : BankRightFiniteState A source :=
  ((bankRightControllerAt A source).initial,
    (bankRightMonitorAt A source).initial)

noncomputable def initialBankLeftFiniteState
    (source : BankLeftMacro A) : BankLeftFiniteState A source :=
  ((bankLeftControllerAt A source).initial,
    (bankLeftMonitorAt A source).initial)

noncomputable def stepBankRightFiniteState
    (source : BankRightMacro A) (state : BankRightFiniteState A source)
    (move : In₂ × In₁) : BankRightFiniteState A source :=
  let controller := bankRightControllerAt A source
  let monitor := bankRightMonitorAt A source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def stepBankLeftFiniteState
    (source : BankLeftMacro A) (state : BankLeftFiniteState A source)
    (move : In₁ × In₂) : BankLeftFiniteState A source :=
  let controller := bankLeftControllerAt A source
  let monitor := bankLeftMonitorAt A source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def bankRightFiniteStateAfter
    (source : BankRightMacro A) (past : List (In₂ × In₁)) :
    BankRightFiniteState A source :=
  past.foldl (stepBankRightFiniteState A source)
    (initialBankRightFiniteState A source)

noncomputable def bankLeftFiniteStateAfter
    (source : BankLeftMacro A) (past : List (In₁ × In₂)) :
    BankLeftFiniteState A source :=
  past.foldl (stepBankLeftFiniteState A source)
    (initialBankLeftFiniteState A source)

theorem bankRightFiniteStateAfter_eq
    (source : BankRightMacro A) : ∀ past : List (In₂ × In₁),
    bankRightFiniteStateAfter A source past =
      ((bankRightControllerAt A source).controlAt (senderWord past),
        narrowedControl (bankRightMonitorAt A source)
          (bankRightControllerAt A source).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [bankRightFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepBankRightFiniteState A source
        (bankRightFiniteStateAfter A source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

theorem bankLeftFiniteStateAfter_eq
    (source : BankLeftMacro A) : ∀ past : List (In₁ × In₂),
    bankLeftFiniteStateAfter A source past =
      ((bankLeftControllerAt A source).controlAt (senderWord past),
        narrowedControl (bankLeftMonitorAt A source)
          (bankLeftControllerAt A source).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [bankLeftFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepBankLeftFiniteState A source
        (bankLeftFiniteStateAfter A source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

theorem bankRight_narrowedControl_scan
    (source : BankRightMacro A) : ∀ past : List (In₂ × In₁),
    (narrowedControl (bankRightMonitorAt A source)
      (bankRightControllerAt A source).labeledTree past).2.1 =
      pairedRightScanAfter A source.2.1.1
        (pairedRightLambdaOfNarrowed A (feasiblePolicy A source.1)
          source.2.1.1 source.2.1.2
          (bankRightControllerAt A source).labeledTree) past := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, pairedRightScanAfter_append]
      change pairedRightScanStep A
        (narrowedControl (bankRightMonitorAt A source)
          (bankRightControllerAt A source).labeledTree past).2.1
        (pairedRightBlockLetterAt
          (pairedRightLambdaOfNarrowed A (feasiblePolicy A source.1)
            source.2.1.1 source.2.1.2
            (bankRightControllerAt A source).labeledTree) past move) = _
      rw [ih]

theorem bankLeft_narrowedControl_scan
    (source : BankLeftMacro A) : ∀ past : List (In₁ × In₂),
    (narrowedControl (bankLeftMonitorAt A source)
      (bankLeftControllerAt A source).labeledTree past).2.1 =
      pairedLeftScanAfter A source.2.1.1
        (pairedLeftLambdaOfNarrowed A (feasiblePolicy A source.1)
          source.2.1.1 source.2.1.2
          (bankLeftControllerAt A source).labeledTree) past := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, pairedLeftScanAfter_append]
      change pairedLeftScanStep A
        (narrowedControl (bankLeftMonitorAt A source)
          (bankLeftControllerAt A source).labeledTree past).2.1
        (pairedLeftBlockLetterAt
          (pairedLeftLambdaOfNarrowed A (feasiblePolicy A source.1)
            source.2.1.1 source.2.1.2
            (bankLeftControllerAt A source).labeledTree) past move) = _
      rw [ih]

/-- Every close along a real right-bank controller path stages a left-bank
key. -/
theorem bankRight_real_close_staged
    (source : BankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (stepBankRightReceiverFor A source
      (bankRightFiniteStateAfter A source past).1 row
      (bankRightFiniteStateAfter A source past).2 move).2.2.isSome := by
  apply Option.isSome_iff_exists.mpr
  rw [bankRightFiniteStateAfter_eq A source]
  let lambda := pairedRightLambdaOfNarrowed A (feasiblePolicy A source.1)
    source.2.1.1 source.2.1.2 (bankRightControllerAt A source).labeledTree
  have hallowed := ((feasibleControllerFamily A source.1).right_sound A
    source.2.1.1 source.2.1.2 source.2.2).2 row past move
  let monitorState := narrowedControl (bankRightMonitorAt A source)
    (bankRightControllerAt A source).labeledTree past
  let controller := bankRightControllerAt A source
  let letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, (controller.labelOf (controller.controlAt (senderWord past))).2
      monitorState move,
      (controller.labelOf (controller.controlAt (senderWord past))).1 move.2)
  have hallowed' : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inl source.2.1))
      (Sum.inr (Sum.inr
        (bankRightCloseMacro A source monitorState.2.1 row letter))) := by
    rw [bankRightCloseMacro_state]
    rw [bankRight_narrowedControl_scan A source]
    change PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inl source.2.1))
      (pairedRightCloseTarget A
        (pairedRightScanAfter A source.2.1.1 lambda past) row
        (pairedRightBlockLetterAt lambda past move))
    rw [pairedRightCloseTarget_scanAfter A source.2.1.1 lambda past move row]
    simpa [lambda, monitorState, controller, letter, bankRightControllerAt,
      bankRightMonitorAt] using hallowed
  rw [stepBankRightReceiverFor_staged_of_allowed A source
    (controller.controlAt (senderWord past)) row monitorState move hallowed']
  exact ⟨_, rfl⟩

/-- Left mirror. -/
theorem bankLeft_real_close_staged
    (source : BankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (stepBankLeftReceiverFor A source
      (bankLeftFiniteStateAfter A source past).1 row
      (bankLeftFiniteStateAfter A source past).2 move).2.2.isSome := by
  apply Option.isSome_iff_exists.mpr
  rw [bankLeftFiniteStateAfter_eq A source]
  let lambda := pairedLeftLambdaOfNarrowed A (feasiblePolicy A source.1)
    source.2.1.1 source.2.1.2 (bankLeftControllerAt A source).labeledTree
  have hallowed := ((feasibleControllerFamily A source.1).left_sound A
    source.2.1.1 source.2.1.2 source.2.2).2 row past move
  let monitorState := narrowedControl (bankLeftMonitorAt A source)
    (bankLeftControllerAt A source).labeledTree past
  let controller := bankLeftControllerAt A source
  let letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, (controller.labelOf (controller.controlAt (senderWord past))).2
      monitorState move,
      (controller.labelOf (controller.controlAt (senderWord past))).1 move.2)
  have hallowed' : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inr source.2.1))
      (Sum.inr (Sum.inl
        (bankLeftCloseMacro A source monitorState.2.1 row letter))) := by
    rw [bankLeftCloseMacro_state]
    rw [bankLeft_narrowedControl_scan A source]
    change PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inr source.2.1))
      (pairedLeftCloseTarget A
        (pairedLeftScanAfter A source.2.1.1 lambda past) row
        (pairedLeftBlockLetterAt lambda past move))
    rw [pairedLeftCloseTarget_scanAfter A source.2.1.1 lambda past move row]
    simpa [lambda, monitorState, controller, letter, bankLeftControllerAt,
      bankLeftMonitorAt] using hallowed
  rw [stepBankLeftReceiverFor_staged_of_allowed A source
    (controller.controlAt (senderWord past)) row monitorState move hallowed']
  exact ⟨_, rfl⟩

/-! ## End-to-end recurrent activation -/

/-- A real right-bank close not only stages a key: for either locally
observed receipt bit it activates a finite left-bank owner/receiver pair. -/
theorem activateBankLeftFromBankRight_real_isSome
    (source : BankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) (received : Bool) :
    (activateBankLeftFromBankRight A
      (stepBankRightReceiverFor A source
        (bankRightFiniteStateAfter A source past).1 row
        (bankRightFiniteStateAfter A source past).2 move)
      received).isSome := by
  simpa [activateBankLeftFromBankRight] using
    bankRight_real_close_staged A source row past move

/-- Left mirror. -/
theorem activateBankRightFromBankLeft_real_isSome
    (source : BankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) (received : Bool) :
    (activateBankRightFromBankLeft A
      (stepBankLeftReceiverFor A source
        (bankLeftFiniteStateAfter A source past).1 row
        (bankLeftFiniteStateAfter A source past).2 move)
      received).isSome := by
  simpa [activateBankRightFromBankLeft] using
    bankLeft_real_close_staged A source row past move

end


end DetParityAutomaton

end DistributedSynthesis
