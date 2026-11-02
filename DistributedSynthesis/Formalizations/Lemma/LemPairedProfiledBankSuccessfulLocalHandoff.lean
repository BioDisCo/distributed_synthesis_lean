/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBothOverlap

/-!
# Exact successful handoff for the profiled feasible bank

`PairedProfiledTreeState` already stores the finite boundary annotation needed
at a switch: a right child stores the complete right initial-action profile,
and a left child stores its left mirror.  The annotation is computed inside
the parent's paired-entry transition, before any child policy is selected.

This file records the corresponding readback facts.  A successful receiver
step preserves the one feasible-policy bank, identifies its staged macro with
the exact annotated policy successor, and exposes the `Allowed` edge.  On a
real finite-controller prefix, the sticky profile law then gives the physical
cross-output equality directly.  The final theorem does not ask for a
`ProfiledBankRightBoundaryCompatible` or
`ProfiledBankLeftBoundaryCompatible` premise.
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

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
private theorem profiledBankLeftMacroOfRightCertificate_live_of_eq
    (source : ProfiledBankRightMacro A)
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
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1)) target) :
    let result := profiledBankLeftMacroOfRightCertificate A source target scan
      row letter herase hallowed
    result.1 = source.1 ∧ result.2.1 = live := by
  subst target
  exact ⟨rfl, rfl⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
private theorem profiledBankRightMacroOfLeftCertificate_live_of_eq
    (source : ProfiledBankLeftMacro A)
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
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1)) target) :
    let result := profiledBankRightMacroOfLeftCertificate A source target scan
      row letter herase hallowed
    result.1 = source.1 ∧ result.2.1 = live := by
  subst target
  exact ⟨rfl, rfl⟩

/-- A successful right receiver step is the exact annotated successor of the
unchanged feasible profiled policy. -/
theorem stepProfiledBankRightReceiverFor_some_exact
    (source : ProfiledBankRightMacro A)
    (ownerControl : (profiledBankRightController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankRightMonitor A source).State)
    (move : In₂ × In₁)
    (target : ProfiledBankLeftMacro A)
    (hstage :
      (stepProfiledBankRightReceiverFor A source ownerControl row monitorState
        move).2.2 = some target) :
    target.1 = source.1 ∧
      (((profiledBankRightController A source).labelOf ownerControl).2
          monitorState move |>.target row) =
        .inr (.inr target.2.1) ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1))
          (.inr (.inr target.2.1)) := by
  classical
  let controller := profiledBankRightController A source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A
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
                  (output,
                    (profiledBankRightMonitor A source).step monitorState
                      (move, output, label.1 move.2),
                    some (profiledBankLeftMacroOfRightCertificate A source
                      (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledBankRightReceiverFor, controller, label,
                output, physical, hsafe]
            rw [hstep] at hstage
            simp only [Option.some.injEq] at hstage
            have hconstructed :=
              profiledBankLeftMacroOfRightCertificate_live_of_eq A source
                (output.target row) leftLive monitorState.2.1 row physical
                  htarget hsafe.1 hsafe.2
            have hbank : target.1 = source.1 := by
              rw [← hstage]
              exact hconstructed.1
            have hlive : target.2.1 = leftLive := by
              rw [← hstage]
              exact hconstructed.2
            refine ⟨hbank, ?_, ?_⟩
            · exact congrArg
                (fun live =>
                  (Sum.inr (Sum.inr live) : PairedProfiledTreeState A))
                hlive.symm
            · rw [hlive]
              simpa [htarget] using hsafe.2
  · have hstep :
        stepProfiledBankRightReceiverFor A source ownerControl row
            monitorState move =
          (output,
            (profiledBankRightMonitor A source).step monitorState
              (move, output, label.1 move.2), none) := by
      simp [stepProfiledBankRightReceiverFor, controller, label, output,
        physical, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-- Left-oriented exact annotated successor. -/
theorem stepProfiledBankLeftReceiverFor_some_exact
    (source : ProfiledBankLeftMacro A)
    (ownerControl : (profiledBankLeftController A source).Control)
    (row : PairedEntryRow)
    (monitorState : (profiledBankLeftMonitor A source).State)
    (move : In₁ × In₂)
    (target : ProfiledBankRightMacro A)
    (hstage :
      (stepProfiledBankLeftReceiverFor A source ownerControl row monitorState
        move).2.2 = some target) :
    target.1 = source.1 ∧
      (((profiledBankLeftController A source).labelOf ownerControl).2
          monitorState move |>.target row) =
        .inr (.inl target.2.1) ∧
      PairedProfiledRationalPolicy.Allowed A
        (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1))
          (.inr (.inl target.2.1)) := by
  classical
  let controller := profiledBankLeftController A source
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A
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
                  (output,
                    (profiledBankLeftMonitor A source).step monitorState
                      (move, output, label.1 move.2),
                    some (profiledBankRightMacroOfLeftCertificate A source
                      (output.target row) monitorState.2.1 row physical
                        hsafe.1 hsafe.2)) := by
              simp [stepProfiledBankLeftReceiverFor, controller, label,
                output, physical, hsafe]
            rw [hstep] at hstage
            simp only [Option.some.injEq] at hstage
            have hconstructed :=
              profiledBankRightMacroOfLeftCertificate_live_of_eq A source
                (output.target row) rightLive monitorState.2.1 row physical
                  htarget hsafe.1 hsafe.2
            have hbank : target.1 = source.1 := by
              rw [← hstage]
              exact hconstructed.1
            have hlive : target.2.1 = rightLive := by
              rw [← hstage]
              exact hconstructed.2
            refine ⟨hbank, ?_, ?_⟩
            · exact congrArg
                (fun live =>
                  (Sum.inr (Sum.inl live) : PairedProfiledTreeState A))
                hlive.symm
            · rw [hlive]
              simpa [htarget] using hsafe.2
        | inr leftLive =>
            rw [htarget] at hsafe
            cases row <;>
              simp [erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
  · have hstep :
        stepProfiledBankLeftReceiverFor A source ownerControl row
            monitorState move =
          (output,
            (profiledBankLeftMonitor A source).step monitorState
              (move, output, label.1 move.2), none) := by
      simp [stepProfiledBankLeftReceiverFor, controller, label, output,
        physical, hsafe]
    rw [hstep] at hstage
    simp at hstage

/-! ## Direct physical equality at a real annotated handoff -/

/-- If a real right-bank prefix stages the annotated child `target`, the
fresh left receiver output is the old right close.  This is the operational
boundary-compatibility property. -/
theorem profiledBankRight_real_staged_cross_output_eq
    (source : ProfiledBankRightMacro A) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (stagingMove : In₂ × In₁)
    (target : ProfiledBankLeftMacro A)
    (hstage :
      (stepProfiledBankRightReceiverFor A source
        (profiledBankRightFiniteStateAfter A source past).1 row
        (profiledBankRightFiniteStateAfter A source past).2
        stagingMove).2.2 = some target)
    (move : In₁ × In₂) :
    (switchProfiledBankRightOwnerToBankLeftReceiver A
        ⟨source,
          (profiledBankRightFiniteStateAfter A source
            (past ++ [stagingMove])).1⟩
        ⟨source, row,
          (profiledBankRightFiniteStateAfter A source
            (past ++ [stagingMove])).2, some target⟩
        move false).1 =
      pairedRightClosingForRow row
        (stepProfiledBankRightReceiverFor A source
          (profiledBankRightFiniteStateAfter A source
            (past ++ [stagingMove])).1 row
          (profiledBankRightFiniteStateAfter A source
            (past ++ [stagingMove])).2
          (move.2, move.1)).1.physical := by
  obtain ⟨actual, hactual, hcompatible⟩ :=
    profiledBankRight_real_both_compatible A source row past stagingMove move
  rw [hstage] at hactual
  simp only [Option.some.injEq] at hactual
  subst actual
  simpa [ProfiledBankRightBoundaryCompatible,
    profiledBankRightOwnerControlFor] using hcompatible

/-- Left-oriented mirror of the direct physical equality. -/
theorem profiledBankLeft_real_staged_cross_output_eq
    (source : ProfiledBankLeftMacro A) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (stagingMove : In₁ × In₂)
    (target : ProfiledBankRightMacro A)
    (hstage :
      (stepProfiledBankLeftReceiverFor A source
        (profiledBankLeftFiniteStateAfter A source past).1 row
        (profiledBankLeftFiniteStateAfter A source past).2
        stagingMove).2.2 = some target)
    (move : In₂ × In₁) :
    (switchProfiledBankLeftOwnerToBankRightReceiver A
        ⟨source,
          (profiledBankLeftFiniteStateAfter A source
            (past ++ [stagingMove])).1⟩
        ⟨source, row,
          (profiledBankLeftFiniteStateAfter A source
            (past ++ [stagingMove])).2, some target⟩
        move false).1 =
      pairedLeftClosingForRow row
        (stepProfiledBankLeftReceiverFor A source
          (profiledBankLeftFiniteStateAfter A source
            (past ++ [stagingMove])).1 row
          (profiledBankLeftFiniteStateAfter A source
            (past ++ [stagingMove])).2
          (move.2, move.1)).1.physical := by
  obtain ⟨actual, hactual, hcompatible⟩ :=
    profiledBankLeft_real_both_compatible A source row past stagingMove move
  rw [hstage] at hactual
  simp only [Option.some.injEq] at hactual
  subst actual
  simpa [ProfiledBankLeftBoundaryCompatible,
    profiledBankLeftOwnerControlFor] using hcompatible

end


end DetParityAutomaton

end DistributedSynthesis
