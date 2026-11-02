/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPolicyClose
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBlockMonitor

/-!
# Projecting singleton raw-joint policy targets to profiled block targets

The finite-code policy need not install a semantic witness at its successor.
For physical block regularization it is enough that the successor *code* has
the exact singleton target shape.  This file extracts that shape.

A right physical close leaves one process-two/left slot; a left close leaves
one process-one/right slot.  Projecting that unique live slot gives exactly
the old `PairedProfiledTreeState` child used by the block monitor.  Hence its
stored action profile is the literal closing profile, and the next physical
round satisfies the delayed overlap check.  All statements are finite-code
facts and require no target semantic provenance.
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

/-! ## Finite target projections -/

/-- Project the unique process-two/left slot expected after a right block to
the old profiled-state carrier.  An absent slot is mapped to the old sink. -/
def profiledRawJointUnitRightTargetProjection
    (code : ProfiledRawJointIncidenceCode A (I := Unit)) :
    PairedProfiledTreeState A :=
  match code.family.left () with
  | some slot => .inr (.inr slot)
  | none => .inl PUnit.unit

/-- Project the unique process-one/right slot expected after a left block. -/
def profiledRawJointUnitLeftTargetProjection
    (code : ProfiledRawJointIncidenceCode A (I := Unit)) :
    PairedProfiledTreeState A :=
  match code.family.right () with
  | some slot => .inr (.inl slot)
  | none => .inl PUnit.unit

/-! ## Exact physical child shape -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- The projected target code of a concrete right close is exactly the old
profiled child of the selected source slot and lambda. -/
theorem profiledRawJointUnitRightTargetProjection_next
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁)
    (source : ProfiledRawRightSlot A)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.right () = some source)
    (hlambda : move.rightLambda () = some lambda)
    (hfunctional : code.family.rightPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.rightPattern ((), row) ((), row) = true) :
    profiledRawJointUnitRightTargetProjection A
        (profiledRawJointOneSidedNext A code move
          (profiledRawJointUnitRightActualDirection
            (In₁ := In₁) (In₂ := In₂) row past input)) =
      pairedProfiledOneChild A source.1.1 lambda row past input := by
  rw [profiledRawJointUnitRightTargetProjection,
    profiledRawJointOneSidedNext_unitRight_leftSlot A code move row past input
      source lambda hsource hlambda hfunctional hreflexive,
    pairedProfiledOneChild_eq_profiledRawRightChildSlot A source lambda row
      past input]

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Left-close mirror. -/
theorem profiledRawJointUnitLeftTargetProjection_next
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂)
    (source : ProfiledRawLeftSlot A)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.left () = some source)
    (hlambda : move.leftLambda () = some lambda)
    (hfunctional : code.family.leftPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.leftPattern ((), row) ((), row) = true) :
    profiledRawJointUnitLeftTargetProjection A
        (profiledRawJointOneSidedNext A code move
          (profiledRawJointUnitLeftActualDirection
            (In₁ := In₁) (In₂ := In₂) row past input)) =
      pairedProfiledTwoChild A source.1.1 lambda row past input := by
  rw [profiledRawJointUnitLeftTargetProjection,
    profiledRawJointOneSidedNext_unitLeft_rightSlot A code move row past input
      source lambda hsource hlambda hfunctional hreflexive,
    pairedProfiledTwoChild_eq_profiledRawLeftChildSlot A source lambda row
      past input]

/-! ## Scanner and stored-profile projections -/

section
omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- Erasing the projected right target gives exactly the physical scanner's
close target. -/
theorem erase_profiledRawJointUnitRightTargetProjection_next
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁)
    (source : ProfiledRawRightSlot A)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.right () = some source)
    (hlambda : move.rightLambda () = some lambda)
    (hfunctional : code.family.rightPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.rightPattern ((), row) ((), row) = true) :
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          (profiledRawJointOneSidedNext A code move
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))) =
      pairedRightCloseTarget A
        (pairedRightScanAfter A source.1.1 lambda past) row
        (pairedRightBlockLetterAt lambda past input) := by
  rw [profiledRawJointUnitRightTargetProjection_next A code move row past
      input source lambda hsource hlambda hfunctional hreflexive,
    erase_pairedProfiledOneChild,
    pairedRightCloseTarget_scanAfter]

/-- Left scanner mirror. -/
theorem erase_profiledRawJointUnitLeftTargetProjection_next
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂)
    (source : ProfiledRawLeftSlot A)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.left () = some source)
    (hlambda : move.leftLambda () = some lambda)
    (hfunctional : code.family.leftPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.leftPattern ((), row) ((), row) = true) :
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          (profiledRawJointOneSidedNext A code move
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))) =
      pairedLeftCloseTarget A
        (pairedLeftScanAfter A source.1.1 lambda past) row
        (pairedLeftBlockLetterAt lambda past input) := by
  rw [profiledRawJointUnitLeftTargetProjection_next A code move row past
      input source lambda hsource hlambda hfunctional hreflexive,
    erase_pairedProfiledTwoChild,
    pairedLeftCloseTarget_scanAfter]

/-- The finite right-policy target stores exactly the profile needed at the
following left-block boundary. -/
theorem profiledRawJointUnitRightTargetProjection_next_profile
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁)
    (source : ProfiledRawRightSlot A)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.right () = some source)
    (hlambda : move.rightLambda () = some lambda)
    (hfunctional : code.family.rightPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.rightPattern ((), row) ((), row) = true) :
    leftProfileOfProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          (profiledRawJointOneSidedNext A code move
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))) =
      some (rightClosingProfile lambda row past input) := by
  rw [profiledRawJointUnitRightTargetProjection_next A code move row past
    input source lambda hsource hlambda hfunctional hreflexive]
  cases row <;> rfl

/-- Stored profile mirror. -/
theorem profiledRawJointUnitLeftTargetProjection_next_profile
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂)
    (source : ProfiledRawLeftSlot A)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.left () = some source)
    (hlambda : move.leftLambda () = some lambda)
    (hfunctional : code.family.leftPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.leftPattern ((), row) ((), row) = true) :
    rightProfileOfProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          (profiledRawJointOneSidedNext A code move
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))) =
      some (leftClosingProfile lambda row past input) := by
  rw [profiledRawJointUnitLeftTargetProjection_next A code move row past
    input source lambda hsource hlambda hfunctional hreflexive]
  cases row <;> rfl

end

/-! ## Delayed-overlap adapters -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- The following right-block letter realizes every profile read from the
previous finite policy target.  This is the old monitor's delayed-overlap
field, now derived solely from target-code shape. -/
theorem profiledRawJointUnitRightTargetProjection_delayedOverlap
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input nextInput : In₂ × In₁)
    (source : ProfiledRawRightSlot A)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.right () = some source)
    (hlambda : move.rightLambda () = some lambda)
    (hfunctional : code.family.rightPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.rightPattern ((), row) ((), row) = true)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hexpected : leftProfileOfProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          (profiledRawJointOneSidedNext A code move
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))) =
      some expected) :
    pairedRightClosingForRow row
        (profiledRightReceiverStrategy A source.1.1 lambda (past ++ [input])
          nextInput).physical =
      expected (nextInput.2, nextInput.1) := by
  rw [profiledRawJointUnitRightTargetProjection_next_profile A code move row
    past input source lambda hsource hlambda hfunctional hreflexive] at hexpected
  have heq := Option.some.inj hexpected
  subst expected
  exact profiledRightReceiverStrategy_overlap A source.1.1 lambda row past
    input nextInput

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Delayed-overlap mirror. -/
theorem profiledRawJointUnitLeftTargetProjection_delayedOverlap
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input nextInput : In₁ × In₂)
    (source : ProfiledRawLeftSlot A)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hsource : code.family.left () = some source)
    (hlambda : move.leftLambda () = some lambda)
    (hfunctional : code.family.leftPattern.RowFunctionalAt ((), row))
    (hreflexive : code.family.leftPattern ((), row) ((), row) = true)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hexpected : rightProfileOfProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          (profiledRawJointOneSidedNext A code move
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))) =
      some expected) :
    pairedLeftClosingForRow row
        (profiledLeftReceiverStrategy A source.1.1 lambda (past ++ [input])
          nextInput).physical =
      expected (nextInput.2, nextInput.1) := by
  rw [profiledRawJointUnitLeftTargetProjection_next_profile A code move row
    past input source lambda hsource hlambda hfunctional hreflexive] at hexpected
  have heq := Option.some.inj hexpected
  subst expected
  exact profiledLeftReceiverStrategy_overlap A source.1.1 lambda row past
    input nextInput

end

end DetParityAutomaton

end DistributedSynthesis
