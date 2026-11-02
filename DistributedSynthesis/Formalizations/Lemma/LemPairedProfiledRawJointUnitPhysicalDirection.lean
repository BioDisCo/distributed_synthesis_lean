/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedProvenancePolicy

/-!
# Physical block directions for the singleton raw-joint lineage

The recurrent construction is rooted with `I = Unit`.  This file embeds one
literal right or left physical block prefix into the proof-tree direction
alphabet.  The unused opposite-side fields are filled canonically; they are
never exposed to either process.

The small row-selection lemma isolates the only code-shape fact needed at a
physical close.  If the active row is related to itself and the equality
pattern is row-functional, materializing its pivot class selects exactly that
row.  Reachability of this reflexivity invariant is proved separately; it is
not silently assumed by the direction embedding.
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

/-! ## Canonical singleton physical directions -/

/-- Embed a concrete right-block row, prefix, and current input.  The left
half is dummy proof-tree data because `side = right`. -/
def profiledRawJointUnitRightActualDirection
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) where
  side := .right
  direction := {
    rightPivot := ((), row)
    rightTaggedPast := past.map fun move => (((), move.1), move.2)
    rightInput := input
    leftPivot := ((), .first)
    leftTaggedPast := []
    leftInput := (default, default) }

/-- Left-block mirror. -/
def profiledRawJointUnitLeftActualDirection
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) where
  side := .left
  direction := {
    rightPivot := ((), .first)
    rightTaggedPast := []
    rightInput := (default, default)
    leftPivot := ((), row)
    leftTaggedPast := past.map fun move => (((), move.1), move.2)
    leftInput := input }

section
omit [Fintype In₁] [Fintype In₂]

@[simp] theorem profiledRawJointUnitRightActualDirection_side
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).side = .right :=
  rfl

@[simp] theorem profiledRawJointUnitLeftActualDirection_side
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).side = .left :=
  rfl

@[simp] theorem profiledRawJointUnitRightActualDirection_pivot
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).direction.rightPivot =
      ((), row) :=
  rfl

@[simp] theorem profiledRawJointUnitLeftActualDirection_pivot
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).direction.leftPivot =
      ((), row) :=
  rfl

@[simp] theorem profiledRawJointUnitRightActualDirection_physicalPast
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).direction.rightPhysicalPast =
      past := by
  simp only [profiledRawJointUnitRightActualDirection,
    ProfiledRawJointFamilyDirection.rightPhysicalPast, List.map_map]
  induction past with
  | nil => rfl
  | cons move past ih => simp [ih]

@[simp] theorem profiledRawJointUnitLeftActualDirection_physicalPast
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).direction.leftPhysicalPast =
      past := by
  simp only [profiledRawJointUnitLeftActualDirection,
    ProfiledRawJointFamilyDirection.leftPhysicalPast, List.map_map]
  induction past with
  | nil => rfl
  | cons move past ih => simp [ih]

@[simp] theorem profiledRawJointUnitRightActualDirection_input
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).direction.rightInput =
      input :=
  rfl

@[simp] theorem profiledRawJointUnitLeftActualDirection_input
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input).direction.leftInput =
      input :=
  rfl

end

/-! ## Exact singleton pivot materialization -/

/-- In a row-functional singleton equality pattern, a reflexive active row
materializes as itself. -/
theorem profiledRawJointChildCodeOfPattern_unit_self
    {Root : Type*} (pattern : ProfiledRawJointEqualityPattern Unit)
    (root : ProfiledRawJointCandidate Unit → Root)
    (row : PairedEntryRow)
    (hfunctional : pattern.RowFunctionalAt ((), row))
    (hreflexive : pattern ((), row) ((), row) = true) :
    profiledRawJointChildCodeOfPattern pattern root ((), row) () =
      some (row, root ((), row)) := by
  cases row with
  | first =>
      simp [profiledRawJointChildCodeOfPattern, hreflexive]
  | both =>
      have hfirst : pattern ((), .first) ((), .both) = false := by
        cases hvalue : pattern ((), .first) ((), .both) with
        | false => rfl
        | true =>
            exact (hfunctional () ⟨hvalue, hreflexive⟩).elim
      simp [profiledRawJointChildCodeOfPattern, hfirst, hreflexive]

/-! ## Definitional one-sided target forms -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
@[simp] theorem profiledRawJointOneSidedNext_unitRight
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    profiledRawJointOneSidedNext A code move
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) =
      profiledRawJointRightActualIncidenceNext A code.family move
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input).direction :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
@[simp] theorem profiledRawJointOneSidedNext_unitLeft
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    profiledRawJointOneSidedNext A code move
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) =
      profiledRawJointLeftActualIncidenceNext A code.family move
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input).direction :=
  rfl

/-! ## The literal active slot at a physical close -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] [Fintype Out₂] [Fintype In₁]
    [Fintype In₂] in
/-- Under the reachable row-shape invariant, a concrete right close installs
exactly the slot computed by its selected raw lambda. -/
theorem profiledRawJointOneSidedNext_unitRight_leftSlot
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
    (profiledRawJointOneSidedNext A code move
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)).family.left () =
      some (profiledRawRightChildSlot A source lambda row past input) := by
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  change profiledRawOptionalChildSlots
      (profiledRawRightIndexedChildCode A code.family move actual.direction) () =
    some (profiledRawRightChildSlot A source lambda row past input)
  unfold profiledRawRightIndexedChildCode
  rw [show actual.direction.rightPivot = ((), row) by rfl]
  unfold profiledRawOptionalChildSlots
  rw [profiledRawJointChildCodeOfPattern_unit_self
    code.family.rightPattern
    (profiledRawRightCandidateChild A code.family move actual.direction)
    row hfunctional hreflexive]
  simp [profiledRawOptionalChildSlots, profiledRawRightCandidateChild,
    actual, hsource, hlambda]

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] [Fintype Out₂] [Fintype In₁]
    [Fintype In₂] in
/-- Left-close mirror. -/
theorem profiledRawJointOneSidedNext_unitLeft_rightSlot
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
    (profiledRawJointOneSidedNext A code move
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)).family.right () =
      some (profiledRawLeftChildSlot A source lambda row past input) := by
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  change profiledRawOptionalChildSlots
      (profiledRawLeftIndexedChildCode A code.family move actual.direction) () =
    some (profiledRawLeftChildSlot A source lambda row past input)
  unfold profiledRawLeftIndexedChildCode
  rw [show actual.direction.leftPivot = ((), row) by rfl]
  unfold profiledRawOptionalChildSlots
  rw [profiledRawJointChildCodeOfPattern_unit_self
    code.family.leftPattern
    (profiledRawLeftCandidateChild A code.family move actual.direction)
    row hfunctional hreflexive]
  simp [profiledRawOptionalChildSlots, profiledRawLeftCandidateChild,
    actual, hsource, hlambda]

end

end DetParityAutomaton

end DistributedSynthesis
