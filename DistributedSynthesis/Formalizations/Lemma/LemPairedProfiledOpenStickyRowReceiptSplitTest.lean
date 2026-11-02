/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryLocalHandoff

/-!
# Sticky-row split by the honest local receipt event

This companion to `LemPairedProfiledOpenStickyRowPairTest` checks the smallest
same-overlay pair.  The two states agree in every coordinate except the old
`PairedEntryRow`.

On the blind side both rows are retained and the emitted sender output is
definitionally row-independent.  On the informed side the row is the image
of that receiver's own stored preceding-receipt bit; equal local events force
equal rows.  No leader, orientation, or eventual-recovery test is used.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-- Replace only the row of a right overlay. -/
def ProfiledOpenWitnessedRightRoundOverlay.withEntryRow
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (row : PairedEntryRow) :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode :=
  { overlay with entryRow := row }

/-- Replace only the row of a left overlay. -/
def ProfiledOpenWitnessedLeftRoundOverlay.withEntryRow
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (row : PairedEntryRow) :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode :=
  { overlay with entryRow := row }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem rightOverlay_withEntryRow_entryRow
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (row : PairedEntryRow) :
    (overlay.withEntryRow A initialCode row).entryRow = row :=
  rfl

@[simp] theorem leftOverlay_withEntryRow_entryRow
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (row : PairedEntryRow) :
    (overlay.withEntryRow A initialCode row).entryRow = row :=
  rfl

/-- The hidden-row pair passes at process one's right-block sender for all
current inputs. -/
theorem profiledOpenWitnessedRightSenderOutput_hiddenRow_pair
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (leftRow rightRow : PairedEntryRow) (inputOne : In₁) :
    profiledOpenWitnessedRightSenderOutput A initialCode
        (overlay.withEntryRow A initialCode leftRow) inputOne =
      profiledOpenWitnessedRightSenderOutput A initialCode
        (overlay.withEntryRow A initialCode rightRow) inputOne :=
  rfl

/-- The left-block/process-two blind sender mirror. -/
theorem profiledOpenWitnessedLeftSenderOutput_hiddenRow_pair
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (leftRow rightRow : PairedEntryRow) (inputTwo : In₂) :
    profiledOpenWitnessedLeftSenderOutput A initialCode
        (overlay.withEntryRow A initialCode leftRow) inputTwo =
      profiledOpenWitnessedLeftSenderOutput A initialCode
        (overlay.withEntryRow A initialCode rightRow) inputTwo :=
  rfl

end

/-- Two receiver rows are compatible with one local state when both are the
image of the same locally stored preceding-receipt event. -/
def PairedEntryRowsReceiverCompatible
    (left right : PairedEntryRow) : Prop :=
  ∃ received : Bool,
    left = FirstEntryFinitePolicyFamilies.entryRowOfReceived received ∧
      right = FirstEntryFinitePolicyFamilies.entryRowOfReceived received

theorem pairedEntryRowsReceiverCompatible_eq
    {left right : PairedEntryRow}
    (hcompatible : PairedEntryRowsReceiverCompatible left right) :
    left = right := by
  rcases hcompatible with ⟨received, rfl, rfl⟩
  rfl

theorem pairedEntryRowsReceiverCompatible_iff_eq
    (left right : PairedEntryRow) :
    PairedEntryRowsReceiverCompatible left right ↔ left = right := by
  constructor
  · exact pairedEntryRowsReceiverCompatible_eq
  · intro hrow
    subst right
    rcases FirstEntryFinitePolicyFamilies.exists_received_eq_entryRow left with
      ⟨received, hreceived⟩
    exact ⟨received, hreceived.symm, hreceived.symm⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Compatible right receivers agree because their locally stored rows agree;
this is not a claim that `.first` and `.both` are interchangeable. -/
theorem profiledOpenWitnessedRightReceiverOutput_of_compatibleRows
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    {leftRow rightRow : PairedEntryRow}
    (hcompatible : PairedEntryRowsReceiverCompatible leftRow rightRow)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightReceiverOutput A initialCode
        (overlay.withEntryRow A initialCode leftRow) inputOne inputTwo =
      profiledOpenWitnessedRightReceiverOutput A initialCode
        (overlay.withEntryRow A initialCode rightRow) inputOne inputTwo := by
  rw [pairedEntryRowsReceiverCompatible_eq hcompatible]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Compatible left receivers agree. -/
theorem profiledOpenWitnessedLeftReceiverOutput_of_compatibleRows
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    {leftRow rightRow : PairedEntryRow}
    (hcompatible : PairedEntryRowsReceiverCompatible leftRow rightRow)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftReceiverOutput A initialCode
        (overlay.withEntryRow A initialCode leftRow) inputOne inputTwo =
      profiledOpenWitnessedLeftReceiverOutput A initialCode
        (overlay.withEntryRow A initialCode rightRow) inputOne inputTwo := by
  rw [pairedEntryRowsReceiverCompatible_eq hcompatible]

/-- A different-row pair cannot be a same-local-receipt receiver pair. -/
theorem not_receiverCompatible_of_entryRow_ne
    {left right : PairedEntryRow} (hne : left ≠ right) :
    ¬ PairedEntryRowsReceiverCompatible left right := by
  intro hcompatible
  exact hne (pairedEntryRowsReceiverCompatible_eq hcompatible)

end

end DetParityAutomaton

end DistributedSynthesis
