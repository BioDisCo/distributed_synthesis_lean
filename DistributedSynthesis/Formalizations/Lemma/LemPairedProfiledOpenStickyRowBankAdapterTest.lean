/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenStickyRowReceiptSplitTest
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiveActivation

/-!
# Fail-fast adapter from the local receiver bank to witnessed overlay rows

This file tests only the sticky-row seam.  The existing end-to-end local
controller stores a `PairedEntryRow` in every member of its receiver bank.
We install the witnessed overlay's row from that coordinate, retain the
connection under a same-direction step, and rebuild the connection with the
existing activation rows at a reversal.

The Boolean below is the already stored historical family-bank member.  It
is not the current orientation, graph, or a strict-leader test.  The hidden
dependent semantic member of the witnessed overlay is deliberately not
identified with it: physical member/root homogeneity handles that separate
coordinate once the receiver row is fixed.
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

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable (package : PairedInitialProfiledRationalPackage A)

/-! ## The literal adapter relation -/

/-- A right witnessed overlay reads its sticky row from one member of the
genuinely local process-two receiver bank. -/
def ProfiledOpenWitnessedRightRoundOverlay.UsesReceiverBankRow
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    {move : EndToEndRightFamilyPairMove A package}
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) : Prop :=
  overlay.entryRow = (bank member).1

/-- Process-one/left-family mirror. -/
def ProfiledOpenWitnessedLeftRoundOverlay.UsesReceiverBankRow
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    {move : EndToEndLeftFamilyPairMove A package}
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) : Prop :=
  overlay.entryRow = (bank member).1

/-- Install only the proof-side overlay row from the local right bank. -/
def ProfiledOpenWitnessedRightRoundOverlay.withReceiverBankRow
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    {move : EndToEndRightFamilyPairMove A package}
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode :=
  overlay.withEntryRow A initialCode (bank member).1

/-- Left mirror. -/
def ProfiledOpenWitnessedLeftRoundOverlay.withReceiverBankRow
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    {move : EndToEndLeftFamilyPairMove A package}
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode :=
  overlay.withEntryRow A initialCode (bank member).1

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem rightOverlay_withReceiverBankRow_uses
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    {move : EndToEndRightFamilyPairMove A package}
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) :
    (overlay.withReceiverBankRow A initialCode package bank member
      ).UsesReceiverBankRow A initialCode package bank member :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem leftOverlay_withReceiverBankRow_uses
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    {move : EndToEndLeftFamilyPairMove A package}
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) :
    (overlay.withReceiverBankRow A initialCode package bank member
      ).UsesReceiverBankRow A initialCode package bank member :=
  rfl

/-! ## Same-direction retention -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The overlay candidate step and the real local receiver-bank step retain
the same row coordinate. -/
theorem rightOverlay_usesReceiverBankRow_step
    (sender : EndToEndRightFamilyOneControl A package)
    (bank : EndToEndRightFamilyReceiverBank A package sender.1)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (member : Bool) (inputOne : In₁) (inputTwo : In₂)
    (hrow : overlay.UsesReceiverBankRow A initialCode package bank member) :
    (overlay.step A initialCode inputOne inputTwo).UsesReceiverBankRow A
      initialCode package
      (stepEndToEndRightFamilyReceiverBank A package sender bank
        (inputTwo, inputOne)) member := by
  change overlay.entryRow = (bank member).1
  exact hrow

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem leftOverlay_usesReceiverBankRow_step
    (sender : EndToEndLeftFamilyTwoControl A package)
    (bank : EndToEndLeftFamilyReceiverBank A package sender.1)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (member : Bool) (inputOne : In₁) (inputTwo : In₂)
    (hrow : overlay.UsesReceiverBankRow A initialCode package bank member) :
    (overlay.step A initialCode inputOne inputTwo).UsesReceiverBankRow A
      initialCode package
      (stepEndToEndLeftFamilyReceiverBank A package sender bank
        (inputOne, inputTwo)) member := by
  change overlay.entryRow = (bank member).1
  exact hrow

/-! ## Reversal activation and reinstallation -/

/-- Rebuild the process-two receiver bank when a staged right sender becomes
active.  The continued member keeps the dormant row and the fresh member is
installed from process two's own preceding-receipt bit. -/
noncomputable def reinstalledRightReceiverBank
    (pastAnchor : Bool)
    (oldMove : EndToEndRightFamilyPairMove A package)
    (oldBank : EndToEndRightFamilyReceiverBank A package oldMove)
    (newMove : EndToEndRightFamilyPairMove A package)
    (previouslyReceived : Bool) :
    EndToEndRightFamilyReceiverBank A package newMove :=
  initialEndToEndRightFamilyReceiverBank A package newMove
    (endToEndActivationNextRightFamilyRows A package pastAnchor oldMove
      oldBank previouslyReceived)

/-- Process-one mirror. -/
noncomputable def reinstalledLeftReceiverBank
    (pastAnchor : Bool)
    (oldMove : EndToEndLeftFamilyPairMove A package)
    (oldBank : EndToEndLeftFamilyReceiverBank A package oldMove)
    (newMove : EndToEndLeftFamilyPairMove A package)
    (previouslyReceived : Bool) :
    EndToEndLeftFamilyReceiverBank A package newMove :=
  initialEndToEndLeftFamilyReceiverBank A package newMove
    (endToEndActivationNextLeftFamilyRows A package pastAnchor oldMove oldBank
      previouslyReceived)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The continued right member literally retains its old local row. -/
@[simp] theorem reinstalledRightReceiverBank_false_row
    (pastAnchor : Bool)
    (oldMove : EndToEndRightFamilyPairMove A package)
    (oldBank : EndToEndRightFamilyReceiverBank A package oldMove)
    (newMove : EndToEndRightFamilyPairMove A package)
    (previouslyReceived : Bool) :
    (reinstalledRightReceiverBank A package pastAnchor oldMove oldBank newMove
      previouslyReceived false).1 = (oldBank pastAnchor).1 :=
  rfl

/-- The fresh right member is installed solely from the receiver's local
preceding-receipt event. -/
@[simp] theorem reinstalledRightReceiverBank_true_row
    (pastAnchor : Bool)
    (oldMove : EndToEndRightFamilyPairMove A package)
    (oldBank : EndToEndRightFamilyReceiverBank A package oldMove)
    (newMove : EndToEndRightFamilyPairMove A package)
    (previouslyReceived : Bool) :
    (reinstalledRightReceiverBank A package pastAnchor oldMove oldBank newMove
      previouslyReceived true).1 =
        guardedEntryRowOfReceived previouslyReceived :=
  rfl

@[simp] theorem reinstalledLeftReceiverBank_false_row
    (pastAnchor : Bool)
    (oldMove : EndToEndLeftFamilyPairMove A package)
    (oldBank : EndToEndLeftFamilyReceiverBank A package oldMove)
    (newMove : EndToEndLeftFamilyPairMove A package)
    (previouslyReceived : Bool) :
    (reinstalledLeftReceiverBank A package pastAnchor oldMove oldBank newMove
      previouslyReceived false).1 = (oldBank (!pastAnchor)).1 :=
  rfl

@[simp] theorem reinstalledLeftReceiverBank_true_row
    (pastAnchor : Bool)
    (oldMove : EndToEndLeftFamilyPairMove A package)
    (oldBank : EndToEndLeftFamilyReceiverBank A package oldMove)
    (newMove : EndToEndLeftFamilyPairMove A package)
    (previouslyReceived : Bool) :
    (reinstalledLeftReceiverBank A package pastAnchor oldMove oldBank newMove
      previouslyReceived true).1 =
        guardedEntryRowOfReceived previouslyReceived :=
  rfl

/-- Installing the right overlay from the rebuilt local bank closes the
adapter relation for either member. -/
theorem rightOverlay_reinstall_usesReceiverBankRow
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (pastAnchor : Bool)
    (oldMove : EndToEndRightFamilyPairMove A package)
    (oldBank : EndToEndRightFamilyReceiverBank A package oldMove)
    (newMove : EndToEndRightFamilyPairMove A package)
    (previouslyReceived member : Bool) :
    let bank := reinstalledRightReceiverBank A package pastAnchor oldMove
      oldBank newMove previouslyReceived
    (overlay.withReceiverBankRow A initialCode package bank member
      ).UsesReceiverBankRow A initialCode package bank member := by
  exact rightOverlay_withReceiverBankRow_uses A initialCode package overlay
    _ member

/-- Left mirror. -/
theorem leftOverlay_reinstall_usesReceiverBankRow
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (pastAnchor : Bool)
    (oldMove : EndToEndLeftFamilyPairMove A package)
    (oldBank : EndToEndLeftFamilyReceiverBank A package oldMove)
    (newMove : EndToEndLeftFamilyPairMove A package)
    (previouslyReceived member : Bool) :
    let bank := reinstalledLeftReceiverBank A package pastAnchor oldMove
      oldBank newMove previouslyReceived
    (overlay.withReceiverBankRow A initialCode package bank member
      ).UsesReceiverBankRow A initialCode package bank member := by
  exact leftOverlay_withReceiverBankRow_uses A initialCode package overlay
    _ member

end

/-! ## The physical output now reads the local bank coordinate -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- After adaptation, the right physical receiver literally evaluates the
row stored in process two's local bank. -/
theorem rightReceiverOutput_withReceiverBankRow
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    {move : EndToEndRightFamilyPairMove A package}
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightReceiverOutput A initialCode
        (overlay.withReceiverBankRow A initialCode package bank member)
        inputOne inputTwo =
      pairedRightInformedForRow (bank member).1
        (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
          inputTwo).2.1.1.physical :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left physical receiver mirror. -/
theorem leftReceiverOutput_withReceiverBankRow
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    {move : EndToEndLeftFamilyPairMove A package}
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftReceiverOutput A initialCode
        (overlay.withReceiverBankRow A initialCode package bank member)
        inputOne inputTwo =
      pairedLeftInformedForRow (bank member).1
        (profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
          inputTwo).2.1.1.physical :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
