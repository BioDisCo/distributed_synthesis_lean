/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiverBankStep
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFullFamilyAutomaton

/-!
# Total receiver-bank synchronization for the full family carrier

At a receive, the receiver can compare the family move stored with its dormant
bank against the family move delivered by the partner's sender overlay.  On an
equality it transports the dependent bank and advances both members using the
stored past-overlap anchor.  An inequality is totalized by leaving the local
summary unchanged; the semantic invariant will rule out that branch on
represented plays.

The synchronization does not refresh either process's own sender family.  It
also has no graph, current-orientation, family-member, or strict-leader input.
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

/-! ## Dependent bank transport -/

/-- Transport a left receiver bank along equality of its stored family move. -/
def castEndToEndLeftFamilyReceiverBank
    {source target : EndToEndLeftFamilyPairMove A package}
    (hmove : source = target)
    (bank : EndToEndLeftFamilyReceiverBank A package source) :
    EndToEndLeftFamilyReceiverBank A package target :=
  hmove ▸ bank

/-- Right-family mirror. -/
def castEndToEndRightFamilyReceiverBank
    {source target : EndToEndRightFamilyPairMove A package}
    (hmove : source = target)
    (bank : EndToEndRightFamilyReceiverBank A package source) :
    EndToEndRightFamilyReceiverBank A package target :=
  hmove ▸ bank

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem castEndToEndLeftFamilyReceiverBank_rfl
    {move : EndToEndLeftFamilyPairMove A package}
    (bank : EndToEndLeftFamilyReceiverBank A package move) :
    castEndToEndLeftFamilyReceiverBank A package rfl bank = bank :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem castEndToEndRightFamilyReceiverBank_rfl
    {move : EndToEndRightFamilyPairMove A package}
    (bank : EndToEndRightFamilyReceiverBank A package move) :
    castEndToEndRightFamilyReceiverBank A package rfl bank = bank :=
  rfl

/-! ## Process-one synchronization against the delivered left sender -/

/-- The matched process-one receive branch.  `hmove` is only a dependent cast:
the executable choice is still equality of two finite stored moves. -/
noncomputable def endToEndFamilyFullRecvOneBankSyncMatched
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1) :
    EndToEndFamilyFullOneSummary A package :=
  let bank := castEndToEndLeftFamilyReceiverBank A package hmove
    self.1.leftReceiver.2.2
  let next := stepEndToEndLeftFamilyReceiverBankFor A package
    other.1.leftSender bank self.1.leftReceiver.1 (inputOne, inputTwo)
  (⟨self.1.rightSender,
      ⟨self.1.leftReceiver.1, ⟨other.1.leftSender.1, next.2⟩⟩⟩,
    next.1)

/-- Total process-one receive synchronization.  A move mismatch uses the
explicit no-op fallback. -/
noncomputable def endToEndFamilyFullRecvOneBankSync
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    EndToEndFamilyFullOneSummary A package := by
  classical
  if hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1 then
    exact endToEndFamilyFullRecvOneBankSyncMatched A package self inputOne other
      inputTwo hmove
  else
    exact self

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyFullRecvOneBankSync_of_move_eq
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1) :
    endToEndFamilyFullRecvOneBankSync A package self inputOne other inputTwo =
      endToEndFamilyFullRecvOneBankSyncMatched A package self inputOne other
        inputTwo hmove := by
  classical
  simp only [endToEndFamilyFullRecvOneBankSync, dif_pos hmove]

@[simp] theorem endToEndFamilyFullRecvOneBankSync_of_move_ne
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (hmove : self.1.leftReceiver.2.1 ≠ other.1.leftSender.1) :
    endToEndFamilyFullRecvOneBankSync A package self inputOne other inputTwo =
      self := by
  classical
  simp only [endToEndFamilyFullRecvOneBankSync, dif_neg hmove]

/-- In the equality branch, the emitted output is exactly the output selected
by the historical anchor from the simultaneous memberwise bank step. -/
@[simp] theorem endToEndFamilyFullRecvOneBankSync_output_of_move_eq
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1) :
    (endToEndFamilyFullRecvOneBankSync A package self inputOne other inputTwo).2 =
      (stepEndToEndLeftFamilyReceiverBankFor A package other.1.leftSender
        (castEndToEndLeftFamilyReceiverBank A package hmove
          self.1.leftReceiver.2.2)
        self.1.leftReceiver.1 (inputOne, inputTwo)).1 := by
  classical
  simp only [endToEndFamilyFullRecvOneBankSync_of_move_eq A package self inputOne
    other inputTwo hmove, endToEndFamilyFullRecvOneBankSyncMatched]

/-- In the equality branch, the complete stored receiver bundle contains
exactly the two-member successor bank returned by the executable bank step. -/
@[simp] theorem endToEndFamilyFullRecvOneBankSync_leftReceiver_of_move_eq
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1) :
    (endToEndFamilyFullRecvOneBankSync A package self inputOne other inputTwo).1.leftReceiver =
      ⟨self.1.leftReceiver.1,
        ⟨other.1.leftSender.1,
          (stepEndToEndLeftFamilyReceiverBankFor A package other.1.leftSender
            (castEndToEndLeftFamilyReceiverBank A package hmove
              self.1.leftReceiver.2.2)
            self.1.leftReceiver.1 (inputOne, inputTwo)).2⟩⟩ := by
  classical
  simp only [endToEndFamilyFullRecvOneBankSync_of_move_eq A package self inputOne
    other inputTwo hmove, endToEndFamilyFullRecvOneBankSyncMatched]

@[simp] theorem endToEndFamilyFullRecvOneBankSync_rightSender_of_move_eq
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1) :
    (endToEndFamilyFullRecvOneBankSync A package self inputOne other inputTwo).1.rightSender =
      self.1.rightSender := by
  classical
  simp only [endToEndFamilyFullRecvOneBankSync_of_move_eq A package self inputOne
    other inputTwo hmove, endToEndFamilyFullRecvOneBankSyncMatched]

end

/-! ## Process-two synchronization against the delivered right sender -/

noncomputable def endToEndFamilyFullRecvTwoBankSyncMatched
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1) :
    EndToEndFamilyFullTwoSummary A package :=
  let bank := castEndToEndRightFamilyReceiverBank A package hmove
    self.1.rightReceiver.2.2
  let next := stepEndToEndRightFamilyReceiverBankFor A package
    other.1.rightSender bank self.1.rightReceiver.1 (inputTwo, inputOne)
  (⟨⟨self.1.rightReceiver.1, ⟨other.1.rightSender.1, next.2⟩⟩,
      self.1.leftSender⟩,
    next.1)

/-- Total process-two mirror, with the same explicit no-op mismatch branch. -/
noncomputable def endToEndFamilyFullRecvTwoBankSync
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁) :
    EndToEndFamilyFullTwoSummary A package := by
  classical
  if hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1 then
    exact endToEndFamilyFullRecvTwoBankSyncMatched A package self inputTwo other
      inputOne hmove
  else
    exact self

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyFullRecvTwoBankSync_of_move_eq
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1) :
    endToEndFamilyFullRecvTwoBankSync A package self inputTwo other inputOne =
      endToEndFamilyFullRecvTwoBankSyncMatched A package self inputTwo other
        inputOne hmove := by
  classical
  simp only [endToEndFamilyFullRecvTwoBankSync, dif_pos hmove]

@[simp] theorem endToEndFamilyFullRecvTwoBankSync_of_move_ne
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (hmove : self.1.rightReceiver.2.1 ≠ other.1.rightSender.1) :
    endToEndFamilyFullRecvTwoBankSync A package self inputTwo other inputOne =
      self := by
  classical
  simp only [endToEndFamilyFullRecvTwoBankSync, dif_neg hmove]

@[simp] theorem endToEndFamilyFullRecvTwoBankSync_output_of_move_eq
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1) :
    (endToEndFamilyFullRecvTwoBankSync A package self inputTwo other inputOne).2 =
      (stepEndToEndRightFamilyReceiverBankFor A package other.1.rightSender
        (castEndToEndRightFamilyReceiverBank A package hmove
          self.1.rightReceiver.2.2)
        self.1.rightReceiver.1 (inputTwo, inputOne)).1 := by
  classical
  simp only [endToEndFamilyFullRecvTwoBankSync_of_move_eq A package self inputTwo
    other inputOne hmove, endToEndFamilyFullRecvTwoBankSyncMatched]

@[simp] theorem endToEndFamilyFullRecvTwoBankSync_rightReceiver_of_move_eq
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1) :
    (endToEndFamilyFullRecvTwoBankSync A package self inputTwo other inputOne).1.rightReceiver =
      ⟨self.1.rightReceiver.1,
        ⟨other.1.rightSender.1,
          (stepEndToEndRightFamilyReceiverBankFor A package other.1.rightSender
            (castEndToEndRightFamilyReceiverBank A package hmove
              self.1.rightReceiver.2.2)
            self.1.rightReceiver.1 (inputTwo, inputOne)).2⟩⟩ := by
  classical
  simp only [endToEndFamilyFullRecvTwoBankSync_of_move_eq A package self inputTwo
    other inputOne hmove, endToEndFamilyFullRecvTwoBankSyncMatched]

@[simp] theorem endToEndFamilyFullRecvTwoBankSync_leftSender_of_move_eq
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1) :
    (endToEndFamilyFullRecvTwoBankSync A package self inputTwo other inputOne).1.leftSender =
      self.1.leftSender := by
  classical
  simp only [endToEndFamilyFullRecvTwoBankSync_of_move_eq A package self inputTwo
    other inputOne hmove, endToEndFamilyFullRecvTwoBankSyncMatched]

end

end

end DetParityAutomaton

end DistributedSynthesis
