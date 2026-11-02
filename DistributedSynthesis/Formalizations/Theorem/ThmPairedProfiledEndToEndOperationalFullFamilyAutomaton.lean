/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiverBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyCarrier
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# Full sender/receiver family local-summary carrier

This wrapper combines the shared blind sender overlays with their dual
two-member receiver banks.  A process advances its sender overlay exactly
when it does not receive; its dormant receiver bank is unchanged.  Receive
steps are isolated in a finite table interface and will be filled by the
source-specific family receiver computation.

No control stores an actual family member, current orientation, graph value,
or strict-leader bit.
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

abbrev EndToEndFamilyFullOneSummary :=
  EndToEndFamilyFullOneControl A package × Out₁

abbrev EndToEndFamilyFullTwoSummary :=
  EndToEndFamilyFullTwoControl A package × Out₂

noncomputable instance : Fintype
    (EndToEndFamilyFullOneSummary A package) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndFamilyFullTwoSummary A package) := by
  classical
  infer_instance

/-! ## Blind local steps -/

/-- Process one advances only the shared right-family sender. -/
def endToEndFamilyFullNoRecvOne
    (control : EndToEndFamilyFullOneControl A package) (input : In₁) :
    Out₁ × EndToEndFamilyFullOneControl A package :=
  let next := endToEndRightFamilyNoRecvOne A package control.rightSender input
  (next.1, ⟨next.2, control.leftReceiver⟩)

/-- Process two advances only the shared left-family sender. -/
def endToEndFamilyFullNoRecvTwo
    (control : EndToEndFamilyFullTwoControl A package) (input : In₂) :
    Out₂ × EndToEndFamilyFullTwoControl A package :=
  let next := endToEndLeftFamilyNoRecvTwo A package control.leftSender input
  (next.1, ⟨control.rightReceiver, next.2⟩)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyFullNoRecvOne_rightSender
    (control : EndToEndFamilyFullOneControl A package) (input : In₁) :
    (endToEndFamilyFullNoRecvOne A package control input).2.rightSender =
      (endToEndRightFamilyNoRecvOne A package control.rightSender input).2 :=
  rfl

@[simp] theorem endToEndFamilyFullNoRecvOne_leftReceiver
    (control : EndToEndFamilyFullOneControl A package) (input : In₁) :
    (endToEndFamilyFullNoRecvOne A package control input).2.leftReceiver =
      control.leftReceiver :=
  rfl

@[simp] theorem endToEndFamilyFullNoRecvTwo_rightReceiver
    (control : EndToEndFamilyFullTwoControl A package) (input : In₂) :
    (endToEndFamilyFullNoRecvTwo A package control input).2.rightReceiver =
      control.rightReceiver :=
  rfl

@[simp] theorem endToEndFamilyFullNoRecvTwo_leftSender
    (control : EndToEndFamilyFullTwoControl A package) (input : In₂) :
    (endToEndFamilyFullNoRecvTwo A package control input).2.leftSender =
      (endToEndLeftFamilyNoRecvTwo A package control.leftSender input).2 :=
  rfl

@[simp] theorem endToEndFamilyFullNoRecvOne_output
    (control : EndToEndFamilyFullOneControl A package) (input : In₁) :
    (endToEndFamilyFullNoRecvOne A package control input).1 =
      (endToEndRightFamilyNoRecvOne A package control.rightSender input).1 :=
  rfl

@[simp] theorem endToEndFamilyFullNoRecvTwo_output
    (control : EndToEndFamilyFullTwoControl A package) (input : In₂) :
    (endToEndFamilyFullNoRecvTwo A package control input).1 =
      (endToEndLeftFamilyNoRecvTwo A package control.leftSender input).1 :=
  rfl

end

def endToEndFamilyFullStepNoRecvOne
    (summary : EndToEndFamilyFullOneSummary A package) (input : In₁) :
    EndToEndFamilyFullOneSummary A package :=
  let next := endToEndFamilyFullNoRecvOne A package summary.1 input
  (next.2, next.1)

def endToEndFamilyFullStepNoRecvTwo
    (summary : EndToEndFamilyFullTwoSummary A package) (input : In₂) :
    EndToEndFamilyFullTwoSummary A package :=
  let next := endToEndFamilyFullNoRecvTwo A package summary.1 input
  (next.2, next.1)

/-! ## Finite receive boundary -/

structure EndToEndFamilyFullReceiveTable where
  recvOne : EndToEndFamilyFullOneSummary A package → In₁ →
    EndToEndFamilyFullTwoSummary A package → In₂ →
      EndToEndFamilyFullOneSummary A package
  recvTwo : EndToEndFamilyFullTwoSummary A package → In₂ →
    EndToEndFamilyFullOneSummary A package → In₁ →
      EndToEndFamilyFullTwoSummary A package

/-- The complete family carrier as a genuine finite local-summary automaton. -/
def endToEndFamilyFullSummaryAutomaton
    (initialOne : EndToEndFamilyFullOneSummary A package)
    (initialTwo : EndToEndFamilyFullTwoSummary A package)
    (receive : EndToEndFamilyFullReceiveTable A package) :
    LocalSummaryAutomaton In₁ In₂ where
  Summary
    | .one => EndToEndFamilyFullOneSummary A package
    | .two => EndToEndFamilyFullTwoSummary A package
  finite
    | .one => inferInstance
    | .two => inferInstance
  initial
    | .one => initialOne
    | .two => initialTwo
  stepNoRecv
    | .one, summary, .inl input =>
        endToEndFamilyFullStepNoRecvOne A package summary input
    | .two, summary, .inr input =>
        endToEndFamilyFullStepNoRecvTwo A package summary input
    | _, summary, _ => summary
  stepRecv
    | .one, self, .inl inputOne, other, .inr inputTwo =>
        receive.recvOne self inputOne other inputTwo
    | .two, self, .inr inputTwo, other, .inl inputOne =>
        receive.recvTwo self inputTwo other inputOne
    | _, self, _, _, _ => self

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndFamilyFullSummaryAutomaton_stepNoRecv_one
    (initialOne : EndToEndFamilyFullOneSummary A package)
    (initialTwo : EndToEndFamilyFullTwoSummary A package)
    (receive : EndToEndFamilyFullReceiveTable A package)
    (summary : EndToEndFamilyFullOneSummary A package) (input : In₁) :
    (endToEndFamilyFullSummaryAutomaton A package initialOne initialTwo
      receive).stepNoRecv .one summary (.inl input) =
        endToEndFamilyFullStepNoRecvOne A package summary input :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndFamilyFullSummaryAutomaton_stepNoRecv_two
    (initialOne : EndToEndFamilyFullOneSummary A package)
    (initialTwo : EndToEndFamilyFullTwoSummary A package)
    (receive : EndToEndFamilyFullReceiveTable A package)
    (summary : EndToEndFamilyFullTwoSummary A package) (input : In₂) :
    (endToEndFamilyFullSummaryAutomaton A package initialOne initialTwo
      receive).stepNoRecv .two summary (.inr input) =
        endToEndFamilyFullStepNoRecvTwo A package summary input :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
