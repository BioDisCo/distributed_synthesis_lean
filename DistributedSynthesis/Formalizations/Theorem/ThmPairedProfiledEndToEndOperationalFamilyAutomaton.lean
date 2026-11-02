/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyCarrier
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# Executable local-summary interface for the end-to-end family carrier

This is the first actual operational wrapper around the simultaneous
root-family tables.  Process one stores one right-family overlay and process
two stores one left-family overlay.  The post control has no constructor or
field for a current orientation, selected family member, overlap anchor, or
strict leader.

The local no-receive transitions are complete and executable.  The receive
table is an explicit finite interface parameter: constructing that table from
the semantic family handoff is the next installation theorem, but it cannot
affect how a blind process steps.  Thus the dangerous alternating transitions
already reduce definitionally to the family-carrier equations proved in
`ThmPairedProfiledEndToEndOperationalFamilyCarrier`.
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

/-! ## Proof-free local controls -/

/-- Process one's actual post control.  The wrapper makes explicit that the
shared right-family overlay, rather than a member projection, is stored. -/
structure EndToEndFamilyOperationalOneControl where
  shared : EndToEndRightFamilyOneControl A package

/-- Process-two mirror. -/
structure EndToEndFamilyOperationalTwoControl where
  shared : EndToEndLeftFamilyTwoControl A package

noncomputable instance : Fintype
    (EndToEndFamilyOperationalOneControl A package) := by
  classical
  exact Fintype.ofEquiv (EndToEndRightFamilyOneControl A package)
    { toFun := fun shared => ⟨shared⟩
      invFun := fun control => control.shared
      left_inv := by intro shared; rfl
      right_inv := by intro control; cases control; rfl }

noncomputable instance : Fintype
    (EndToEndFamilyOperationalTwoControl A package) := by
  classical
  exact Fintype.ofEquiv (EndToEndLeftFamilyTwoControl A package)
    { toFun := fun shared => ⟨shared⟩
      invFun := fun control => control.shared
      left_inv := by intro shared; rfl
      right_inv := by intro control; cases control; rfl }

/-- The output is retained in the local summary, as in the existing complete
operational automaton. -/
abbrev EndToEndFamilyOperationalOneSummary :=
  EndToEndFamilyOperationalOneControl A package × Out₁

/-- Process-two mirror. -/
abbrev EndToEndFamilyOperationalTwoSummary :=
  EndToEndFamilyOperationalTwoControl A package × Out₂

noncomputable instance : Fintype
    (EndToEndFamilyOperationalOneSummary A package) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndFamilyOperationalTwoSummary A package) := by
  classical
  infer_instance

/-- Enter a right family at the shared initial table state. -/
def initialEndToEndFamilyOperationalOneControl
    (move : EndToEndRightFamilyPairMove A package) :
    EndToEndFamilyOperationalOneControl A package :=
  ⟨EndToEndRightFamilyPairOverlay.initial A package move⟩

/-- Left-oriented mirror. -/
def initialEndToEndFamilyOperationalTwoControl
    (move : EndToEndLeftFamilyPairMove A package) :
    EndToEndFamilyOperationalTwoControl A package :=
  ⟨EndToEndLeftFamilyPairOverlay.initial A package move⟩

/-! ## Executable no-receive transitions -/

/-- Process one's post transition reads only its own shared overlay and input. -/
def endToEndFamilyOperationalNoRecvOne
    (control : EndToEndFamilyOperationalOneControl A package) (input : In₁) :
    Out₁ × EndToEndFamilyOperationalOneControl A package :=
  let next := endToEndRightFamilyNoRecvOne A package control.shared input
  (next.1, ⟨next.2⟩)

/-- Process-two mirror. -/
def endToEndFamilyOperationalNoRecvTwo
    (control : EndToEndFamilyOperationalTwoControl A package) (input : In₂) :
    Out₂ × EndToEndFamilyOperationalTwoControl A package :=
  let next := endToEndLeftFamilyNoRecvTwo A package control.shared input
  (next.1, ⟨next.2⟩)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyOperationalNoRecvOne_shared
    (control : EndToEndFamilyOperationalOneControl A package) (input : In₁) :
    (endToEndFamilyOperationalNoRecvOne A package control input).2.shared =
      (endToEndRightFamilyNoRecvOne A package control.shared input).2 :=
  rfl

@[simp] theorem endToEndFamilyOperationalNoRecvTwo_shared
    (control : EndToEndFamilyOperationalTwoControl A package) (input : In₂) :
    (endToEndFamilyOperationalNoRecvTwo A package control input).2.shared =
      (endToEndLeftFamilyNoRecvTwo A package control.shared input).2 :=
  rfl

@[simp] theorem endToEndFamilyOperationalNoRecvOne_output
    (control : EndToEndFamilyOperationalOneControl A package) (input : In₁) :
    (endToEndFamilyOperationalNoRecvOne A package control input).1 =
      (endToEndRightFamilyNoRecvOne A package control.shared input).1 :=
  rfl

@[simp] theorem endToEndFamilyOperationalNoRecvTwo_output
    (control : EndToEndFamilyOperationalTwoControl A package) (input : In₂) :
    (endToEndFamilyOperationalNoRecvTwo A package control input).1 =
      (endToEndLeftFamilyNoRecvTwo A package control.shared input).1 :=
  rfl

end

/-- Local-summary ordering: the new control precedes the output. -/
def endToEndFamilyOperationalStepNoRecvOne
    (summary : EndToEndFamilyOperationalOneSummary A package) (input : In₁) :
    EndToEndFamilyOperationalOneSummary A package :=
  let next := endToEndFamilyOperationalNoRecvOne A package summary.1 input
  (next.2, next.1)

/-- Process-two mirror. -/
def endToEndFamilyOperationalStepNoRecvTwo
    (summary : EndToEndFamilyOperationalTwoSummary A package) (input : In₂) :
    EndToEndFamilyOperationalTwoSummary A package :=
  let next := endToEndFamilyOperationalNoRecvTwo A package summary.1 input
  (next.2, next.1)

/-! ## Receive-table boundary and a genuine local-summary automaton -/

/-- Receive tables specifying how a receiver installs the next
pair of shared family tables.  This interface contains only finite local
summaries and inputs; it has no proof witness or hidden member argument. -/
structure EndToEndFamilyOperationalReceiveTable where
  recvOne : EndToEndFamilyOperationalOneSummary A package → In₁ →
    EndToEndFamilyOperationalTwoSummary A package → In₂ →
      EndToEndFamilyOperationalOneSummary A package
  recvTwo : EndToEndFamilyOperationalTwoSummary A package → In₂ →
    EndToEndFamilyOperationalOneSummary A package → In₁ →
      EndToEndFamilyOperationalTwoSummary A package

/-- The family post carrier as an actual `LocalSummaryAutomaton`.  Correctly
typed view increments use the executable family transitions.  Ill-typed
`PSum` branches stutter and are unreachable for genuine views. -/
def endToEndFamilyOperationalSummaryAutomaton
    (initialOne : EndToEndFamilyOperationalOneSummary A package)
    (initialTwo : EndToEndFamilyOperationalTwoSummary A package)
    (receive : EndToEndFamilyOperationalReceiveTable A package) :
    LocalSummaryAutomaton In₁ In₂ where
  Summary
    | .one => EndToEndFamilyOperationalOneSummary A package
    | .two => EndToEndFamilyOperationalTwoSummary A package
  finite
    | .one => inferInstance
    | .two => inferInstance
  initial
    | .one => initialOne
    | .two => initialTwo
  stepNoRecv
    | .one, summary, .inl input =>
        endToEndFamilyOperationalStepNoRecvOne A package summary input
    | .two, summary, .inr input =>
        endToEndFamilyOperationalStepNoRecvTwo A package summary input
    | _, summary, _ => summary
  stepRecv
    | .one, self, .inl inputOne, other, .inr inputTwo =>
        receive.recvOne self inputOne other inputTwo
    | .two, self, .inr inputTwo, other, .inl inputOne =>
        receive.recvTwo self inputTwo other inputOne
    | _, self, _, _, _ => self

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndFamilyOperationalSummaryAutomaton_stepNoRecv_one
    (initialOne : EndToEndFamilyOperationalOneSummary A package)
    (initialTwo : EndToEndFamilyOperationalTwoSummary A package)
    (receive : EndToEndFamilyOperationalReceiveTable A package)
    (summary : EndToEndFamilyOperationalOneSummary A package) (input : In₁) :
    (endToEndFamilyOperationalSummaryAutomaton A package initialOne initialTwo
      receive).stepNoRecv .one summary (.inl input) =
        endToEndFamilyOperationalStepNoRecvOne A package summary input :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndFamilyOperationalSummaryAutomaton_stepNoRecv_two
    (initialOne : EndToEndFamilyOperationalOneSummary A package)
    (initialTwo : EndToEndFamilyOperationalTwoSummary A package)
    (receive : EndToEndFamilyOperationalReceiveTable A package)
    (summary : EndToEndFamilyOperationalTwoSummary A package) (input : In₂) :
    (endToEndFamilyOperationalSummaryAutomaton A package initialOne initialTwo
      receive).stepNoRecv .two summary (.inr input) =
        endToEndFamilyOperationalStepNoRecvTwo A package summary input :=
  rfl

/-! ## Reduction of the two dangerous alternating cases -/

/-- The operational process-one transition used in
`.mixedLeft false → .right` is exactly the underlying shared-family step. -/
theorem endToEndFamilyOperationalCrossAnchorOne
    (candidates : EndToEndBothCandidates A package)
    (move : In₁ × In₂)
    (control : EndToEndFamilyOperationalOneControl A package)
    (currentMember targetMember : Bool)
    (project : control.shared.MemberControl A package →
      Option (EndToEndPhaseOneControl A package))
    (hcurrent : control.shared.RepresentsStep A package currentMember move.1
      project
      (endToEndPostNoRecvOne A package candidates.right.oneControl move.1))
    (htarget : control.shared.RepresentsStep A package targetMember move.1
      project
      (((candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).2.map fun phase => phase.oneControl))) :
    endToEndPostNoRecvOne A package candidates.right.oneControl move.1 =
      ((candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).2.map fun phase => phase.oneControl) := by
  exact endToEndCrossAnchorOne_of_familyCarrier A package candidates move
    control.shared currentMember targetMember project hcurrent htarget

/-- The operational process-two transition used in
`.mixedRight true → .left` is the left-family mirror. -/
theorem endToEndFamilyOperationalCrossAnchorTwo
    (candidates : EndToEndBothCandidates A package)
    (move : In₁ × In₂)
    (control : EndToEndFamilyOperationalTwoControl A package)
    (currentMember targetMember : Bool)
    (project : control.shared.MemberControl A package →
      Option (EndToEndPhaseTwoControl A package))
    (hcurrent : control.shared.RepresentsStep A package currentMember move.2
      project
      (endToEndPostNoRecvTwo A package candidates.left.twoControl move.2))
    (htarget : control.shared.RepresentsStep A package targetMember move.2
      project
      (((candidates.right.reverseRightToLeft A package move false).1.2,
        (candidates.right.reverseRightToLeft A package move false).2.map
          fun phase => phase.twoControl))) :
    endToEndPostNoRecvTwo A package candidates.left.twoControl move.2 =
      ((candidates.right.reverseRightToLeft A package move false).1.2,
        (candidates.right.reverseRightToLeft A package move false).2.map
          fun phase => phase.twoControl) := by
  exact endToEndCrossAnchorTwo_of_familyCarrier A package candidates move
    control.shared currentMember targetMember project hcurrent htarget

end

end DetParityAutomaton

end DistributedSynthesis
