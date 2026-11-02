/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyOverlay
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalPostStep

/-!
# Local operational carrier for an end-to-end root family

The old post-seam carrier evolves one rational controller selected by the
proof-side anchor.  That is precisely the wrong representation during an
ambiguous alternating stretch: two possible anchors may have the same local
view, while independently rationalized controllers need not have the same
next finite state.

This file installs the simultaneous family overlay as the actual local state.
Process one stores a right-family overlay and process two stores a left-family
overlay.  Neither state stores the selected family member, an orientation, or
a strict-leader bit.  The member is used only in the correctness relation.

The final correspondence lemmas are the replacement for the two ad-hoc
`hcurrent`/`htarget` equations of the first fixed-family adapter.  Once the
proof invariant says that a concrete proof-side transition is represented by
one member projection of the carrier, its equality with that member's table
step is derived, and two represented concrete transitions are equal even when
their hidden members differ.
-/

namespace DistributedSynthesis

universe u v x y s z

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

/-! ## The two genuinely local finite carriers -/

/-- Process one's finite state during an ambiguous right-family stretch.
This is the shared table state, not a selected member controller. -/
abbrev EndToEndRightFamilyOneControl :=
  EndToEndRightFamilyPairOverlay A package

/-- Process two's left-oriented mirror. -/
abbrev EndToEndLeftFamilyTwoControl :=
  EndToEndLeftFamilyPairOverlay A package

noncomputable instance : Fintype (EndToEndRightFamilyOneControl A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndLeftFamilyTwoControl A package) := by
  classical
  infer_instance

/-- A proof-level pair of the two independent local family controls.  This
pair is useful as an overlap invariant; it is not shared runtime memory. -/
structure EndToEndFamilyOverlapControls where
  one : EndToEndRightFamilyOneControl A package
  two : EndToEndLeftFamilyTwoControl A package

noncomputable instance : Fintype (EndToEndFamilyOverlapControls A package) := by
  classical
  exact Fintype.ofEquiv
    (EndToEndRightFamilyOneControl A package ×
      EndToEndLeftFamilyTwoControl A package)
    { toFun := fun pair => ⟨pair.1, pair.2⟩
      invFun := fun controls => (controls.one, controls.two)
      left_inv := by intro pair; cases pair; rfl
      right_inv := by intro controls; cases controls; rfl }

/-! ## Executable blind steps -/

/-- Process one's strict local step is read from the simultaneous right-family
table itself.  No hidden member is selected to compute either component. -/
def endToEndRightFamilyNoRecvOne
    (state : EndToEndRightFamilyOneControl A package) (input : In₁) :
    Out₁ × EndToEndRightFamilyOneControl A package :=
  (state.2.output
      (endToEndRightFamilyRootMonitors A package state.1.1)
      state.1.2.toTransitionRationalTree input,
    state.step A package input)

/-- Process-two mirror. -/
def endToEndLeftFamilyNoRecvTwo
    (state : EndToEndLeftFamilyTwoControl A package) (input : In₂) :
    Out₂ × EndToEndLeftFamilyTwoControl A package :=
  (state.2.output
      (endToEndLeftFamilyRootMonitors A package state.1.1)
      state.1.2.toTransitionRationalTree input,
    state.step A package input)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndRightFamilyNoRecvOne_fst
    (state : EndToEndRightFamilyOneControl A package) (input : In₁) :
    (endToEndRightFamilyNoRecvOne A package state input).1 =
      state.2.output
        (endToEndRightFamilyRootMonitors A package state.1.1)
        state.1.2.toTransitionRationalTree input :=
  rfl

@[simp] theorem endToEndRightFamilyNoRecvOne_snd
    (state : EndToEndRightFamilyOneControl A package) (input : In₁) :
    (endToEndRightFamilyNoRecvOne A package state input).2 =
      state.step A package input :=
  rfl

@[simp] theorem endToEndLeftFamilyNoRecvTwo_fst
    (state : EndToEndLeftFamilyTwoControl A package) (input : In₂) :
    (endToEndLeftFamilyNoRecvTwo A package state input).1 =
      state.2.output
        (endToEndLeftFamilyRootMonitors A package state.1.1)
        state.1.2.toTransitionRationalTree input :=
  rfl

@[simp] theorem endToEndLeftFamilyNoRecvTwo_snd
    (state : EndToEndLeftFamilyTwoControl A package) (input : In₂) :
    (endToEndLeftFamilyNoRecvTwo A package state input).2 =
      state.step A package input :=
  rfl

end

/-! ## Bidirectional overlap product -/

/-- Advance only process one's local component of the proof-level overlap
pair.  The other component is unchanged because no shared state is being
mutated. -/
def EndToEndFamilyOverlapControls.stepOne
    (controls : EndToEndFamilyOverlapControls A package) (input : In₁) :
    Out₁ × EndToEndFamilyOverlapControls A package :=
  let next := endToEndRightFamilyNoRecvOne A package controls.one input
  (next.1, ⟨next.2, controls.two⟩)

/-- Process-two mirror. -/
def EndToEndFamilyOverlapControls.stepTwo
    (controls : EndToEndFamilyOverlapControls A package) (input : In₂) :
    Out₂ × EndToEndFamilyOverlapControls A package :=
  let next := endToEndLeftFamilyNoRecvTwo A package controls.two input
  (next.1, ⟨controls.one, next.2⟩)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem EndToEndFamilyOverlapControls.stepOne_one
    (controls : EndToEndFamilyOverlapControls A package) (input : In₁) :
    (controls.stepOne A package input).2.one =
      (endToEndRightFamilyNoRecvOne A package controls.one input).2 :=
  rfl

@[simp] theorem EndToEndFamilyOverlapControls.stepOne_two
    (controls : EndToEndFamilyOverlapControls A package) (input : In₁) :
    (controls.stepOne A package input).2.two = controls.two :=
  rfl

@[simp] theorem EndToEndFamilyOverlapControls.stepTwo_one
    (controls : EndToEndFamilyOverlapControls A package) (input : In₂) :
    (controls.stepTwo A package input).2.one = controls.one :=
  rfl

@[simp] theorem EndToEndFamilyOverlapControls.stepTwo_two
    (controls : EndToEndFamilyOverlapControls A package) (input : In₂) :
    (controls.stepTwo A package input).2.two =
      (endToEndLeftFamilyNoRecvTwo A package controls.two input).2 :=
  rfl

end

/-! ## Proof-only member projections -/

/-- Project the successor shared state to any hidden right member. -/
def endToEndRightFamilyNextMemberControl
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (input : In₁) : state.MemberControl A package :=
  let next := (endToEndRightFamilyNoRecvOne A package state input).2
  next.2.memberControl
    (endToEndRightFamilyRootMonitors A package next.1.1)
    next.1.2.toTransitionRationalTree member

/-- Left-oriented mirror. -/
def endToEndLeftFamilyNextMemberControl
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (input : In₂) : state.MemberControl A package :=
  let next := (endToEndLeftFamilyNoRecvTwo A package state input).2
  next.2.memberControl
    (endToEndLeftFamilyRootMonitors A package next.1.1)
    next.1.2.toTransitionRationalTree member

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The actual right-family local transition is exactly every member
projection: both its output and its next finite control agree. -/
theorem endToEndRightFamilyNoRecvOne_member
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (input : In₁) :
    ((endToEndRightFamilyNoRecvOne A package state input).1,
        endToEndRightFamilyNextMemberControl A package state member input) =
      state.memberStep A package member input := by
  rfl

/-- Process-two mirror. -/
theorem endToEndLeftFamilyNoRecvTwo_member
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (input : In₂) :
    ((endToEndLeftFamilyNoRecvTwo A package state input).1,
        endToEndLeftFamilyNextMemberControl A package state member input) =
      state.memberStep A package member input := by
  rfl

/-- Project the next right member control through arbitrary proof-side data. -/
theorem endToEndRightFamilyNoRecvOne_project
    {Aux : Type z}
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (input : In₁) (project : state.MemberControl A package → Aux) :
    ((endToEndRightFamilyNoRecvOne A package state input).1,
        project (endToEndRightFamilyNextMemberControl A package state member
          input)) =
      let step := state.memberStep A package member input
      (step.1, project step.2) := by
  exact congrArg (fun step => (step.1, project step.2))
    (endToEndRightFamilyNoRecvOne_member A package state member input)

/-- Left-oriented mirror. -/
theorem endToEndLeftFamilyNoRecvTwo_project
    {Aux : Type z}
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (input : In₂) (project : state.MemberControl A package → Aux) :
    ((endToEndLeftFamilyNoRecvTwo A package state input).1,
        project (endToEndLeftFamilyNextMemberControl A package state member
          input)) =
      let step := state.memberStep A package member input
      (step.1, project step.2) := by
  exact congrArg (fun step => (step.1, project step.2))
    (endToEndLeftFamilyNoRecvTwo_member A package state member input)

end

/-! ## The representation invariant consumed at the seam -/

/-- A concrete proof-side right transition is represented by a hidden member
when it is the projection of the actual shared carrier step. -/
def EndToEndRightFamilyOneControl.RepresentsStep
    {Aux : Type z}
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (input : In₁) (project : state.MemberControl A package → Aux)
    (concrete : Out₁ × Aux) : Prop :=
  concrete =
    ((endToEndRightFamilyNoRecvOne A package state input).1,
      project (endToEndRightFamilyNextMemberControl A package state member
        input))

/-- Left-oriented mirror. -/
def EndToEndLeftFamilyTwoControl.RepresentsStep
    {Aux : Type z}
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (input : In₂) (project : state.MemberControl A package → Aux)
    (concrete : Out₂ × Aux) : Prop :=
  concrete =
    ((endToEndLeftFamilyNoRecvTwo A package state input).1,
      project (endToEndLeftFamilyNextMemberControl A package state member
        input))

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- A right representation supplies the exact fixed-family adapter equation. -/
theorem EndToEndRightFamilyOneControl.RepresentsStep.to_memberStep
    {Aux : Type z}
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (input : In₁) (project : state.MemberControl A package → Aux)
    (concrete : Out₁ × Aux)
    (hrep : state.RepresentsStep A package member input project concrete) :
    concrete =
      let step := state.memberStep A package member input
      (step.1, project step.2) := by
  exact hrep.trans
    (endToEndRightFamilyNoRecvOne_project A package state member input project)

/-- Left-oriented mirror. -/
theorem EndToEndLeftFamilyTwoControl.RepresentsStep.to_memberStep
    {Aux : Type z}
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (input : In₂) (project : state.MemberControl A package → Aux)
    (concrete : Out₂ × Aux)
    (hrep : state.RepresentsStep A package member input project concrete) :
    concrete =
      let step := state.memberStep A package member input
      (step.1, project step.2) := by
  exact hrep.trans
    (endToEndLeftFamilyNoRecvTwo_project A package state member input project)

/-- Two right transitions represented by the same shared carrier agree,
although the correctness proof may attach different hidden members to them. -/
theorem EndToEndRightFamilyOneControl.eq_of_representsStep
    {Aux : Type z}
    (state : EndToEndRightFamilyOneControl A package)
    (leftMember rightMember : Bool) (input : In₁)
    (project : state.MemberControl A package → Aux)
    (left right : Out₁ × Aux)
    (hleft : state.RepresentsStep A package leftMember input project left)
    (hright : state.RepresentsStep A package rightMember input project right) :
    left = right := by
  rw [hleft, hright]
  rfl

/-- Left-oriented mirror. -/
theorem EndToEndLeftFamilyTwoControl.eq_of_representsStep
    {Aux : Type z}
    (state : EndToEndLeftFamilyTwoControl A package)
    (leftMember rightMember : Bool) (input : In₂)
    (project : state.MemberControl A package → Aux)
    (left right : Out₂ × Aux)
    (hleft : state.RepresentsStep A package leftMember input project left)
    (hright : state.RepresentsStep A package rightMember input project right) :
    left = right := by
  rw [hleft, hright]
  rfl

end

/-! ## Exact alternating-seam adapters

These adapters establish the two equations `hcurrent` and `htarget`.
Here the invariant only states that each proof-side transition is represented
by the actual shared carrier.  Equality is then forced even if its two hidden
member witnesses differ. -/

/-- The `.mixedLeft false → .right` cross-anchor equation follows from two
member correspondences with the same process-one family carrier. -/
theorem endToEndCrossAnchorOne_of_familyCarrier
    (candidates : EndToEndBothCandidates A package)
    (move : In₁ × In₂)
    (state : EndToEndRightFamilyOneControl A package)
    (currentMember targetMember : Bool)
    (project : state.MemberControl A package →
      Option (EndToEndPhaseOneControl A package))
    (hcurrent : state.RepresentsStep A package currentMember move.1 project
      (endToEndPostNoRecvOne A package candidates.right.oneControl move.1))
    (htarget : state.RepresentsStep A package targetMember move.1 project
      (((candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).2.map fun phase => phase.oneControl))) :
    endToEndPostNoRecvOne A package candidates.right.oneControl move.1 =
      ((candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).1.1,
        (candidates.left.reverseLeftToRight A package
          (move.2, move.1) false).2.map fun phase => phase.oneControl) := by
  exact state.eq_of_representsStep A package currentMember targetMember move.1
    project _ _ hcurrent htarget

/-- The `.mixedRight true → .left` process-two mirror. -/
theorem endToEndCrossAnchorTwo_of_familyCarrier
    (candidates : EndToEndBothCandidates A package)
    (move : In₁ × In₂)
    (state : EndToEndLeftFamilyTwoControl A package)
    (currentMember targetMember : Bool)
    (project : state.MemberControl A package →
      Option (EndToEndPhaseTwoControl A package))
    (hcurrent : state.RepresentsStep A package currentMember move.2 project
      (endToEndPostNoRecvTwo A package candidates.left.twoControl move.2))
    (htarget : state.RepresentsStep A package targetMember move.2 project
      (((candidates.right.reverseRightToLeft A package move false).1.2,
        (candidates.right.reverseRightToLeft A package move false).2.map
          fun phase => phase.twoControl))) :
    endToEndPostNoRecvTwo A package candidates.left.twoControl move.2 =
      ((candidates.right.reverseRightToLeft A package move false).1.2,
        (candidates.right.reverseRightToLeft A package move false).2.map
          fun phase => phase.twoControl) := by
  exact state.eq_of_representsStep A package currentMember targetMember move.2
    project _ _ hcurrent htarget

end

end DetParityAutomaton

end DistributedSynthesis
