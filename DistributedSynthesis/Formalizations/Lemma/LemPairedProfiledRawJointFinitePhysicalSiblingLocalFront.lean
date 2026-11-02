/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointLeaderFreeControllerCarrier

/-!
# Local no-receive front of a finite sibling block

The finite sibling alphabet is proof-side data until it is installed in two
local controls.  This file performs the first literal installation step.  A
right sibling move gives process one a finite owner control; on `noRecv` that
control advances from process one's own input only.  The left mirror gives
the corresponding process-two field.

These functions have exactly the type of the `exceptionalNoRecvOne` and
`exceptionalNoRecvTwo` fields of `ProfiledRawJointLeaderFreeKernel` after the
displayed front types are substituted.  Neither function receives an
`EnvironmentRound`, graph, partner input, orientation, leader, or sibling
member.

The member-insensitivity theorems are stronger than equality of physical
outputs: after the common target relation has been materialized, the entire
narrowed controller is independent of the proof-side Boolean, so both the
emitted output and successor local control agree definitionally.

This module intentionally does not claim that an exact semantic move indexed
by a full input pair can already be selected by a process which has observed
only its own current input.  Coupling that finite family at installation is
the next front-carrier obligation.
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

/-! ## Right sibling: the process-one no-receive field -/

/-- The owner family below a finite right sibling key.  The fixed `false`
projection is not a semantic choice: both projections are definitionally the
same controller. -/
noncomputable abbrev ProfiledRawJointRightPhysicalSiblingOwner
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :=
  (move.memberController A false).Control

noncomputable instance
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    Fintype (ProfiledRawJointRightPhysicalSiblingOwner A move) := by
  classical
  infer_instance

/-- A finite exceptional front state with one already installed right move.
There is no member bit in this sigma. -/
noncomputable abbrev ProfiledRawJointRightPhysicalSiblingExceptional :=
  Sigma (ProfiledRawJointRightPhysicalSiblingOwner A)

noncomputable instance :
    Fintype (ProfiledRawJointRightPhysicalSiblingExceptional A) := by
  classical
  infer_instance

/-- Unused mirror family while displaying the exact process-one kernel
field.  Later front assembly replaces it by the genuine staged receiver. -/
abbrev ProfiledRawJointRightPhysicalSiblingDummyLeftReceiver
    (_move : ProfiledRawJointRightPhysicalSiblingMove A) := PUnit

/-- One member-parametric view of the owner step.  Its signature contains
only the installed finite control and process one's own input. -/
noncomputable def profiledRawJointRightPhysicalSiblingMemberNoRecvStep
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (member : Bool)
    (control : (move.memberController A member).Control)
    (input : In₁) :
    Out₁ × (move.memberController A member).Control :=
  let controller := move.memberController A member
  let label := controller.labelOf control
  (label.1 input, controller.step control input)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The complete local no-receive result is insensitive to the hidden
common/strict member. -/
theorem profiledRawJointRightPhysicalSiblingMemberNoRecvStep_eq
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool)
    (control : (move.memberController A left).Control)
    (input : In₁) :
    profiledRawJointRightPhysicalSiblingMemberNoRecvStep A move left control
        input =
      profiledRawJointRightPhysicalSiblingMemberNoRecvStep A move right
        control input :=
  rfl

/-- The concrete `exceptionalNoRecvOne` field below one installed right
sibling move.  It resolves the exceptional front to the ordinary right-owner
constructor using only the honest local `noRecv` event. -/
noncomputable def profiledRawJointRightPhysicalSiblingExceptionalNoRecvOne
    (state : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (input : In₁) :
    Out₁ ×
      ProfiledRawJointLeaderFreeOneControl PUnit
        (ProfiledRawJointRightPhysicalSiblingExceptional A)
        (ProfiledRawJointRightPhysicalSiblingMove A)
        (ProfiledRawJointRightPhysicalSiblingOwner A)
        (ProfiledRawJointRightPhysicalSiblingDummyLeftReceiver A) :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    state.1 false state.2 input
  (next.1, .rightOwner state.1 next.2)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact field equation, stated through an arbitrary proof-side member.  The
member disappears from both the physical output and successor owner control. -/
theorem profiledRawJointRightPhysicalSiblingExceptionalNoRecvOne_eq_member
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (member : Bool)
    (control : (move.memberController A member).Control)
    (input : In₁) :
    profiledRawJointRightPhysicalSiblingExceptionalNoRecvOne A
        ⟨move, control⟩ input =
      let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A move
        member control input
      (next.1,
        ProfiledRawJointLeaderFreeOneControl.rightOwner move next.2) :=
  rfl

/-! ## Left mirror: the process-two no-receive field -/

noncomputable abbrev ProfiledRawJointLeftPhysicalSiblingOwner
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :=
  (move.memberController A false).Control

noncomputable instance
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    Fintype (ProfiledRawJointLeftPhysicalSiblingOwner A move) := by
  classical
  infer_instance

noncomputable abbrev ProfiledRawJointLeftPhysicalSiblingExceptional :=
  Sigma (ProfiledRawJointLeftPhysicalSiblingOwner A)

noncomputable instance :
    Fintype (ProfiledRawJointLeftPhysicalSiblingExceptional A) := by
  classical
  infer_instance

abbrev ProfiledRawJointLeftPhysicalSiblingDummyRightReceiver
    (_move : ProfiledRawJointLeftPhysicalSiblingMove A) := PUnit

noncomputable def profiledRawJointLeftPhysicalSiblingMemberNoRecvStep
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (member : Bool)
    (control : (move.memberController A member).Control)
    (input : In₂) :
    Out₂ × (move.memberController A member).Control :=
  let controller := move.memberController A member
  let label := controller.labelOf control
  (label.1 input, controller.step control input)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingMemberNoRecvStep_eq
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool)
    (control : (move.memberController A left).Control)
    (input : In₂) :
    profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A move left control
        input =
      profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A move right
        control input :=
  rfl

/-- Concrete `exceptionalNoRecvTwo` mirror. -/
noncomputable def profiledRawJointLeftPhysicalSiblingExceptionalNoRecvTwo
    (state : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (input : In₂) :
    Out₂ ×
      ProfiledRawJointLeaderFreeTwoControl PUnit
        (ProfiledRawJointLeftPhysicalSiblingExceptional A)
        (ProfiledRawJointLeftPhysicalSiblingMove A)
        (ProfiledRawJointLeftPhysicalSiblingDummyRightReceiver A)
        (ProfiledRawJointLeftPhysicalSiblingOwner A) :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    state.1 false state.2 input
  (next.1, .leftOwner state.1 next.2)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingExceptionalNoRecvTwo_eq_member
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (member : Bool)
    (control : (move.memberController A member).Control)
    (input : In₂) :
    profiledRawJointLeftPhysicalSiblingExceptionalNoRecvTwo A
        ⟨move, control⟩ input =
      let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A move
        member control input
      (next.1,
        ProfiledRawJointLeaderFreeTwoControl.leftOwner move next.2) :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
