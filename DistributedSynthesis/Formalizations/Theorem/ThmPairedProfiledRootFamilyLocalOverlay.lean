/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootFamilyHandoff

/-!
# Local finite state of a simultaneous root-family controller

The two difficult alternating seams need more than equality of the output at
the root.  The blind process must use the same finite transition state under
both hidden proof anchors, so that equality is preserved after every further
blind round.

`FiniteRootFamilyLocalOverlay` is the minimal such state.  It consists of the
control of the one simultaneous family table and the existing root-selection
flag of `finiteRootMemberController`.  The hidden family index is deliberately
absent.  It is used only when the receiver component of the table is read.

The final `localStep_eq` theorem is the operational pair-test interface: both
the emitted blind output and the next local control are independent of the
hidden anchor.  The profiled right/left wrappers merely retain the finite
family move whose table supplies that shared control.
-/

namespace DistributedSynthesis

universe i u v x y w s

section Generic

variable {I : Type i} {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable (M : I → BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- The actual local state used by the blind sender of a simultaneous family
controller.  The Boolean is the pre-selection/active flag already present in
every member projection; it is not a hidden-root or leader bit. -/
abbrev FiniteRootFamilyLocalOverlay
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State)) :=
  family.Control × Bool

/-- Initial local state of the shared family table. -/
def FiniteRootFamilyLocalOverlay.initial
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State)) :
    FiniteRootFamilyLocalOverlay M family :=
  (family.initial, false)

/-- The overlay is definitionally a valid local control for every hidden
member projection. -/
def FiniteRootFamilyLocalOverlay.memberControl
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (state : FiniteRootFamilyLocalOverlay M family) (index : I) :
    (finiteRootMemberController M family index).Control :=
  state

/-- One blind input advances only the shared table control.  The selection
flag becomes active after the first input, exactly as in every member
projection. -/
def FiniteRootFamilyLocalOverlay.step
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (state : FiniteRootFamilyLocalOverlay M family) (input : SIn) :
    FiniteRootFamilyLocalOverlay M family :=
  (family.step state.1 input, true)

/-- Output of the blind sender.  It is read directly from the simultaneous
table, before any hidden member is selected. -/
def FiniteRootFamilyLocalOverlay.output
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (state : FiniteRootFamilyLocalOverlay M family) (input : SIn) : SOut :=
  (family.labelOf state.1).1 input

/-- The initial overlay is the initial control of every projection. -/
@[simp] theorem FiniteRootFamilyLocalOverlay.memberControl_initial
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State)) (index : I) :
    (FiniteRootFamilyLocalOverlay.initial M family).memberControl M family
        index =
      (finiteRootMemberController M family index).initial :=
  rfl

/-- Projection commutes with the finite local transition. -/
@[simp] theorem FiniteRootFamilyLocalOverlay.memberControl_step
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (state : FiniteRootFamilyLocalOverlay M family) (index : I)
    (input : SIn) :
    (state.step M family input).memberControl M family index =
      (finiteRootMemberController M family index).step
        (state.memberControl M family index) input :=
  rfl

/-- Every hidden member emits the overlay's one physical sender output. -/
@[simp] theorem FiniteRootFamilyLocalOverlay.member_output
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (state : FiniteRootFamilyLocalOverlay M family) (index : I)
    (input : SIn) :
    ((finiteRootMemberController M family index).labelOf
        (state.memberControl M family index)).1 input =
      state.output M family input :=
  rfl

/-- The exact one-round local pair test.  Both output and successor control
are read from one shared finite state, hence cannot depend on the proof-side
anchor. -/
theorem FiniteRootFamilyLocalOverlay.localStep_eq
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (state : FiniteRootFamilyLocalOverlay M family) (left right : I)
    (input : SIn) :
    (((finiteRootMemberController M family left).labelOf
          (state.memberControl M family left)).1 input,
        (finiteRootMemberController M family left).step
          (state.memberControl M family left) input) =
      (((finiteRootMemberController M family right).labelOf
          (state.memberControl M family right)).1 input,
        (finiteRootMemberController M family right).step
          (state.memberControl M family right) input) :=
  rfl

end Generic

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A finite right-family move together with the one process-one state shared
by its two projections. -/
abbrev ProfiledRightFamilyPairOverlay :=
  Σ move : ProfiledRightFamilyPairMove A,
    FiniteRootFamilyLocalOverlay
      (profiledRightFamilyRootMonitors A move.1)
      move.2.toTransitionRationalTree

/-- Process-two mirror. -/
abbrev ProfiledLeftFamilyPairOverlay :=
  Σ move : ProfiledLeftFamilyPairMove A,
    FiniteRootFamilyLocalOverlay
      (profiledLeftFamilyRootMonitors A move.1)
      move.2.toTransitionRationalTree

noncomputable instance : Fintype (ProfiledRightFamilyPairOverlay A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledLeftFamilyPairOverlay A) := by
  classical
  infer_instance

/-- Install a right pair move at the shared initial sender state. -/
def ProfiledRightFamilyPairOverlay.initial
    (move : ProfiledRightFamilyPairMove A) :
    ProfiledRightFamilyPairOverlay A :=
  ⟨move, FiniteRootFamilyLocalOverlay.initial
    (profiledRightFamilyRootMonitors A move.1)
    move.2.toTransitionRationalTree⟩

/-- Install a left pair move at the shared initial sender state. -/
def ProfiledLeftFamilyPairOverlay.initial
    (move : ProfiledLeftFamilyPairMove A) :
    ProfiledLeftFamilyPairOverlay A :=
  ⟨move, FiniteRootFamilyLocalOverlay.initial
    (profiledLeftFamilyRootMonitors A move.1)
    move.2.toTransitionRationalTree⟩

/-- Advance the shared process-one state of a right-family move. -/
def ProfiledRightFamilyPairOverlay.step
    (state : ProfiledRightFamilyPairOverlay A) (input : In₁) :
    ProfiledRightFamilyPairOverlay A :=
  ⟨state.1, state.2.step
    (profiledRightFamilyRootMonitors A state.1.1)
    state.1.2.toTransitionRationalTree input⟩

/-- Advance the shared process-two state of a left-family move. -/
def ProfiledLeftFamilyPairOverlay.step
    (state : ProfiledLeftFamilyPairOverlay A) (input : In₂) :
    ProfiledLeftFamilyPairOverlay A :=
  ⟨state.1, state.2.step
    (profiledLeftFamilyRootMonitors A state.1.1)
    state.1.2.toTransitionRationalTree input⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Both hidden right anchors give the same process-one output and next
controller state. -/
theorem ProfiledRightFamilyPairOverlay.localStep_eq
    (state : ProfiledRightFamilyPairOverlay A) (left right : Bool)
    (input : In₁) :
    let family := state.1.2.toTransitionRationalTree
    let monitors := profiledRightFamilyRootMonitors A state.1.1
    let shared := state.2
    (((finiteRootMemberController monitors family left).labelOf
          (shared.memberControl monitors family left)).1 input,
        (finiteRootMemberController monitors family left).step
          (shared.memberControl monitors family left) input) =
      (((finiteRootMemberController monitors family right).labelOf
          (shared.memberControl monitors family right)).1 input,
        (finiteRootMemberController monitors family right).step
          (shared.memberControl monitors family right) input) := by
  exact FiniteRootFamilyLocalOverlay.localStep_eq
    (profiledRightFamilyRootMonitors A state.1.1)
    state.1.2.toTransitionRationalTree state.2 left right input

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Both hidden left anchors give the same process-two output and next
controller state. -/
theorem ProfiledLeftFamilyPairOverlay.localStep_eq
    (state : ProfiledLeftFamilyPairOverlay A) (left right : Bool)
    (input : In₂) :
    let family := state.1.2.toTransitionRationalTree
    let monitors := profiledLeftFamilyRootMonitors A state.1.1
    let shared := state.2
    (((finiteRootMemberController monitors family left).labelOf
          (shared.memberControl monitors family left)).1 input,
        (finiteRootMemberController monitors family left).step
          (shared.memberControl monitors family left) input) =
      (((finiteRootMemberController monitors family right).labelOf
          (shared.memberControl monitors family right)).1 input,
        (finiteRootMemberController monitors family right).step
          (shared.memberControl monitors family right) input) := by
  exact FiniteRootFamilyLocalOverlay.localStep_eq
    (profiledLeftFamilyRootMonitors A state.1.1)
    state.1.2.toTransitionRationalTree state.2 left right input

end

end DetParityAutomaton

end DistributedSynthesis
