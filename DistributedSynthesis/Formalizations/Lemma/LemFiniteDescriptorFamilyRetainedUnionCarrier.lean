/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRationalSenderFactorization

/-!
# A retained local carrier for one descriptor-union move

`FiniteDescriptorFamilyAllowedMove` performs the important extraction in the
right order: first put every receiver-side descriptor into one finite union,
then rationalize the one semantic sender shared by that union.  This file
exposes the smallest sender-side runtime state of the resulting object.

The state stores exactly

* one finite union-move identity; and
* one control of that union controller.

A descriptor is only a receiver-side projection of this state.  It is not
stored by the blind carrier and it is not an argument of its executable
transition.  The projection theorems show that even an arbitrary sequence of
receiver-side descriptor choices reads the same sender output trace and takes
the same sender-control transitions.

This carrier is independent of whether the accepted object is consumed as a
finite tree or as an infinite run.  Finite prefixes are represented by
`advanceWord`; infinite input streams by `senderRun` and `senderOutput`.
-/

namespace DistributedSynthesis

universe i u v x y w

noncomputable section

variable {Descriptor : Type i}
variable (Root : Descriptor → Type i)
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable
  (M : ∀ descriptor, Root descriptor →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (Allowed : ∀ descriptor,
    (((Root descriptor × RIn) × SIn) → ROut) → Prop)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

private noncomputable abbrev UnionMove :=
  FiniteDescriptorFamilyAllowedMove Root M Allowed

/-! ## The finite sender carrier -/

/-- The minimal runtime payload retained across an unresolved receiver-side
descriptor choice.  The control is a control of the one stored union table,
not a control selected independently from a descriptor projection. -/
structure FiniteDescriptorFamilyRetainedUnionState where
  move : UnionMove Root M Allowed
  control : move.1.toTransitionRationalTree.Control

noncomputable instance finiteDescriptorFamilyRetainedUnionStateFintype :
    Fintype (FiniteDescriptorFamilyRetainedUnionState Root M Allowed) := by
  classical
  let e : FiniteDescriptorFamilyRetainedUnionState Root M Allowed ≃
      Sigma (fun move : UnionMove Root M Allowed ↦
        move.1.toTransitionRationalTree.Control) :=
    { toFun := fun state ↦ ⟨state.move, state.control⟩
      invFun := fun state ↦ ⟨state.1, state.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Install a union move at its common initial sender control. -/
def FiniteDescriptorFamilyAllowedMove.retainedUnionInitial
    (move : UnionMove Root M Allowed) :
    FiniteDescriptorFamilyRetainedUnionState Root M Allowed :=
  ⟨move, move.1.toTransitionRationalTree.initial⟩

/-- Install a union move at the control reached by one already consumed
sender-input prefix. -/
def FiniteDescriptorFamilyAllowedMove.retainedUnionAt
    (move : UnionMove Root M Allowed) (word : List SIn) :
    FiniteDescriptorFamilyRetainedUnionState Root M Allowed :=
  ⟨move, move.1.toTransitionRationalTree.controlAt word⟩

/-! ## Receiver-side projection views -/

/-- View the stored control through one receiver descriptor.  This changes
only the receiver label/state type; the underlying sender control is the
same finite value. -/
def FiniteDescriptorFamilyRetainedUnionState.projectionControl
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptor : Descriptor) :
    (state.move.controllerFor Root M Allowed descriptor).Control :=
  state.control

/-- The sender-output function seen through one descriptor projection. -/
def FiniteDescriptorFamilyRetainedUnionState.projectionSenderLabel
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptor : Descriptor) : SIn → SOut :=
  ((state.move.controllerFor Root M Allowed descriptor).labelOf
    (state.projectionControl Root M Allowed descriptor)).1

omit [DecidableEq RIn] in
/-- Every receiver descriptor sees literally the same sender-output
function at the retained union control. -/
theorem
    FiniteDescriptorFamilyRetainedUnionState.projectionSenderLabel_eq
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (left right : Descriptor) :
    state.projectionSenderLabel Root M Allowed left =
      state.projectionSenderLabel Root M Allowed right := by
  exact
    FiniteDescriptorFamilyAllowedMove.controllerFor_senderAtControl_eq
      Root M Allowed state.move left right state.control

/-! ## Executable blind step -/

/-- One graph-blind sender step, read directly from the stored union table.
No descriptor, root, graph, orientation, leader flag, or history is an input
of this transition. -/
def FiniteDescriptorFamilyRetainedUnionState.senderNoRecv
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (input : SIn) :
    SOut × FiniteDescriptorFamilyRetainedUnionState Root M Allowed :=
  let controller := state.move.1.toTransitionRationalTree
  ((controller.labelOf state.control).1 input,
    ⟨state.move, controller.step state.control input⟩)

/-- Proof-side reading of the same blind step through a receiver descriptor.
This definition is useful at interfaces whose receiver state already names a
descriptor; executable blind code should use `senderNoRecv`. -/
def FiniteDescriptorFamilyRetainedUnionState.projectionSenderNoRecv
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptor : Descriptor) (input : SIn) :
    SOut × FiniteDescriptorFamilyRetainedUnionState Root M Allowed :=
  let controller := state.move.controllerFor Root M Allowed descriptor
  ((controller.labelOf
      (state.projectionControl Root M Allowed descriptor)).1 input,
    ⟨state.move,
      controller.step
        (state.projectionControl Root M Allowed descriptor) input⟩)

section
omit [DecidableEq RIn]

/-- Projecting does not alter either half of the sender step. -/
theorem
    FiniteDescriptorFamilyRetainedUnionState.projectionSenderNoRecv_eq
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptor : Descriptor) (input : SIn) :
    state.projectionSenderNoRecv Root M Allowed descriptor input =
      state.senderNoRecv Root M Allowed input := by
  rfl

/-- In particular, two arbitrary descriptor projections take the same
output/control step. -/
theorem
    FiniteDescriptorFamilyRetainedUnionState.projectionSenderNoRecv_eq_projection
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (left right : Descriptor) (input : SIn) :
    state.projectionSenderNoRecv Root M Allowed left input =
      state.projectionSenderNoRecv Root M Allowed right input := by
  rfl

@[simp] theorem
    FiniteDescriptorFamilyRetainedUnionState.senderNoRecv_move
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (input : SIn) :
    (state.senderNoRecv Root M Allowed input).2.move = state.move :=
  rfl

end

/-! ## Finite prefixes -/

/-- Advance the shared sender carrier through a finite local input word. -/
def FiniteDescriptorFamilyRetainedUnionState.advanceWord
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (word : List SIn) :
    FiniteDescriptorFamilyRetainedUnionState Root M Allowed :=
  ⟨state.move,
    word.foldl state.move.1.toTransitionRationalTree.step state.control⟩

section
omit [DecidableEq RIn]

@[simp] theorem
    FiniteDescriptorFamilyRetainedUnionState.advanceWord_cons
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (input : SIn) (word : List SIn) :
    state.advanceWord Root M Allowed (input :: word) =
      ((state.senderNoRecv Root M Allowed input).2).advanceWord Root M Allowed
        word :=
  rfl

@[simp] theorem
    FiniteDescriptorFamilyAllowedMove.retainedUnionAt_nil
    (move : UnionMove Root M Allowed) :
    move.retainedUnionAt Root M Allowed ([] : List SIn) =
      move.retainedUnionInitial Root M Allowed :=
  rfl

theorem
    FiniteDescriptorFamilyAllowedMove.retainedUnionAt_append
    (move : UnionMove Root M Allowed) (headWord suffix : List SIn) :
    move.retainedUnionAt Root M Allowed (headWord ++ suffix) =
      (move.retainedUnionAt Root M Allowed headWord).advanceWord Root M Allowed
        suffix := by
  simp [FiniteDescriptorFamilyAllowedMove.retainedUnionAt,
    FiniteDescriptorFamilyRetainedUnionState.advanceWord,
    TransitionRationalTree.controlAt, List.foldl_append]

end

/-! ## Infinite traces -/

/-- State of the shared sender carrier after `n` inputs of a stream. -/
def FiniteDescriptorFamilyRetainedUnionState.senderRun
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (inputs : Nat → SIn) : Nat →
      FiniteDescriptorFamilyRetainedUnionState Root M Allowed
  | 0 => state
  | n + 1 =>
      ((state.senderRun inputs n).senderNoRecv Root M Allowed
        (inputs n)).2

/-- Output emitted at position `n` of a local input stream. -/
def FiniteDescriptorFamilyRetainedUnionState.senderOutput
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (inputs : Nat → SIn) (n : Nat) : SOut :=
  ((state.senderRun Root M Allowed inputs n).senderNoRecv Root M Allowed
    (inputs n)).1

/-- Run obtained when a proof-side receiver chooses a possibly different
descriptor at every depth. -/
def FiniteDescriptorFamilyRetainedUnionState.projectedSenderRun
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptorAt : Nat → Descriptor) (inputs : Nat → SIn) : Nat →
      FiniteDescriptorFamilyRetainedUnionState Root M Allowed
  | 0 => state
  | n + 1 =>
      ((state.projectedSenderRun descriptorAt inputs n
        ).projectionSenderNoRecv Root M Allowed (descriptorAt n)
          (inputs n)).2

/-- Projected output trace corresponding to `projectedSenderRun`. -/
def FiniteDescriptorFamilyRetainedUnionState.projectedSenderOutput
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptorAt : Nat → Descriptor) (inputs : Nat → SIn)
    (n : Nat) : SOut :=
  ((state.projectedSenderRun Root M Allowed descriptorAt inputs n
    ).projectionSenderNoRecv Root M Allowed (descriptorAt n) (inputs n)).1

section
omit [DecidableEq RIn]

/-- Descriptor choices do not affect the retained sender state at any
depth. -/
theorem
    FiniteDescriptorFamilyRetainedUnionState.projectedSenderRun_eq
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptorAt : Nat → Descriptor) (inputs : Nat → SIn)
    (n : Nat) :
    state.projectedSenderRun Root M Allowed descriptorAt inputs n =
      state.senderRun Root M Allowed inputs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteDescriptorFamilyRetainedUnionState.projectedSenderRun,
        FiniteDescriptorFamilyRetainedUnionState.senderRun, ih,
        FiniteDescriptorFamilyRetainedUnionState.projectionSenderNoRecv_eq]

/-- **All-depth descriptor independence.**  Two arbitrary receiver-side
descriptor schedules induce the same blind output trace.  The theorem is
stronger than a fixed-descriptor comparison and is the direct reusable
finite/infinite handoff law. -/
theorem
    FiniteDescriptorFamilyRetainedUnionState.projectedSenderOutput_eq
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (left right : Nat → Descriptor) (inputs : Nat → SIn) (n : Nat) :
    state.projectedSenderOutput Root M Allowed left inputs n =
      state.projectedSenderOutput Root M Allowed right inputs n := by
  unfold FiniteDescriptorFamilyRetainedUnionState.projectedSenderOutput
  rw [state.projectedSenderRun_eq Root M Allowed left inputs n,
    state.projectedSenderRun_eq Root M Allowed right inputs n]
  exact congrFun
    ((state.senderRun Root M Allowed inputs n).projectionSenderLabel_eq
      Root M Allowed (left n) (right n)) (inputs n)

/-- Every projected trace is the canonical descriptor-free sender trace. -/
theorem
    FiniteDescriptorFamilyRetainedUnionState.projectedSenderOutput_eq_senderOutput
    (state : FiniteDescriptorFamilyRetainedUnionState Root M Allowed)
    (descriptorAt : Nat → Descriptor) (inputs : Nat → SIn)
    (n : Nat) :
    state.projectedSenderOutput Root M Allowed descriptorAt inputs n =
      state.senderOutput Root M Allowed inputs n := by
  unfold FiniteDescriptorFamilyRetainedUnionState.projectedSenderOutput
    FiniteDescriptorFamilyRetainedUnionState.senderOutput
  rw [state.projectedSenderRun_eq Root M Allowed descriptorAt inputs n]
  rfl

end

end

end DistributedSynthesis
