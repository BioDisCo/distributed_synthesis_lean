/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyOverlay

/-!
# Receiver banks dual to the shared root-family senders

A simultaneous family table shares the blind sender state, but its informed
partner must retain one monitor state for every proof-side member.  These
banks are the missing dual half of the executable family carrier.

Process one stores a left-family receiver bank in addition to its shared
right sender overlay; process two stores the right-family mirror.  A bank
contains both Boolean candidates and no selected member.  In particular none
of the controls below contains the current orientation or a strict-leader bit.
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

/-! ## Member states and simultaneous banks -/

/-- Receiver data for one member of a right-oriented family.  The pending
macro is package-wide because an exceptional or recurrent right block always
hands to one of the two recurrent-left origin summands. -/
abbrev EndToEndRightFamilyReceiverMemberState
    (move : EndToEndRightFamilyPairMove A package) (member : Bool) :=
  PairedEntryRow ×
    (endToEndRightRestartRootMonitor A package (move.1 member)).State ×
      Option (EndToEndRecurrentLeftMacro A package)

/-- Left-oriented mirror. -/
abbrev EndToEndLeftFamilyReceiverMemberState
    (move : EndToEndLeftFamilyPairMove A package) (member : Bool) :=
  PairedEntryRow ×
    (endToEndLeftRestartRootMonitor A package (move.1 member)).State ×
      Option (EndToEndRecurrentRightMacro A package)

/-- Both possible process-two receiver states for one shared right table.
There is deliberately no field selecting an actual member. -/
abbrev EndToEndRightFamilyReceiverBank
    (move : EndToEndRightFamilyPairMove A package) :=
  (member : Bool) → EndToEndRightFamilyReceiverMemberState A package move member

/-- Both possible process-one receiver states for one shared left table. -/
abbrev EndToEndLeftFamilyReceiverBank
    (move : EndToEndLeftFamilyPairMove A package) :=
  (member : Bool) → EndToEndLeftFamilyReceiverMemberState A package move member

noncomputable instance (move : EndToEndRightFamilyPairMove A package) :
    Fintype (EndToEndRightFamilyReceiverBank A package move) := by
  classical
  infer_instance

noncomputable instance (move : EndToEndLeftFamilyPairMove A package) :
    Fintype (EndToEndLeftFamilyReceiverBank A package move) := by
  classical
  infer_instance

/-- Initialize every right-family receiver projection at the restart state
stored by its root.  Rows are local proof projections, not a member selector. -/
def initialEndToEndRightFamilyReceiverBank
    (move : EndToEndRightFamilyPairMove A package)
    (row : Bool → PairedEntryRow) :
    EndToEndRightFamilyReceiverBank A package move :=
  fun member => ⟨row member, (move.1 member).2, none⟩

/-- Left-oriented mirror. -/
def initialEndToEndLeftFamilyReceiverBank
    (move : EndToEndLeftFamilyPairMove A package)
    (row : Bool → PairedEntryRow) :
    EndToEndLeftFamilyReceiverBank A package move :=
  fun member => ⟨row member, (move.1 member).2, none⟩

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem initialEndToEndRightFamilyReceiverBank_row
    (move : EndToEndRightFamilyPairMove A package)
    (row : Bool → PairedEntryRow) (member : Bool) :
    (initialEndToEndRightFamilyReceiverBank A package move row member).1 =
      row member :=
  rfl

@[simp] theorem initialEndToEndRightFamilyReceiverBank_monitor
    (move : EndToEndRightFamilyPairMove A package)
    (row : Bool → PairedEntryRow) (member : Bool) :
    (initialEndToEndRightFamilyReceiverBank A package move row member).2.1 =
      (move.1 member).2 :=
  rfl

@[simp] theorem initialEndToEndRightFamilyReceiverBank_pending
    (move : EndToEndRightFamilyPairMove A package)
    (row : Bool → PairedEntryRow) (member : Bool) :
    (initialEndToEndRightFamilyReceiverBank A package move row member).2.2 =
      none :=
  rfl

@[simp] theorem initialEndToEndLeftFamilyReceiverBank_row
    (move : EndToEndLeftFamilyPairMove A package)
    (row : Bool → PairedEntryRow) (member : Bool) :
    (initialEndToEndLeftFamilyReceiverBank A package move row member).1 =
      row member :=
  rfl

@[simp] theorem initialEndToEndLeftFamilyReceiverBank_monitor
    (move : EndToEndLeftFamilyPairMove A package)
    (row : Bool → PairedEntryRow) (member : Bool) :
    (initialEndToEndLeftFamilyReceiverBank A package move row member).2.1 =
      (move.1 member).2 :=
  rfl

@[simp] theorem initialEndToEndLeftFamilyReceiverBank_pending
    (move : EndToEndLeftFamilyPairMove A package)
    (row : Bool → PairedEntryRow) (member : Bool) :
    (initialEndToEndLeftFamilyReceiverBank A package move row member).2.2 =
      none :=
  rfl

end

/-! ## Proof-free dependent receiver bundles -/

/-- A process-two receiver bank together with the right family whose table
and roots give all of its dependent types.  The Boolean is the synchronized
past-overlap anchor already present in the old two-shadow carrier.  It selects
the receiver projection justified by the delivered history; it is not the
current graph or a strict-leader bit. -/
abbrev EndToEndRightFamilyReceiverBundle :=
  Bool × (Σ move : EndToEndRightFamilyPairMove A package,
    EndToEndRightFamilyReceiverBank A package move)

/-- Process-one mirror, with the same kind of past anchor. -/
abbrev EndToEndLeftFamilyReceiverBundle :=
  Bool × (Σ move : EndToEndLeftFamilyPairMove A package,
    EndToEndLeftFamilyReceiverBank A package move)

noncomputable instance : Fintype
    (EndToEndRightFamilyReceiverBundle A package) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndLeftFamilyReceiverBundle A package) := by
  classical
  infer_instance

/-- The complete finite post control of process one: its shared right sender
plus both possible left receiver projections. -/
structure EndToEndFamilyFullOneControl where
  rightSender : EndToEndRightFamilyPairOverlay A package
  leftReceiver : EndToEndLeftFamilyReceiverBundle A package

/-- The complete finite post control of process two. -/
structure EndToEndFamilyFullTwoControl where
  rightReceiver : EndToEndRightFamilyReceiverBundle A package
  leftSender : EndToEndLeftFamilyPairOverlay A package

noncomputable instance : Fintype
    (EndToEndFamilyFullOneControl A package) := by
  classical
  exact Fintype.ofEquiv
    (EndToEndRightFamilyPairOverlay A package ×
      EndToEndLeftFamilyReceiverBundle A package)
    { toFun := fun pair => ⟨pair.1, pair.2⟩
      invFun := fun control => (control.rightSender, control.leftReceiver)
      left_inv := by intro pair; cases pair; rfl
      right_inv := by intro control; cases control; rfl }

noncomputable instance : Fintype
    (EndToEndFamilyFullTwoControl A package) := by
  classical
  exact Fintype.ofEquiv
    (EndToEndRightFamilyReceiverBundle A package ×
      EndToEndLeftFamilyPairOverlay A package)
    { toFun := fun pair => ⟨pair.1, pair.2⟩
      invFun := fun control => (control.rightReceiver, control.leftSender)
      left_inv := by intro pair; cases pair; rfl
      right_inv := by intro control; cases control; rfl }

end

end DetParityAutomaton

end DistributedSynthesis
