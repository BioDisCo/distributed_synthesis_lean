/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyReindexing

/-!
# Exact sender behavior carried by a finite rational table

The state-controlled narrowing table is a finite value, but it denotes a
complete (infinite-domain) blind sender strategy.  This file records the
exact factorization: after rationalization, every output at every sender word
is a projection of that one finite table value.  The same statement survives
descriptor-family reindexing literally.

This is intentionally a *post-rationalization* theorem.  The Rabin extraction
used to construct a `LocallyConsistentNarrowedTable` preserves its accepted
language and the imposed label laws; it does not reproduce the arbitrary raw
`SenderBlockStrategy` from which the non-regular witness was built.  Thus the
lemmas below can be used as a finite `MoveIdentity` readback, but they do not
assert the missing finite-state retraction of a raw distributed strategy.
-/

namespace DistributedSynthesis

universe i u v x y w

section LocallyConsistentTable

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable (Allowed : (RIn × SIn → ROut) → Prop)
variable [DecidablePred Allowed]

/-- The complete blind sender strategy denoted by one finite narrowed table. -/
noncomputable def LocallyConsistentNarrowedTable.senderStrategy
    (table : LocallyConsistentNarrowedTable M Allowed) :
    SenderBlockStrategy SIn SOut :=
  fun word input =>
    (table.toTransitionRationalTree.labeledTree word).1 input

omit [DecidableEq RIn] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [DecidablePred Allowed] in
@[simp] theorem LocallyConsistentNarrowedTable.senderStrategy_apply
    (table : LocallyConsistentNarrowedTable M Allowed)
    (word : List SIn) (input : SIn) :
    table.senderStrategy M Allowed word input =
      (table.toTransitionRationalTree.labeledTree word).1 input :=
  rfl

omit [DecidableEq RIn] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [DecidablePred Allowed] in
/-- Equality of the finite table identity gives equality of the complete
sender behavior, not merely equality at its initial node. -/
theorem LocallyConsistentNarrowedTable.senderStrategy_eq_of_table_eq
    {left right : LocallyConsistentNarrowedTable M Allowed}
    (h : left = right) :
    left.senderStrategy M Allowed = right.senderStrategy M Allowed := by
  exact congrArg (fun table => table.senderStrategy M Allowed) h

end LocallyConsistentTable

section DescriptorFamily

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

/-- The one complete blind sender strategy denoted by a finite union move.
It is read directly from the union table, before any descriptor projection. -/
noncomputable def FiniteDescriptorFamilyAllowedMove.sharedSenderStrategy
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed) :
    SenderBlockStrategy SIn SOut :=
  fun word input =>
    (move.1.toTransitionRationalTree.labeledTree word).1 input

section
omit [DecidableEq RIn]

@[simp] theorem FiniteDescriptorFamilyAllowedMove.sharedSenderStrategy_apply
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (word : List SIn) (input : SIn) :
    move.sharedSenderStrategy Root M Allowed word input =
      (move.1.toTransitionRationalTree.labeledTree word).1 input :=
  rfl

/-- Every descriptor projection reads the exact same rational sender
strategy carried by the finite union move. -/
theorem FiniteDescriptorFamilyAllowedMove.controllerFor_senderStrategy
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (descriptor : Descriptor) (word : List SIn) :
    ((move.controllerFor Root M Allowed descriptor).labeledTree word).1 =
      move.sharedSenderStrategy Root M Allowed word := by
  simp only [FiniteDescriptorFamilyAllowedMove.controllerFor,
    FiniteDescriptorFamilyAllowedMove.sharedSenderStrategy]
  exact reindexFiniteRootFamilyController_sender
    (descriptorRootUnionMonitor Root M)
    (fun root : Root descriptor => Sigma.mk descriptor root)
    move.1.toTransitionRationalTree word

/-- Descriptor projection does not change the sender label at an arbitrary
retained union-control state.  This is stronger than the root/word form above
in exactly the way needed by a deferred local carrier: after an unresolved
round the carrier may retain a control directly instead of reconstructing a
word that reaches it. -/
theorem FiniteDescriptorFamilyAllowedMove.controllerFor_senderAtControl_eq
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (left right : Descriptor)
    (control : move.1.toTransitionRationalTree.Control) :
    ((move.controllerFor Root M Allowed left).labelOf control).1 =
      ((move.controllerFor Root M Allowed right).labelOf control).1 := by
  rfl

/-- All descriptor projections also advance the retained sender control by
the literal same transition.  Together with
`controllerFor_senderAtControl_eq`, this is the one-step bisimulation law for
two receiver-side projections of one stored union-move identity. -/
theorem FiniteDescriptorFamilyAllowedMove.controllerFor_step_eq
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (left right : Descriptor)
    (control : move.1.toTransitionRationalTree.Control) (input : SIn) :
    (move.controllerFor Root M Allowed left).step control input =
      (move.controllerFor Root M Allowed right).step control input := by
  rfl

/-- Bundled Mealy-step form of the two preceding laws.  A runtime carrier may
store the union move and this one control once; changing only the
receiver-side descriptor then leaves the complete blind step unchanged. -/
theorem FiniteDescriptorFamilyAllowedMove.controllerFor_senderStep_eq
    (move : FiniteDescriptorFamilyAllowedMove Root M Allowed)
    (left right : Descriptor)
    (control : move.1.toTransitionRationalTree.Control) (input : SIn) :
    (((move.controllerFor Root M Allowed left).labelOf control).1 input,
        (move.controllerFor Root M Allowed left).step control input) =
      (((move.controllerFor Root M Allowed right).labelOf control).1 input,
        (move.controllerFor Root M Allowed right).step control input) := by
  rfl

/-- Consequently equality of the finite union-move identity entails
extensional equality of its complete infinite-domain sender strategies. -/
theorem FiniteDescriptorFamilyAllowedMove.sharedSenderStrategy_eq_of_move_eq
    {left right : FiniteDescriptorFamilyAllowedMove Root M Allowed}
    (h : left = right) :
    left.sharedSenderStrategy Root M Allowed =
      right.sharedSenderStrategy Root M Allowed := by
  exact congrArg
    (fun move => move.sharedSenderStrategy Root M Allowed) h

end

end DescriptorFamily

end DistributedSynthesis
