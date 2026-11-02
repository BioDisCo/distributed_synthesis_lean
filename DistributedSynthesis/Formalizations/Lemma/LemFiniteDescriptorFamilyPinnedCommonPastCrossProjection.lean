/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyCommonPastNarrowing

/-!
# Cross projections from one pinned common-past family move

`exists_finiteDescriptorFamilyPinnedCommonPastMove` already constructs the
right finite object for a same-occurrence receiver comparison: one root-pinned
descriptor-family controller whose *literal* union receiver table is still a
single semantic receiver family at one common past.

This file packages that existential as a finite move type and gives its
heterogeneous readback law.  At every controller word and every fixed union
monitor state, two arbitrary projections of two hidden members satisfy every
equation satisfied by their semantic receivers at a common past.  In
particular, the two projections may be `closingBoth` and `informedBoth`; they
need not be the same function.

The final theorem records the exact scope of the construction.  Descriptor
projections may be compared whenever their local monitor states embed to the
same union state.  Fresh roots always do.  Independently continued active
states generally do not, and this interface deliberately supplies no false
identification between them.

All descriptors and roots remain receiver-side proof indices.  The sender
controller is the one shared union controller and receives no descriptor,
root, orientation, hierarchy side, leader bit, or strict-leader bit.
-/

namespace DistributedSynthesis

universe i u v x y w z

noncomputable section

variable {Descriptor : Type i}
variable (Root : Descriptor → Type i)
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable
  (M : ∀ descriptor, Root descriptor →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (Weak : ∀ descriptor,
    (((Root descriptor × RIn) × SIn) → ROut) → Prop)
variable
  (expected : ∀ member : Sigma Root,
    RIn × SIn → RealizedBlockRound RIn SIn ROut SOut)
variable
  (receiver : ∀ member : Sigma Root,
    ReceiverBlockStrategy RIn SIn ROut)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

private abbrev PinnedUnionMonitor :=
  finiteRootFamilyMonitor
    (descriptorRootUnionMonitor Root
      (descriptorRootPinnedMonitor Root M expected))

/-- The smallest runtime carrier returned by common-past extraction: the
existing pinned weak move, plus a proof that its very same union controller
still has common semantic provenance.  The proof does not add runtime data. -/
noncomputable abbrev FiniteDescriptorFamilyPinnedCommonPastMove :=
  { move : FiniteDescriptorFamilyPinnedAllowedMove Root M Weak expected //
    NarrowedTablesAllowed
      (PinnedUnionMonitor Root M expected)
      (FiniteRootFamilyCommonPastAllowed receiver)
      move.1.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype
      (FiniteDescriptorFamilyPinnedCommonPastMove Root M Weak expected
        receiver) := by
  classical
  infer_instance

/-- Package the existing common-past extraction without changing its chosen
controller. -/
noncomputable def finiteDescriptorFamilyPinnedCommonPastMoveOfStrategies
    [Inhabited (Sigma Root)] [Inhabited RIn] [Inhabited SIn]
    [Inhabited ROut]
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ member env,
      (M member.1 member.2).WinsPlay
        (pairPlay (receiver member) sender env))
    (hroot : ∀ member input,
      pairPlay (receiver member) sender (fun _ ↦ input) 0 =
        expected member input)
    (hweak : ∀ past,
      DescriptorRootUnionAllowed Root Weak
        (finiteRootFamilyReceiver receiver past)) :
    FiniteDescriptorFamilyPinnedCommonPastMove Root M Weak expected
      receiver := by
  classical
  let hexists := exists_finiteDescriptorFamilyPinnedCommonPastMove Root M Weak
    expected receiver sender hwin hroot hweak
  exact ⟨Classical.choose hexists, Classical.choose_spec hexists⟩

section
omit [DecidableEq RIn]

/-- A common-past family table preserves a heterogeneous semantic relation
between any two hidden members at every controller word.  Both member reads
use one fixed union monitor state; that is what makes them two rows of the
same literal receiver table. -/
theorem FiniteDescriptorFamilyPinnedCommonPastMove.union_receiver_rel
    (move : FiniteDescriptorFamilyPinnedCommonPastMove Root M Weak expected
      receiver)
    (Rel : ROut → ROut → Prop)
    (hsemantic : ∀ (past : List (RIn × SIn))
      (left right : Sigma Root) (receiverInput : RIn) (senderInput : SIn),
      Rel (receiver left past (receiverInput, senderInput))
        (receiver right past (receiverInput, senderInput)))
    (word : List SIn) (state : (PinnedUnionMonitor Root M expected).State)
    (left right : Sigma Root) (receiverInput : RIn) (senderInput : SIn) :
    Rel
      ((move.1.1.toTransitionRationalTree.labeledTree word).2 state
        ((left, receiverInput), senderInput))
      ((move.1.1.toTransitionRationalTree.labeledTree word).2 state
        ((right, receiverInput), senderInput)) := by
  rcases move.2 word state with ⟨past, hpast⟩
  rw [hpast]
  exact hsemantic
    (past.map fun old ↦ (old.1.2, old.2)) left right receiverInput
      senderInput

/-- Equality form with unrelated output projections.  This is the direct
shape of the closing/informed anti-mosaic equation. -/
theorem FiniteDescriptorFamilyPinnedCommonPastMove.union_receiver_projection_eq
    (move : FiniteDescriptorFamilyPinnedCommonPastMove Root M Weak expected
      receiver)
    {Projected : Type z}
    (projectLeft projectRight : ROut → Projected)
    (hsemantic : ∀ (past : List (RIn × SIn))
      (left right : Sigma Root) (receiverInput : RIn) (senderInput : SIn),
      projectLeft (receiver left past (receiverInput, senderInput)) =
        projectRight (receiver right past (receiverInput, senderInput)))
    (word : List SIn) (state : (PinnedUnionMonitor Root M expected).State)
    (left right : Sigma Root) (receiverInput : RIn) (senderInput : SIn) :
    projectLeft
        ((move.1.1.toTransitionRationalTree.labeledTree word).2 state
          ((left, receiverInput), senderInput)) =
      projectRight
        ((move.1.1.toTransitionRationalTree.labeledTree word).2 state
          ((right, receiverInput), senderInput)) := by
  exact move.union_receiver_rel Root M Weak expected receiver
    (fun left right ↦ projectLeft left = projectRight right) hsemantic word
      state left right receiverInput senderInput

/-- Cross-descriptor projection readback.  The explicit state equation is
the exact non-mosaic side condition: both reads must be rows of one union
table, not rows selected independently at two active monitor states. -/
theorem
    FiniteDescriptorFamilyPinnedCommonPastMove.controllerFor_receiver_projection_eq
    (move : FiniteDescriptorFamilyPinnedCommonPastMove Root M Weak expected
      receiver)
    {Projected : Type z}
    (projectLeft projectRight : ROut → Projected)
    (hsemantic : ∀ (past : List (RIn × SIn))
      (left right : Sigma Root) (receiverInput : RIn) (senderInput : SIn),
      projectLeft (receiver left past (receiverInput, senderInput)) =
        projectRight (receiver right past (receiverInput, senderInput)))
    (word : List SIn)
    (leftDescriptor rightDescriptor : Descriptor)
    (leftState :
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor Root M expected leftDescriptor)).State)
    (rightState :
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor Root M expected rightDescriptor)).State)
    (hstate :
      reindexFiniteRootFamilyState
          (descriptorRootUnionMonitor Root
            (descriptorRootPinnedMonitor Root M expected))
          (fun root : Root leftDescriptor ↦
            Sigma.mk leftDescriptor root) leftState =
        reindexFiniteRootFamilyState
          (descriptorRootUnionMonitor Root
            (descriptorRootPinnedMonitor Root M expected))
          (fun root : Root rightDescriptor ↦
            Sigma.mk rightDescriptor root) rightState)
    (leftRoot : Root leftDescriptor) (rightRoot : Root rightDescriptor)
    (receiverInput : RIn) (senderInput : SIn) :
    projectLeft
        (((move.1.controllerFor Root
          (descriptorRootPinnedMonitor Root M expected) Weak leftDescriptor
          ).labeledTree word).2 leftState
            ((leftRoot, receiverInput), senderInput)) =
      projectRight
        (((move.1.controllerFor Root
          (descriptorRootPinnedMonitor Root M expected) Weak rightDescriptor
          ).labeledTree word).2 rightState
            ((rightRoot, receiverInput), senderInput)) := by
  change projectLeft
      ((move.1.1.toTransitionRationalTree.labelOf
        ((move.1.controllerFor Root
          (descriptorRootPinnedMonitor Root M expected) Weak leftDescriptor
          ).controlAt word)).2
        (reindexFiniteRootFamilyState
          (descriptorRootUnionMonitor Root
            (descriptorRootPinnedMonitor Root M expected))
          (fun root : Root leftDescriptor ↦ Sigma.mk leftDescriptor root)
          leftState)
        ((⟨leftDescriptor, leftRoot⟩, receiverInput), senderInput)) =
    projectRight
      ((move.1.1.toTransitionRationalTree.labelOf
        ((move.1.controllerFor Root
          (descriptorRootPinnedMonitor Root M expected) Weak rightDescriptor
          ).controlAt word)).2
        (reindexFiniteRootFamilyState
          (descriptorRootUnionMonitor Root
            (descriptorRootPinnedMonitor Root M expected))
          (fun root : Root rightDescriptor ↦ Sigma.mk rightDescriptor root)
          rightState)
        ((⟨rightDescriptor, rightRoot⟩, receiverInput), senderInput))
  simp only [FiniteDescriptorFamilyAllowedMove.controllerFor,
    reindexFiniteRootFamilyController_controlAt]
  rw [hstate]
  exact move.union_receiver_projection_eq Root M Weak expected receiver
    projectLeft projectRight hsemantic word _ ⟨leftDescriptor, leftRoot⟩
      ⟨rightDescriptor, rightRoot⟩ receiverInput senderInput

/-- Fresh roots from arbitrary descriptors always satisfy the common-state
premise, even after an arbitrary sender-controller word. -/
theorem
    FiniteDescriptorFamilyPinnedCommonPastMove.controllerFor_initial_receiver_projection_eq
    (move : FiniteDescriptorFamilyPinnedCommonPastMove Root M Weak expected
      receiver)
    {Projected : Type z}
    (projectLeft projectRight : ROut → Projected)
    (hsemantic : ∀ (past : List (RIn × SIn))
      (left right : Sigma Root) (receiverInput : RIn) (senderInput : SIn),
      projectLeft (receiver left past (receiverInput, senderInput)) =
        projectRight (receiver right past (receiverInput, senderInput)))
    (word : List SIn)
    (leftDescriptor rightDescriptor : Descriptor)
    (leftRoot : Root leftDescriptor) (rightRoot : Root rightDescriptor)
    (receiverInput : RIn) (senderInput : SIn) :
    projectLeft
        (((move.1.controllerFor Root
          (descriptorRootPinnedMonitor Root M expected) Weak leftDescriptor
          ).labeledTree word).2 .initial
            ((leftRoot, receiverInput), senderInput)) =
      projectRight
        (((move.1.controllerFor Root
          (descriptorRootPinnedMonitor Root M expected) Weak rightDescriptor
          ).labeledTree word).2 .initial
            ((rightRoot, receiverInput), senderInput)) := by
  apply move.controllerFor_receiver_projection_eq Root M Weak expected receiver
    projectLeft projectRight hsemantic word leftDescriptor rightDescriptor
      .initial .initial
  rfl

end

end

end DistributedSynthesis
