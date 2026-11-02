/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyReindexing
import DistributedSynthesis.Formalizations.Theorem.ThmRootPinnedBlockNarrowing

/-!
# Root-pinned descriptor-family extraction

`FiniteDescriptorFamilyAllowedMove` preserves every receiver-table law, but
such a law cannot constrain the blind sender component of a narrowed label.
For the sibling-install seam we must retain one sender/receiver equality from
the raw distributed strategy across rationalization.

This file puts the already proved finite `rootPinned` safety wrapper around
*each member monitor before the descriptor union is formed*.  One union
extraction therefore still shares a sender across all descriptors, preserves
`DescriptorRootUnionAllowed`, and additionally exposes the complete prescribed
root record for every member.  The pin is proof-side monitor state; it is not
an orientation, leader, descriptor, or selected-root input to the sender.
-/

namespace DistributedSynthesis

universe i u v x y w

section

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
variable
  (expected : ∀ member : Sigma Root,
    RIn × SIn → RealizedBlockRound RIn SIn ROut SOut)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-! ## Pinning before the union -/

/-- The member monitor pinned to the raw record selected for that exact
descriptor/root pair. -/
noncomputable abbrev descriptorRootPinnedMonitor
    (descriptor : Descriptor) (root : Root descriptor) :=
  (M descriptor root).rootPinned (expected ⟨descriptor, root⟩)

/-- One finite law-preserving descriptor-family move whose every member also
retains its prescribed first record. -/
noncomputable abbrev FiniteDescriptorFamilyPinnedAllowedMove :=
  FiniteDescriptorFamilyAllowedMove Root
    (descriptorRootPinnedMonitor Root M expected) Allowed

noncomputable instance :
    Fintype (FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected) := by
  classical
  infer_instance

/-- Extract the pinned union move from one semantic sender and all semantic
receivers.  The two pin premises are facts about those strategies, not
post-extraction equalities. -/
noncomputable def finiteDescriptorFamilyPinnedAllowedMoveOfStrategies
    [Inhabited (Sigma Root)] [Inhabited RIn] [Inhabited SIn]
    [Inhabited ROut]
    (defaultTable : (((Sigma Root) × RIn) × SIn) → ROut)
    (hdefault : DescriptorRootUnionAllowed Root Allowed defaultTable)
    (receiver : ∀ _ : Sigma Root,
      ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ member env,
      (M member.1 member.2).WinsPlay
        (pairPlay (receiver member) sender env))
    (hroot : ∀ member move,
      pairPlay (receiver member) sender (fun _ => move) 0 =
        expected member move)
    (hallowed : ∀ past,
      DescriptorRootUnionAllowed Root Allowed
        ((finiteRootFamilyReceiver receiver) past)) :
    FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected := by
  apply finiteDescriptorFamilyAllowedMoveOfStrategies Root
    (descriptorRootPinnedMonitor Root M expected) Allowed defaultTable
    hdefault receiver sender
  · intro member env
    exact (M member.1 member.2).rootPinned_realizable
      (expected member) (receiver member) sender (hwin member)
      (hroot member) env
  · exact hallowed

/-! ## Member readback -/

/-- The member controller projected from the pinned descriptor union.  Its
sender control is still the one union control. -/
noncomputable def FiniteDescriptorFamilyPinnedAllowedMove.memberController
    (move : FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected)
    (descriptor : Descriptor) (root : Root descriptor) :=
  finiteRootMemberController
    (descriptorRootPinnedMonitor Root M expected descriptor)
    (move.controllerFor Root (descriptorRootPinnedMonitor Root M expected)
      Allowed descriptor) root

section
omit [DecidableEq RIn]

/-- Every projected member retains its exact prescribed root record. -/
theorem FiniteDescriptorFamilyPinnedAllowedMove.member_root_record
    [Inhabited RIn] [Inhabited SIn]
    (move : FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected)
    (descriptor : Descriptor) (root : Root descriptor)
    (input : RIn × SIn) :
    narrowedRecord
        ((M descriptor root).rootPinned
          (expected ⟨descriptor, root⟩))
        ((move.memberController Root M Allowed expected descriptor root).labeledTree
          [])
        ((M descriptor root).rootPinned
          (expected ⟨descriptor, root⟩)).initial input =
      expected ⟨descriptor, root⟩ input := by
  apply (M descriptor root).rootPinned_root_record
    (expected ⟨descriptor, root⟩)
  exact move.member_allThreadsWin Root
    (descriptorRootPinnedMonitor Root M expected) Allowed descriptor root

/-- The receiver-table law is preserved on every descriptor projection even
though the projected monitor carries the finite root pin. -/
theorem FiniteDescriptorFamilyPinnedAllowedMove.controllerFor_allowed
    (move : FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected)
    (descriptor : Descriptor) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor Root M expected descriptor))
      (Allowed descriptor)
      (move.controllerFor Root (descriptorRootPinnedMonitor Root M expected)
        Allowed descriptor).labeledTree :=
  FiniteDescriptorFamilyAllowedMove.controllerFor_allowed Root
    (descriptorRootPinnedMonitor Root M expected) Allowed move descriptor

/-- All descriptor projections still use the literal same blind sender
table.  The root pin changes monitor state only. -/
theorem FiniteDescriptorFamilyPinnedAllowedMove.sender_eq
    (move : FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected)
    (left right : Descriptor) (word : List SIn) :
    ((move.controllerFor Root (descriptorRootPinnedMonitor Root M expected)
        Allowed left).labeledTree word).1 =
      ((move.controllerFor Root (descriptorRootPinnedMonitor Root M expected)
        Allowed right).labeledTree word).1 :=
  FiniteDescriptorFamilyAllowedMove.sender_eq Root
    (descriptorRootPinnedMonitor Root M expected) Allowed move left right word

end

/-- Erasing the finite pin from a projected member leaves a winning play of
the original member monitor.  The controller itself remains in the foreign
(pinned-union) control type, which is the faithful readback interface. -/
theorem FiniteDescriptorFamilyPinnedAllowedMove.member_base_wins
    [Inhabited RIn] [Inhabited SIn]
    (move : FiniteDescriptorFamilyPinnedAllowedMove Root M Allowed expected)
    (descriptor : Descriptor) (root : Root descriptor)
    (env : Nat → RIn × SIn) :
    (M descriptor root).WinsPlay
      (treePlay
        (narrowedInducedTree
          ((M descriptor root).rootPinned
            (expected ⟨descriptor, root⟩))
          (move.memberController Root M Allowed expected descriptor root).labeledTree)
        env) := by
  let pin := (M descriptor root).rootPinned
    (expected ⟨descriptor, root⟩)
  let controller :=
    move.memberController Root M Allowed expected descriptor root
  have hthreads : NarrowedAllThreadsWin pin controller.labeledTree := by
    exact move.member_allThreadsWin Root
      (descriptorRootPinnedMonitor Root M expected) Allowed descriptor root
  have htree : pin.lift.WinningTree
      (narrowedInducedTree pin controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin pin hthreads
  have hpinned : pin.WinsPlay
      (treePlay (narrowedInducedTree pin controller.labeledTree) env) :=
    (pin.lift_winningTree_iff
      (narrowedInducedTree pin controller.labeledTree)).mp htree env
  exact (M descriptor root).rootPinned_base_wins_of_wins
    (expected ⟨descriptor, root⟩)
    (treePlay (narrowedInducedTree pin controller.labeledTree) env) hpinned

end

end DistributedSynthesis
