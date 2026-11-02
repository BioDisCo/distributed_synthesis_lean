/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyPinnedReindexing
import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyProvenanceReindexing

/-!
# One extraction retaining both root pins and semantic provenance

Root pinning and arbitrary-node semantic provenance must constrain the same
state-controlled extraction.  Extracting a pinned weak controller and a
provenance controller separately gives no equality between their rational
choices.

This module composes the two existing generic constructions in the safe
order.  The member monitors are root-pinned first; one union controller is
then extracted under the strong table law and weakened on that literal
controller to the finite weak law.  The returned weak pinned move therefore
retains both its exact first record and its proof-only strong table law.
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
  (Strong Weak : ∀ descriptor,
    (((Root descriptor × RIn) × SIn) → ROut) → Prop)
variable
  (expected : ∀ member : Sigma Root,
    RIn × SIn → RealizedBlockRound RIn SIn ROut SOut)

variable [Fintype Descriptor] [DecidableEq Descriptor]
variable [∀ descriptor, Fintype (Root descriptor)]
variable [∀ descriptor, DecidableEq (Root descriptor)]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- A fixed finite weak pinned move whose literal underlying controller also
satisfies every descriptor-indexed strong table law. -/
noncomputable abbrev FiniteDescriptorFamilyPinnedProvenanceMove :=
  FiniteDescriptorFamilyProvenanceMove Root
    (descriptorRootPinnedMonitor Root M expected) Strong Weak

noncomputable instance :
    Fintype (FiniteDescriptorFamilyPinnedProvenanceMove Root M Strong Weak
      expected) := by
  classical
  infer_instance

/-- Perform one strong extraction after pinning every member monitor, then
weaken the law without changing controller states, transitions, or labels. -/
noncomputable def finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies
    [Inhabited (Sigma Root)] [Inhabited RIn] [Inhabited SIn]
    [Inhabited ROut]
    (himp : ∀ descriptor responses,
      Strong descriptor responses → Weak descriptor responses)
    (defaultTable : (((Sigma Root) × RIn) × SIn) → ROut)
    (hdefault : DescriptorRootUnionAllowed Root Strong defaultTable)
    (receiver : ∀ _ : Sigma Root,
      ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ member env,
      (M member.1 member.2).WinsPlay
        (pairPlay (receiver member) sender env))
    (hroot : ∀ member input,
      pairPlay (receiver member) sender (fun _ ↦ input) 0 =
        expected member input)
    (hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        ((finiteRootFamilyReceiver receiver) past)) :
    FiniteDescriptorFamilyPinnedProvenanceMove Root M Strong Weak expected := by
  apply finiteDescriptorFamilyProvenanceMoveOfStrategies Root
    (descriptorRootPinnedMonitor Root M expected) Strong Weak himp
    defaultTable hdefault receiver sender
  · intro member env
    exact (M member.1 member.2).rootPinned_realizable
      (expected member) (receiver member) sender (hwin member)
      (hroot member) env
  · exact hstrong

/-- Forget only the proof-only strong law.  The result is definitionally a
root-pinned weak move over the same controller. -/
noncomputable def FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (move : FiniteDescriptorFamilyPinnedProvenanceMove Root M Strong Weak
      expected) :
    FiniteDescriptorFamilyPinnedAllowedMove Root M Weak expected :=
  move.toWeakMove Root (descriptorRootPinnedMonitor Root M expected) Strong
    Weak

omit [DecidableEq RIn] in
/-- Arbitrary-node strong provenance survives in every descriptor projection
of the weak pinned readback. -/
theorem FiniteDescriptorFamilyPinnedProvenanceMove.controllerFor_strongAllowed
    (move : FiniteDescriptorFamilyPinnedProvenanceMove Root M Strong Weak
      expected)
    (descriptor : Descriptor) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor Root M expected descriptor))
      (Strong descriptor)
      ((move.toPinnedMove Root M Strong Weak expected).controllerFor Root
        (descriptorRootPinnedMonitor Root M expected) Weak descriptor
        |>.labeledTree) := by
  exact FiniteDescriptorFamilyProvenanceMove.controllerFor_strongAllowed Root
    (descriptorRootPinnedMonitor Root M expected) Strong Weak move descriptor

omit [DecidableEq RIn] in
/-- The exact first record is retained by the same weak controller whose
strong arbitrary-node law was proved above. -/
theorem FiniteDescriptorFamilyPinnedProvenanceMove.member_root_record
    [Inhabited RIn] [Inhabited SIn]
    (move : FiniteDescriptorFamilyPinnedProvenanceMove Root M Strong Weak
      expected)
    (descriptor : Descriptor) (root : Root descriptor)
    (input : RIn × SIn) :
    narrowedRecord
        ((M descriptor root).rootPinned (expected ⟨descriptor, root⟩))
        (((move.toPinnedMove Root M Strong Weak expected).memberController Root
          M Weak expected descriptor root).labeledTree [])
        ((M descriptor root).rootPinned
          (expected ⟨descriptor, root⟩)).initial input =
      expected ⟨descriptor, root⟩ input := by
  exact (move.toPinnedMove Root M Strong Weak expected).member_root_record Root
    M Weak expected descriptor root input

end

end DistributedSynthesis
