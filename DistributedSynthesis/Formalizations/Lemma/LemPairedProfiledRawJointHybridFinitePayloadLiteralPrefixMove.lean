/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLiteralRetainedRelation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFinitePayloadLinkedSiblingMove

/-!
# Literal-prefix tables carrying an arbitrary pre-narrowed payload

This file is the two-record bridge from the generic finite-payload semantic
receiver to the repository's finite cross-anchor carrier.  For every finite
`Payload`, an exact semantic activation is enriched with

`(bare target, literal row, children actualDirection)`

*before* simultaneous rational narrowing.  The selected finite table retains
both its first full record and its second full record after advancing both
copies of the shared controller.  Consequently the receiver certificate at
both records still contains the exact payload chosen by the semantic raw
direction.

The hidden Boolean only indexes the two receiver copies installed at the
cross anchor.  Neither local transition tests a graph, hierarchy side,
leader bit, strict-leader bit, history, or semantic source.
-/

namespace DistributedSynthesis

universe u v x y s p

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

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

/-! ## Fixed finite alphabets -/

private noncomputable abbrev RightPayloadBaseMonitor
    {Payload : Type p} [Fintype Payload]
    (descriptor :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload) :=
  BlockRecordMonitor.raiseState.{v, u, max u v x y s p, x,
    max u v x y s, p}
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor false)

/-- The right-oriented fixed finite alphabet of two-record payload-linked
tables. -/
noncomputable abbrev ProfiledRawJointRightFinitePayloadLiteralPrefixMove
    (Payload : Type p) [Fintype Payload] :=
  FiniteCrossAnchorLiteralPrefixMove
    (RightPayloadBaseMonitor A (Payload := Payload))

noncomputable instance
    {Payload : Type p} [Fintype Payload] :
    Fintype (ProfiledRawJointRightFinitePayloadLiteralPrefixMove A Payload) := by
  infer_instance

/-- The state-universe lift is semantically inert; it only aligns the left
receiver alphabet with the generic cross-anchor universe. -/
private noncomputable abbrev LeftPayloadBaseMonitor
    {Payload : Type p} [Fintype Payload]
    (descriptor :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A Payload) :=
  BlockRecordMonitor.raiseState.{u, v, max u v x y s p, y,
    max u v y s, max x p}
    (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor false)

/-- Left-oriented mirror. -/
noncomputable abbrev ProfiledRawJointLeftFinitePayloadLiteralPrefixMove
    (Payload : Type p) [Fintype Payload] :=
  FiniteCrossAnchorLiteralPrefixMove
    (LeftPayloadBaseMonitor A (Payload := Payload))

noncomputable instance
    {Payload : Type p} [Fintype Payload] :
    Fintype (ProfiledRawJointLeftFinitePayloadLiteralPrefixMove A Payload) := by
  infer_instance

/-! ## Exact occurrence-level constructors -/

/-- Narrow the exact payload-enriched right receivers simultaneously for the
two anchor members.  Their finite image descriptors may vary with the member;
the semantic source and blind sender are shared.  The Boolean is only the
installed receiver-member coordinate. -/
noncomputable def profiledRawJointRightFinitePayloadLiteralPrefixMoveOf
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda) :
    ProfiledRawJointRightFinitePayloadLiteralPrefixMove A Payload := by
  let descriptor := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
      (activation member) children
  let monitor := fun member ↦ RightPayloadBaseMonitor A (descriptor member)
  let receiver := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
      (activation member) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) :=
    ⟨receiver false [] default⟩
  apply finiteCrossAnchorLiteralPrefixMove
    (RightPayloadBaseMonitor A (Payload := Payload))
    descriptor
    (fun member ↦ (monitor member).initial)
    receiver
    sender
  intro member env
  apply (BlockRecordMonitor.raiseState_winsPlay_iff
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A
      (descriptor member) false)
    _).2
  rw [sender_eq member]
  simpa [descriptor, receiver] using
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor_realizable A
      (activation member) children member env)

/-- Left mirror. -/
noncomputable def profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda) :
    ProfiledRawJointLeftFinitePayloadLiteralPrefixMove A Payload := by
  let descriptor := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
      (activation member) children
  let baseMonitor := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A
      (descriptor member) false
  let monitor := fun member ↦ LeftPayloadBaseMonitor A (descriptor member)
  let receiver := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
      (activation member) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        Payload) :=
    ⟨receiver false [] default⟩
  apply finiteCrossAnchorLiteralPrefixMove
    (LeftPayloadBaseMonitor A (Payload := Payload))
    descriptor
    (fun member ↦ (monitor member).initial)
    receiver
    sender
  intro member env
  apply (BlockRecordMonitor.raiseState_winsPlay_iff (baseMonitor member) _).2
  rw [sender_eq member]
  simpa [baseMonitor, descriptor, receiver] using
    (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor_realizable A
      (activation member) children member env)

/-! ## Finite local-carrier API -/

private noncomputable abbrev RightPayloadMonitor
    {Payload : Type p} [Fintype Payload] :=
  finiteCrossAnchorLiteralPrefixMonitor
    (RightPayloadBaseMonitor A (Payload := Payload))

private abbrev RightPayloadFirstAllowed
    {Payload : Type p} [Fintype Payload] :=
  finiteCrossAnchorLiteralPrefixFirstAllowed
    (RightPayloadBaseMonitor A (Payload := Payload))

private abbrev RightPayloadSecondAllowed
    {Payload : Type p} [Fintype Payload] :=
  finiteCrossAnchorLiteralPrefixSecondAllowed
    (RightPayloadBaseMonitor A (Payload := Payload))

noncomputable abbrev ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState
    (Payload : Type p) [Fintype Payload] :=
  FiniteCrossAnchorDescriptorFirstTwoSenderState
    (RightPayloadMonitor A (Payload := Payload))
    (RightPayloadFirstAllowed A (Payload := Payload))
    (RightPayloadSecondAllowed A (Payload := Payload))

noncomputable abbrev
    ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState
    (Payload : Type p) [Fintype Payload] :=
  FiniteCrossAnchorDescriptorFirstTwoReceiverState
    (RightPayloadMonitor A (Payload := Payload))
    (RightPayloadFirstAllowed A (Payload := Payload))
    (RightPayloadSecondAllowed A (Payload := Payload))

noncomputable def profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLiteralPrefixMove A Payload) :
    ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A Payload :=
  finiteCrossAnchorDescriptorFirstTwoSenderInitial
    (RightPayloadMonitor A (Payload := Payload))
    (RightPayloadFirstAllowed A (Payload := Payload))
    (RightPayloadSecondAllowed A (Payload := Payload)) move

noncomputable def
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLiteralPrefixMove A Payload)
    (anchor : Bool) :
    ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A Payload :=
  finiteCrossAnchorDescriptorFirstTwoReceiverInitial
    (RightPayloadMonitor A (Payload := Payload))
    (RightPayloadFirstAllowed A (Payload := Payload))
    (RightPayloadSecondAllowed A (Payload := Payload)) move anchor

noncomputable def profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv
    {Payload : Type p} [Fintype Payload]
    (state :
      ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A Payload)
    (input : In₁) :=
  finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
    (RightPayloadMonitor A (Payload := Payload))
    (RightPayloadFirstAllowed A (Payload := Payload))
    (RightPayloadSecondAllowed A (Payload := Payload)) state input

noncomputable def profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv
    {Payload : Type p} [Fintype Payload]
    (state :
      ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A Payload)
    (own : In₂) (delivered : In₁) :=
  finiteCrossAnchorDescriptorFirstTwoReceiverRecv
    (RightPayloadMonitor A (Payload := Payload))
    (RightPayloadFirstAllowed A (Payload := Payload))
    (RightPayloadSecondAllowed A (Payload := Payload)) state own delivered

private noncomputable abbrev LeftPayloadMonitor
    {Payload : Type p} [Fintype Payload] :=
  finiteCrossAnchorLiteralPrefixMonitor
    (LeftPayloadBaseMonitor A (Payload := Payload))

private abbrev LeftPayloadFirstAllowed
    {Payload : Type p} [Fintype Payload] :=
  finiteCrossAnchorLiteralPrefixFirstAllowed
    (LeftPayloadBaseMonitor A (Payload := Payload))

private abbrev LeftPayloadSecondAllowed
    {Payload : Type p} [Fintype Payload] :=
  finiteCrossAnchorLiteralPrefixSecondAllowed
    (LeftPayloadBaseMonitor A (Payload := Payload))

noncomputable abbrev ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState
    (Payload : Type p) [Fintype Payload] :=
  FiniteCrossAnchorDescriptorFirstTwoSenderState
    (LeftPayloadMonitor A (Payload := Payload))
    (LeftPayloadFirstAllowed A (Payload := Payload))
    (LeftPayloadSecondAllowed A (Payload := Payload))

noncomputable abbrev
    ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState
    (Payload : Type p) [Fintype Payload] :=
  FiniteCrossAnchorDescriptorFirstTwoReceiverState
    (LeftPayloadMonitor A (Payload := Payload))
    (LeftPayloadFirstAllowed A (Payload := Payload))
    (LeftPayloadSecondAllowed A (Payload := Payload))

noncomputable def profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointLeftFinitePayloadLiteralPrefixMove A Payload) :
    ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A Payload :=
  finiteCrossAnchorDescriptorFirstTwoSenderInitial
    (LeftPayloadMonitor A (Payload := Payload))
    (LeftPayloadFirstAllowed A (Payload := Payload))
    (LeftPayloadSecondAllowed A (Payload := Payload)) move

noncomputable def profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointLeftFinitePayloadLiteralPrefixMove A Payload)
    (anchor : Bool) :
    ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A Payload :=
  finiteCrossAnchorDescriptorFirstTwoReceiverInitial
    (LeftPayloadMonitor A (Payload := Payload))
    (LeftPayloadFirstAllowed A (Payload := Payload))
    (LeftPayloadSecondAllowed A (Payload := Payload)) move anchor

noncomputable def profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv
    {Payload : Type p} [Fintype Payload]
    (state :
      ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A Payload)
    (input : In₂) :=
  finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
    (LeftPayloadMonitor A (Payload := Payload))
    (LeftPayloadFirstAllowed A (Payload := Payload))
    (LeftPayloadSecondAllowed A (Payload := Payload)) state input

noncomputable def profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv
    {Payload : Type p} [Fintype Payload]
    (state :
      ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A Payload)
    (own : In₁) (delivered : In₂) :=
  finiteCrossAnchorDescriptorFirstTwoReceiverRecv
    (LeftPayloadMonitor A (Payload := Payload))
    (LeftPayloadFirstAllowed A (Payload := Payload))
    (LeftPayloadSecondAllowed A (Payload := Payload)) state own delivered

/-! ## Exact two-record readback

These theorems are stated for the complete local output pair.  In
particular, the receiver equality is in the row-exact payload-linked output
alphabet; no projection has erased the payload.
-/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The first right record of the narrowed table is the exact enriched
semantic record. -/
theorem profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_pair
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₂ × In₁) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let senderRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A move
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1,
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        senderRoot first.2).1) =
      (profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
          (activation anchor) children [] first,
        sender [] first.2) := by
  classical
  let descriptor := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
      (activation member) children
  let baseMonitor := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingMonitor A
      (descriptor member) false
  let monitor := fun member ↦ RightPayloadBaseMonitor A (descriptor member)
  let receiver := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
      (activation member) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) :=
    ⟨receiver false [] default⟩
  let hrealizable : ∀ member env,
      ((monitor member).restartAt (monitor member).initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff
      (baseMonitor member) _).2
    rw [sender_eq member]
    simpa [baseMonitor, descriptor, receiver] using
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor_realizable A
        (activation member) children member env)
  simpa [profiledRawJointRightFinitePayloadLiteralPrefixMoveOf, descriptor,
    baseMonitor, monitor, receiver, RightPayloadBaseMonitor,
    profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial,
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial,
    profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv,
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv,
    RightPayloadMonitor, RightPayloadFirstAllowed, RightPayloadSecondAllowed]
    using
      (finiteCrossAnchorLiteralPrefix_initial_outputs_eq_first
        (RightPayloadBaseMonitor A (Payload := Payload))
        descriptor (fun member ↦ (monitor member).initial)
        receiver sender hrealizable anchor first)

/-- After both local controls retain the first right record, the next output
pair is the exact second enriched semantic record. -/
theorem profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_pair
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let senderRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A move
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let senderAfterFirst :=
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        senderRoot first.2).2
    let receiverAfterFirst :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        senderAfterFirst second.2).1) =
      (profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
          (activation anchor) children [first] second,
        sender [first.2] second.2) := by
  classical
  let descriptor := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
      (activation member) children
  let baseMonitor := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingMonitor A
      (descriptor member) false
  let monitor := fun member ↦ RightPayloadBaseMonitor A (descriptor member)
  let receiver := fun member ↦
    profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
      (activation member) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) :=
    ⟨receiver false [] default⟩
  let hrealizable : ∀ member env,
      ((monitor member).restartAt (monitor member).initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff
      (baseMonitor member) _).2
    rw [sender_eq member]
    simpa [baseMonitor, descriptor, receiver] using
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor_realizable A
        (activation member) children member env)
  simpa [profiledRawJointRightFinitePayloadLiteralPrefixMoveOf, descriptor,
    baseMonitor, monitor, receiver, RightPayloadBaseMonitor,
    profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial,
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial,
    profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv,
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv,
    RightPayloadMonitor, RightPayloadFirstAllowed, RightPayloadSecondAllowed]
    using
      (finiteCrossAnchorLiteralPrefix_retained_outputs_eq_second
        (RightPayloadBaseMonitor A (Payload := Payload))
        descriptor (fun member ↦ (monitor member).initial)
        receiver sender hrealizable anchor first second)

/-- Left first-record mirror. -/
theorem profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_pair
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₁ × In₂) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let senderRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A move
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1,
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A senderRoot
        first.2).1) =
      (profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
          (activation anchor) children [] first,
        sender [] first.2) := by
  classical
  let descriptor := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
      (activation member) children
  let baseMonitor := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A
      (descriptor member) false
  let monitor := fun member ↦ LeftPayloadBaseMonitor A (descriptor member)
  let receiver := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
      (activation member) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        Payload) :=
    ⟨receiver false [] default⟩
  let hrealizable : ∀ member env,
      ((monitor member).restartAt (monitor member).initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff
      (baseMonitor member) _).2
    rw [sender_eq member]
    simpa [baseMonitor, descriptor, receiver] using
      (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor_realizable A
        (activation member) children member env)
  simpa [profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf, descriptor,
    baseMonitor, monitor, receiver, LeftPayloadBaseMonitor,
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial,
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial,
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv,
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv,
    LeftPayloadMonitor, LeftPayloadFirstAllowed, LeftPayloadSecondAllowed]
    using
      (finiteCrossAnchorLiteralPrefix_initial_outputs_eq_first
        (LeftPayloadBaseMonitor A (Payload := Payload))
        descriptor (fun member ↦ (monitor member).initial)
        receiver sender hrealizable anchor first)

/-- Left retained-second mirror. -/
theorem profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_pair
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let senderRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A move
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let senderAfterFirst :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A senderRoot
        first.2).2
    let receiverAfterFirst :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
        senderAfterFirst second.2).1) =
      (profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
          (activation anchor) children [first] second,
        sender [first.2] second.2) := by
  classical
  let descriptor := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
      (activation member) children
  let baseMonitor := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A
      (descriptor member) false
  let monitor := fun member ↦ LeftPayloadBaseMonitor A (descriptor member)
  let receiver := fun member ↦
    profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
      (activation member) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        Payload) :=
    ⟨receiver false [] default⟩
  let hrealizable : ∀ member env,
      ((monitor member).restartAt (monitor member).initial).WinsPlay
        (pairPlay (receiver member) sender env) := by
    intro member env
    apply (BlockRecordMonitor.raiseState_winsPlay_iff
      (baseMonitor member) _).2
    rw [sender_eq member]
    simpa [baseMonitor, descriptor, receiver] using
      (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor_realizable A
        (activation member) children member env)
  simpa [profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf, descriptor,
    baseMonitor, monitor, receiver, LeftPayloadBaseMonitor,
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial,
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial,
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv,
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv,
    LeftPayloadMonitor, LeftPayloadFirstAllowed, LeftPayloadSecondAllowed]
    using
      (finiteCrossAnchorLiteralPrefix_retained_outputs_eq_second
        (LeftPayloadBaseMonitor A (Payload := Payload))
        descriptor (fun member ↦ (monitor member).initial)
        receiver sender hrealizable anchor first second)

end

/-! ### Receiver-only forms

The following projections are the forms consumed by local handoff code.  The
equalities are still in the *full* row-exact payload alphabet.
-/

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₂ × In₁) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1 =
      profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
        (activation anchor) children [] first := by
  simpa using congrArg Prod.fst
    (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_pair
      A activation children sender sender_eq anchor first)

theorem profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1 =
      profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
        (activation anchor) children [first] second := by
  simpa using congrArg Prod.fst
    (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_pair
      A activation children sender sender_eq anchor first second)

theorem profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₁ × In₂) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1 =
      profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
        (activation anchor) children [] first := by
  simpa using congrArg Prod.fst
    (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_pair A
      activation children sender sender_eq anchor first)

theorem profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1 =
      profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
        (activation anchor) children [first] second := by
  simpa using congrArg Prod.fst
    (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_pair
      A activation children sender sender_eq anchor first second)

end

/-! ### Payload and physical projections -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_payload
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₂ × In₁) (row : PairedEntryRow) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      children (.strict
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row [] first)) := by
  dsimp only
  rw [profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first A
    activation children sender sender_eq anchor first]
  rfl

theorem
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_physical
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₂ × In₁) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    output.physical =
      (profiledRawJointTargetRightReceiverStrategy A (activation anchor) []
        first).physical := by
  dsimp only
  rw [profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first A
    activation children sender sender_eq anchor first]
  rfl

theorem
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_payload
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₂ × In₁) (row : PairedEntryRow) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      children (.strict
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row [first] second)) := by
  dsimp only
  rw [profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second A
    activation children sender sender_eq anchor first second]
  rfl

theorem
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_physical
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1
    output.physical =
      (profiledRawJointTargetRightReceiverStrategy A (activation anchor)
        [first] second).physical := by
  dsimp only
  rw [profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second A
    activation children sender sender_eq anchor first second]
  rfl

theorem
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_payload
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₁ × In₂) (row : PairedEntryRow) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      children (.strict
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row [] first)) := by
  dsimp only
  rw [profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first A
    activation children sender sender_eq anchor first]
  rfl

theorem
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_physical
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first : In₁ × In₂) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    output.physical =
      (profiledRawJointTargetLeftReceiverStrategy A (activation anchor) []
        first).physical := by
  dsimp only
  rw [profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first A
    activation children sender sender_eq anchor first]
  rfl

theorem
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_payload
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₁ × In₂) (row : PairedEntryRow) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      children (.strict
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row [first] second)) := by
  dsimp only
  rw [profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second A
    activation children sender sender_eq anchor first second]
  rfl

theorem
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_physical
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      activation children sender sender_eq
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1
    output.physical =
      (profiledRawJointTargetLeftReceiverStrategy A (activation anchor)
        [first] second).physical := by
  dsimp only
  rw [profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second A
    activation children sender sender_eq anchor first second]
  rfl

end

/-! ## Arbitrary-prefix exact-target readback

The first-two equations above are not by themselves a recurrence invariant:
a receiver may next hear after an arbitrarily long blind prefix.  The
following play-level interface erases the finite first-two guard, returns to
the exact payload-linked base monitor, and uses its image condition to recover
the pre-narrowing semantic target at every depth. -/

/-- Complete narrowed play of a right-oriented payload-linked literal move. -/
noncomputable def profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) Out₁ :=
  let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
    activation children sender sender_eq
  let monitorFamily := RightPayloadBaseMonitor A (Payload := Payload)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  treePlay (narrowedInducedTree guard controller.labeledTree) env

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At every depth, the complete right play wins the exact unguarded linked
monitor selected for the current member. -/
theorem profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay_wins
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    let descriptor :=
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
        (activation anchor) children
    let play := profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay A
      activation children sender sender_eq anchor env
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor false
      ).WinsPlay play := by
  dsimp only
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
      (activation anchor) children
  let baseMonitor :=
    profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor false
  let monitorFamily := RightPayloadBaseMonitor A (Payload := Payload)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let move := profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
    activation children sender sender_eq
  let receiver :=
    profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
      (activation false) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) :=
    ⟨receiver [] default⟩
  have hbase := move.memberController_base_wins monitor anchor env
  have hunraised : baseMonitor.WinsPlay
      (profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay A activation
        children sender sender_eq anchor env) := by
    exact (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).mp (by
      simpa [
        profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay,
        move, monitor, monitorFamily, baseMonitor, descriptor,
        RightPayloadBaseMonitor, finiteCrossAnchorRestartFamily,
        BlockRecordMonitor.restartAt,
        profiledRawJointRightFinitePayloadLiteralPrefixMoveOf,
        finiteCrossAnchorLiteralPrefixMove] using hbase)
  exact hunraised

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At an arbitrary depth, every right target is exactly one semantic target
from the selected member, at the queried row, and carries the payload chosen
from the same semantic input occurrence before narrowing. -/
theorem profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay_target_exists
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : Bool → ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₁ Out₁)
    (sender_eq : ∀ member,
      sender = pairedRightSenderStrategy (activation member).lambda)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay A
      activation children sender sender_eq anchor env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    ∃ past input,
      (projected n).2.1.target row =
        ((activation anchor).target row past input,
          (row, children (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input)))) := by
  dsimp only
  let selected := activation anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A selected
      children
  let play := profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay A
    activation children sender sender_eq anchor env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A) play
  have hrowExactWin :
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor
        false).WinsPlay play := by
    exact profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay_wins A
      activation children sender sender_eq anchor env
  have hwin' :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay projected := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetRightBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
          (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
          (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        play).mp hrowExactWin
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
    (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source projected hwin' n row
  have hallowed := hsafe.2
  have himage :
      ProfiledRawJointRightFinitePayloadLinkedTargetAllowed A selected children
        ((projected n).2.1.target row) :=
    (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf_allowed_iff A
      selected children _).mp hallowed
  rcases himage with ⟨witnessRow, past, input, htarget⟩
  have hrow :=
    profiledRawJointHybridFinitePayloadRowExactRightTarget_row A
      (play n).2.1 row
  change profiledRawJointHybridFinitePayloadLinkedTargetRow A
      ((projected n).2.1.target row) = row at hrow
  rw [htarget] at hrow
  change witnessRow = row at hrow
  subst witnessRow
  exact ⟨past, input, htarget⟩

/-- Complete narrowed play of a left-oriented payload-linked literal move. -/
noncomputable def profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        Payload) Out₂ :=
  let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
    activation children sender sender_eq
  let monitorFamily := LeftPayloadBaseMonitor A (Payload := Payload)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  treePlay (narrowedInducedTree guard controller.labeledTree) env

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At every depth, the complete left play wins the exact unguarded linked
monitor selected for the current member. -/
theorem profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay_wins
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    let descriptor :=
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
        (activation anchor) children
    let play := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay A
      activation children sender sender_eq anchor env
    (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor false
      ).WinsPlay play := by
  dsimp only
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
      (activation anchor) children
  let baseMonitor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor false
  let monitorFamily := LeftPayloadBaseMonitor A (Payload := Payload)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let move := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
    activation children sender sender_eq
  let receiver :=
    profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
      (activation false) children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        Payload) :=
    ⟨receiver [] default⟩
  have hbase := move.memberController_base_wins monitor anchor env
  have hunraised : baseMonitor.WinsPlay
      (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay A activation
        children sender sender_eq anchor env) := by
    exact (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).mp (by
      simpa [
        profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay,
        move, monitor, monitorFamily, baseMonitor, descriptor,
        LeftPayloadBaseMonitor, finiteCrossAnchorRestartFamily,
        BlockRecordMonitor.restartAt,
        profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf,
        finiteCrossAnchorLiteralPrefixMove] using hbase)
  exact hunraised

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-oriented arbitrary-prefix exact semantic target and payload
readback. -/
theorem profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay_target_exists
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : Bool → ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (sender : SenderBlockStrategy In₂ Out₂)
    (sender_eq : ∀ member,
      sender = pairedLeftSenderStrategy (activation member).lambda)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay A
      activation children sender sender_eq anchor env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    ∃ past input,
      (projected n).2.1.target row =
        ((activation anchor).target row past input,
          (row, children (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input)))) := by
  dsimp only
  let selected := activation anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A selected
      children
  let play := profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay A
    activation children sender sender_eq anchor env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A) play
  have hrowExactWin :
      (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor
        false).WinsPlay play := by
    exact profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay_wins A
      activation children sender sender_eq anchor env
  have hwin' :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay projected := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetLeftBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
          (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
          (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        play).mp hrowExactWin
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
    (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source projected hwin' n row
  have hallowed := hsafe.2
  have himage :
      ProfiledRawJointLeftFinitePayloadLinkedTargetAllowed A selected children
        ((projected n).2.1.target row) :=
    (profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf_allowed_iff A
      selected children _).mp hallowed
  rcases himage with ⟨witnessRow, past, input, htarget⟩
  have hrow :=
    profiledRawJointHybridFinitePayloadRowExactLeftTarget_row A
      (play n).2.1 row
  change profiledRawJointHybridFinitePayloadLinkedTargetRow A
      ((projected n).2.1.target row) = row at hrow
  rw [htarget] at hrow
  change witnessRow = row at hrow
  subst witnessRow
  exact ⟨past, input, htarget⟩

end

end DetParityAutomaton

end DistributedSynthesis
