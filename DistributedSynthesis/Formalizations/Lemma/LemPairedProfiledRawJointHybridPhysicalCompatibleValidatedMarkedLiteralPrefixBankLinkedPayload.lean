/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFinitePayloadLiteralPrefixMove
import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOneSidedIncomingOrigin

/-!
# The exact marked-bank successor as a pre-narrowing finite payload

The payload-polymorphic linked-target construction expects a finite function
from concrete raw directions to controller states.  For the marked bank that
function is exactly the ordinary same-bank transition:

`direction ↦ successor state (state.childCode direction)`.

This file keeps two facts deliberately separate.  First, the payload emitted
by a semantic receiver is definitionally this exact successor.  Second, if
the current bank state is reachable, that payload is reachable and stores the
exact full child code.  The later literal-prefix construction may therefore
attach the payload before narrowing without choosing a representative from a
bare-target fibre afterwards.

The incoming semantic edge itself is recovered separately by
`...FiniteStep.rightIncomingOrigin` / `leftIncomingOrigin`: those theorems
turn `packet.marked_current` into the exact family, direction, member, and
literal-table equality.  No executable transition receives any of those
proof witnesses.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev BankReachable
    (state : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
    hwin state

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

/-! ## Exact finite child payload -/

/-- The finite payload table attached before receiver narrowing.  It is the
same bank's exact transition at the full code selected by the concrete raw
direction. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren
    (state : BankControl A strategy hwin) :
    HybridDirection (In₁ := In₁) (In₂ := In₂) →
      BankControl A strategy hwin :=
  fun direction ↦
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
      hwin state (state.childCode A strategy hwin direction)

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_apply
    (state : BankControl A strategy hwin)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state direction =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
        strategy hwin state (state.childCode A strategy hwin direction) :=
  rfl

/-! ## Invariant facts, kept separate from payload materialization -/

/-- Every exact child payload of a reachable bank state remains reachable. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    BankReachable A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state direction) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor_reachable A
      strategy hwin state hreachable (state.childCode A strategy hwin direction)

/-- The exact payload stores the complete requested child code, not merely
its public incidence projection. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state direction).2.1 =
      state.childCode A strategy hwin direction := by
  exact
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_code
      A strategy hwin state hreachable direction

/-- In particular, the literal annotation carried by the exact payload is
the replace-only annotation selected by the current packet and direction. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_literal
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state direction).2.1.2.2.2 =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        packet.source state.2.1.2.2.2 direction := by
  exact
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_literal
      A strategy hwin state hreachable direction

/-! ## Exact receiver specialization -/

/-- Attach the exact marked-bank child table to a semantic right receiver
before any finite-tree narrowing. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source) :=
  profiledRawJointRightFinitePayloadLinkedSiblingReceiver A activation
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin state)

/-- The physical right output is unchanged by the bank payload. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver_physical
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
        A strategy hwin state activation past input)).physical =
      (profiledRawJointTargetRightReceiverStrategy A activation past
        input).physical :=
  rfl

/-- The bare target is unchanged by the bank payload. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver_bareTarget
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    ((profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
        A strategy hwin state activation past input)).target row).1 =
      activation.target row past input :=
  rfl

/-- The target payload is definitionally the same-bank successor at the
actual raw direction encoded by this concrete receiver row and input. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver_payload
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
            A strategy hwin state activation past input)).target row) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input)) :=
  rfl

/-- Reachability is a separate invariant consequence of the exact payload
equation. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver_payload_reachable
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
            A strategy hwin state activation past input)).target row)) := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver_payload]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable _

/-- Left-oriented exact receiver specialization. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source) :=
  profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A activation
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin state)

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver_physical
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
        A strategy hwin state activation past input)).physical =
      (profiledRawJointTargetLeftReceiverStrategy A activation past
        input).physical :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver_bareTarget
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    ((profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
        A strategy hwin state activation past input)).target row).1 =
      activation.target row past input :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver_payload
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (state : BankControl A strategy hwin)
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
            A strategy hwin state activation past input)).target row) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input)) :=
  rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver_payload_reachable
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
            A strategy hwin state activation past input)).target row)) := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver_payload]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable _

/-! ## The same two-anchor semantic occurrence, linked before narrowing -/

/-- Fixed finite right-table alphabet after specializing the generic payload
to the marked-bank controller state. -/
noncomputable abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixMove A
    (BankControl A strategy hwin)

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveFintype :
    Fintype
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
        strategy hwin) := by
  infer_instance

/-- Left-table mirror. -/
noncomputable abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixMove A
    (BankControl A strategy hwin)

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveFintype :
    Fintype
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
        strategy hwin) := by
  infer_instance

/-- The exact two right sibling activations of one semantic occurrence.
Their semantic root may differ with the hidden member, but the source slot
and blind sender lambda are shared. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) :=
  profiledRawJointRightPhysicalSiblingActivation A hwin family direction
    semanticMember hmember member

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations_sender
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) :
    profiledRawJointRightSiblingSender A semanticMember =
      pairedRightSenderStrategy
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember
          member).lambda :=
  rfl

/-- Rebuild the literal-prefix table from the same semantic occurrence as
the old table, but attach the exact next marked-bank state to every receiver
target before simultaneous narrowing. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
      strategy hwin :=
  profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations A
      strategy hwin family direction semanticMember hmember)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin state)
    (profiledRawJointRightSiblingSender A semanticMember)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations_sender
      A strategy hwin family direction semanticMember hmember)

/-- Exact left sibling activations. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) :=
  profiledRawJointLeftPhysicalSiblingActivation A hwin family direction
    semanticMember hmember member

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations_sender
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) :
    profiledRawJointLeftSiblingSender A semanticMember =
      pairedLeftSenderStrategy
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember
          member).lambda :=
  rfl

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
      strategy hwin :=
  profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations A
      strategy hwin family direction semanticMember hmember)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin state)
    (profiledRawJointLeftSiblingSender A semanticMember)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations_sender
      A strategy hwin family direction semanticMember hmember)

/-! ## Arbitrary-prefix exact-target validity

The first/two-record equations below are useful executable sanity checks, but
the recurring controller may receive after an arbitrarily long blind prefix.
The real invariant is therefore stated on the complete narrowed play.  Guard
erasure exposes the payload-linked block monitor, whose target-safety clause
places every emitted target back in the exact semantic image used before
narrowing. -/

/-- Complete narrowed right play of the payload-linked literal table. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) Out₁ :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  let monitorFamily := fun descriptor :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A
        (BankControl A strategy hwin) ↦
    BlockRecordMonitor.raiseState
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor
        false)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  treePlay (narrowedInducedTree guard controller.labeledTree) env

/-- Guard erasure for the exact payload-linked right table, at every depth. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_wins
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
    let play :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor false
      ).WinsPlay
      play := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state)
  let baseMonitor :=
    profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor false
  let monitorFamily := fun candidate :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A
        (BankControl A strategy hwin) ↦
    BlockRecordMonitor.raiseState
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A candidate
        false)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin state activation [] default⟩
  have hbase := move.memberController_base_wins monitor anchor env
  have hunraised : baseMonitor.WinsPlay
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env) := by
    exact (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).mp (by
      simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay,
        move, monitor, monitorFamily, baseMonitor, descriptor, activation,
        finiteCrossAnchorRestartFamily, BlockRecordMonitor.restartAt,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf,
        profiledRawJointRightFinitePayloadLiteralPrefixMoveOf,
        finiteCrossAnchorLiteralPrefixMove] using hbase)
  exact hunraised

/-- At an arbitrary depth, every target of the narrowed right table still
contains a genuine same-bank successor selected by one concrete semantic
right direction. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_payload_exists
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env
    ∃ past input,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (((BlockRecordMonitor.projectReceiverPlay
            (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection
              A) play n).2.1.target row)) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) row past input)) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state)
  let play :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin state family direction semanticMember hmember anchor env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A) play
  have hrowExactWin :
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor
        false).WinsPlay play := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_wins
        A strategy hwin state family direction semanticMember hmember anchor
          env
  have hwin' :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay projected := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetRightBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
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
      ProfiledRawJointRightFinitePayloadLinkedTargetAllowed A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        ((projected n).2.1.target row) :=
    (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf_allowed_iff A
      activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state) _).mp hallowed
  rcases himage with ⟨witnessRow, past, input, htarget⟩
  have hrow :=
    profiledRawJointHybridFinitePayloadRowExactRightTarget_row A
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env n).2.1 row
  change profiledRawJointHybridFinitePayloadLinkedTargetRow A
      ((projected n).2.1.target row) = row at hrow
  rw [htarget] at hrow
  change witnessRow = row at hrow
  subst witnessRow
  refine ⟨past, input, ?_⟩
  rw [htarget]
  rfl

/-- Complete narrowed left play of the payload-linked literal table. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) Out₂ :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  let monitorFamily := fun descriptor :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A
        (BankControl A strategy hwin) ↦
    BlockRecordMonitor.raiseState.{u, v, max u v x y s, y,
      max u v y s, max x (max u v x y s)}
      (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor
        false)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  treePlay (narrowedInducedTree guard controller.labeledTree) env

/-- Guard erasure for the exact payload-linked left table, at every depth. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
    let play :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env
    (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor false
      ).WinsPlay play := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state)
  let baseMonitor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor false
  let monitorFamily := fun candidate :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A
        (BankControl A strategy hwin) ↦
    BlockRecordMonitor.raiseState.{u, v, max u v x y s, y,
      max u v y s, max x (max u v x y s)}
      (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A candidate
        false)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin state activation [] default⟩
  have hbase := move.memberController_base_wins monitor anchor env
  have hunraised : baseMonitor.WinsPlay
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env) := by
    exact (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).mp (by
      simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay,
        move, monitor, monitorFamily, baseMonitor, descriptor, activation,
        finiteCrossAnchorRestartFamily, BlockRecordMonitor.restartAt,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf,
        profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf,
        finiteCrossAnchorLiteralPrefixMove] using hbase)
  exact hunraised

/-- Arbitrary-depth left target validity. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_payload_exists
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env
    ∃ past input,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (((BlockRecordMonitor.projectReceiverPlay
            (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection
              A) play n).2.1.target row)) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) row past input)) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state)
  let play :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin state family direction semanticMember hmember anchor env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A) play
  have hrowExactWin :
      (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor
        false).WinsPlay play := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
        A strategy hwin state family direction semanticMember hmember anchor
          env
  have hwin' :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay projected := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetLeftBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
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
      ProfiledRawJointLeftFinitePayloadLinkedTargetAllowed A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        ((projected n).2.1.target row) :=
    (profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf_allowed_iff A
      activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state) _).mp hallowed
  rcases himage with ⟨witnessRow, past, input, htarget⟩
  have hrow :=
    profiledRawJointHybridFinitePayloadRowExactLeftTarget_row A
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env n).2.1 row
  change profiledRawJointHybridFinitePayloadLinkedTargetRow A
      ((projected n).2.1.target row) = row at hrow
  rw [htarget] at hrow
  change witnessRow = row at hrow
  subst witnessRow
  refine ⟨past, input, ?_⟩
  rw [htarget]
  rfl

/-! ### Canonical local controls at an arbitrary finite prefix -/

/-- The graph-blind right endpoint at an arbitrary complete-input prefix of
the exact linked occurrence.  The prefix is a proof-side witness only. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (past : List (In₂ × In₁)) :
    ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A
      (BankControl A strategy hwin) :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  ⟨move, finiteCrossAnchorSenderAtPrefix move.2 past⟩

/-- The matching member-threaded right receiver at the same prefix. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (past : List (In₂ × In₁)) :
    ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A
      (BankControl A strategy hwin) :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  ⟨move, finiteCrossAnchorReceiverAtPrefix move.2 anchor past⟩

/-- Operational right receive after any finite reachable prefix still emits
an exact same-bank successor.  This is the local-control bridge from the
arbitrary-depth play invariant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix_payload_exists
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    let receiver :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
        A strategy hwin state family direction semanticMember hmember anchor
          past
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A receiver
        input.1 input.2).1
    ∃ semanticPast semanticInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (output.target row).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) row semanticPast
                  semanticInput)) := by
  dsimp only
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin state activation [] default⟩
  let env : Nat → In₂ × In₁ :=
    DetParityAutomaton.omegaOfList (past ++ [input])
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_payload_exists
      A strategy hwin state family direction semanticMember hmember anchor env
        past.length row
  have hpast : DetParityAutomaton.omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [DetParityAutomaton.omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change DetParityAutomaton.omegaOfList (past ++ [input]) n = past[n]
      rw [DetParityAutomaton.omegaOfList_eq_getElem
        (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change DetParityAutomaton.omegaOfList (past ++ [input]) past.length = input
    rw [DetParityAutomaton.omegaOfList_eq_getElem
      (past ++ [input]) past.length hnPrefix]
    simp
  have hround := finiteCrossAnchor_localRound_atPrefix_eq_treePlay move.2
    anchor past input env hpast hinput
  have hreceiver := congrArg (fun record => record.2.1) hround
  refine ⟨semanticPast, semanticInput, ?_⟩
  rw [← hpayload]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix,
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay,
    move] using congrArg
      (fun output =>
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (output.target row).1) hreceiver

/-- The payload emitted by the canonical right endpoint at a represented
prefix is exactly the payload in the corresponding linked play round. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix_payload_eq_moveOfPlay
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (env : Nat → In₂ × In₁)
    (hpast : omegaPrefix env past.length = past)
    (hinput : env past.length = input) (row : PairedEntryRow) :
    let receiver :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
        A strategy hwin state family direction semanticMember hmember anchor
          past
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A receiver
        input.1 input.2).1
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env)
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((play past.length).2.1.target row) := by
  dsimp only
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin state activation [] default⟩
  have hround := finiteCrossAnchor_localRound_atPrefix_eq_treePlay move.2
    anchor past input env hpast hinput
  have hreceiver := congrArg (fun record => record.2.1) hround
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix,
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay,
    move] using congrArg
      (fun output =>
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (output.target row).1) hreceiver

/-- Graph-blind left endpoint at an arbitrary complete-input prefix. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (past : List (In₁ × In₂)) :
    ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A
      (BankControl A strategy hwin) :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  ⟨move, finiteCrossAnchorSenderAtPrefix move.2 past⟩

/-- Matching member-threaded left receiver at that prefix. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (past : List (In₁ × In₂)) :
    ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A
      (BankControl A strategy hwin) :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  ⟨move, finiteCrossAnchorReceiverAtPrefix move.2 anchor past⟩

/-- Operational left receive after any finite reachable prefix emits an
exact same-bank successor. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix_payload_exists
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    let receiver :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
        A strategy hwin state family direction semanticMember hmember anchor
          past
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A receiver
        input.1 input.2).1
    ∃ semanticPast semanticInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (output.target row).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) row semanticPast
                  semanticInput)) := by
  dsimp only
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin state activation [] default⟩
  let env : Nat → In₁ × In₂ :=
    DetParityAutomaton.omegaOfList (past ++ [input])
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_payload_exists
      A strategy hwin state family direction semanticMember hmember anchor env
        past.length row
  have hpast : DetParityAutomaton.omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [DetParityAutomaton.omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change DetParityAutomaton.omegaOfList (past ++ [input]) n = past[n]
      rw [DetParityAutomaton.omegaOfList_eq_getElem
        (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change DetParityAutomaton.omegaOfList (past ++ [input]) past.length = input
    rw [DetParityAutomaton.omegaOfList_eq_getElem
      (past ++ [input]) past.length hnPrefix]
    simp
  have hround := finiteCrossAnchor_localRound_atPrefix_eq_treePlay move.2
    anchor past input env hpast hinput
  have hreceiver := congrArg (fun record => record.2.1) hround
  refine ⟨semanticPast, semanticInput, ?_⟩
  rw [← hpayload]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix,
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay,
    move] using congrArg
      (fun output =>
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (output.target row).1) hreceiver

/-- Left canonical endpoint/play payload bridge. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix_payload_eq_moveOfPlay
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (env : Nat → In₁ × In₂)
    (hpast : omegaPrefix env past.length = past)
    (hinput : env past.length = input) (row : PairedEntryRow) :
    let receiver :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
        A strategy hwin state family direction semanticMember hmember anchor
          past
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A receiver
        input.1 input.2).1
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin state family direction semanticMember hmember anchor
          env)
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((play past.length).2.1.target row) := by
  dsimp only
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin state activation [] default⟩
  have hround := finiteCrossAnchor_localRound_atPrefix_eq_treePlay move.2
    anchor past input env hpast hinput
  have hreceiver := congrArg (fun record => record.2.1) hround
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix,
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay,
    move] using congrArg
      (fun output =>
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (output.target row).1) hreceiver

/-! ## Exact first and retained-second readback -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_initial_first_pair
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first : In₂ × In₁) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    let senderRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A move
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1,
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        senderRoot first.2).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
          A strategy hwin state
            (profiledRawJointRightPhysicalSiblingActivation A hwin family
              direction semanticMember hmember anchor)
            [] first,
        profiledRawJointRightSiblingSender A semanticMember [] first.2) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver]
    using
      (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_pair
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointRightSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_retained_second_pair
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
          A strategy hwin state
            (profiledRawJointRightPhysicalSiblingActivation A hwin family
              direction semanticMember hmember anchor)
            [first] second,
        profiledRawJointRightSiblingSender A semanticMember [first.2]
          second.2) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver]
    using
      (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_pair
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointRightSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first second)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_initial_first_pair
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first : In₁ × In₂) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf A
        strategy hwin state family direction semanticMember hmember
    let senderRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A move
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1,
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A senderRoot
        first.2).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
          A strategy hwin state
            (profiledRawJointLeftPhysicalSiblingActivation A hwin family
              direction semanticMember hmember anchor)
            [] first,
        profiledRawJointLeftSiblingSender A semanticMember [] first.2) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver]
    using
      (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_pair
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointLeftSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_retained_second_pair
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf A
        strategy hwin state family direction semanticMember hmember
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
          A strategy hwin state
            (profiledRawJointLeftPhysicalSiblingActivation A hwin family
              direction semanticMember hmember anchor)
            [first] second,
        profiledRawJointLeftSiblingSender A semanticMember [first.2]
          second.2) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver]
    using
      (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_pair
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointLeftSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first second)

/-! ## Exact target payload and physical projections -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_initial_first_payload
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first : In₂ × In₁) (row : PairedEntryRow) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row [] first)) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations]
    using
      (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_payload
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointRightSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first row)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_retained_second_payload
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first second : In₂ × In₁)
    (row : PairedEntryRow) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
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
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row [first] second)) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations]
    using
      (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_payload
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointRightSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first second row)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_retained_second_physical
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
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
      (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember anchor [first] second).physical := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations,
    profiledRawJointRightPhysicalSiblingReceiver]
    using
      (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_physical
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointRightSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first second)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_initial_first_payload
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first : In₁ × In₂) (row : PairedEntryRow) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf A
        strategy hwin state family direction semanticMember hmember
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        anchor
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row [] first)) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations]
    using
      (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_payload
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointLeftSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first row)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_retained_second_payload
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first second : In₁ × In₂)
    (row : PairedEntryRow) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf A
        strategy hwin state family direction semanticMember hmember
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
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row [first] second)) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations]
    using
      (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_payload
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointLeftSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first second row)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_retained_second_physical
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf A
        strategy hwin state family direction semanticMember hmember
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
      (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember anchor [first] second).physical := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations,
    profiledRawJointLeftPhysicalSiblingReceiver]
    using
      (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_physical
        A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (profiledRawJointLeftSiblingSender A semanticMember)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations_sender
          A strategy hwin family direction semanticMember hmember)
        anchor first second)

/-! ## Rebuilding a live current table without equating table alphabets -/

private abbrev OldRightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev OldLeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev LiteralAnnotation :=
  ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A

/-! ## Total finite rebuild values

The semantic-origin relation below is used only to synthesize a finite lookup
table.  Unreachable states and absent lanes still need values of the fixed
linked alphabets, so we first provide harmless payload-linked seed values from
the common world stored in the same bank entry.
-/

/-- A total right linked value for fallback branches of a finite rebuild
lookup.  Its payload table still uses the queried bank state's exact children.
-/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove
    (state : BankControl A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
      strategy hwin := by
  let world :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin state.1).world
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
  exact
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
      (fun _ : Bool ↦ activation)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state)
      (pairedRightSenderStrategy activation.lambda) (fun _ ↦ rfl)

/-- Left fallback value. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove
    (state : BankControl A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
      strategy hwin := by
  let world :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin state.1).world
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  exact
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
      (fun _ : Bool ↦ activation)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state)
      (pairedLeftSenderStrategy activation.lambda) (fun _ ↦ rfl)

/-- The old finite table and the new payload-linked table are two separate
finite values built from the same exact incoming semantic occurrence.  The
parent/source and annotation equations are retained because they are the
semantic seam used by the next child; no equality between the two table
types is asserted. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightLinkedIncomingOrigin
    (state : BankControl A strategy hwin)
    (source : HybridState A strategy)
    (oldMove : OldRightMove A)
    (linkedMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
        strategy hwin) : Prop :=
  ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
      (rawDirection : HybridDirection (In₁ := In₁) (In₂ := In₂))
      (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (familyDirection : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcOnePairedEntryRep strategy × A.State),
    ∃ member_eq : (family.semanticChild A familyDirection).right () =
        some semanticMember,
      parent.step A rawDirection = source ∧
        profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
            parent old rawDirection =
          profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin family
            familyDirection ∧
        (∀ (current : ProfiledRawJointOneSidedSemanticState A strategy
              (I := Unit)),
            source = .oneSided current →
              ∀ (currentMember : ProcOnePairedEntryRep strategy × A.State),
                current.family.right () = some currentMember →
                  ∀ (row : PairedEntryRow) (past : List (In₂ × In₁))
                      (input : In₂ × In₁),
                    (current.step A
                        (profiledRawJointUnitRightActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)).code A =
                      profiledRawJointOneSidedNext A
                        ((profiledRawJointRightSiblingFamily A family
                          familyDirection false).incidenceCode A)
                        ((profiledRawJointRightSiblingFamily A family
                          familyDirection false).move A)
                        (profiledRawJointUnitRightActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)) ∧
        oldMove = profiledRawJointRightLiteralPrefixMoveOf A strategy hwin
          family familyDirection semanticMember member_eq ∧
        linkedMove =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin state family familyDirection semanticMember
              member_eq

/-- Left mirror of the same-occurrence rebuild relation. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftLinkedIncomingOrigin
    (state : BankControl A strategy hwin)
    (source : HybridState A strategy)
    (oldMove : OldLeftMove A)
    (linkedMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
        strategy hwin) : Prop :=
  ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
      (rawDirection : HybridDirection (In₁ := In₁) (In₂ := In₂))
      (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (familyDirection : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
    ∃ member_eq : (family.semanticChild A familyDirection).left () =
        some semanticMember,
      parent.step A rawDirection = source ∧
        profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
            parent old rawDirection =
          profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin family
            familyDirection ∧
        (∀ (current : ProfiledRawJointOneSidedSemanticState A strategy
              (I := Unit)),
            source = .oneSided current →
              ∀ (currentMember : ProcTwoPairedEntryRep strategy × A.State),
                current.family.left () = some currentMember →
                  ∀ (row : PairedEntryRow) (past : List (In₁ × In₂))
                      (input : In₁ × In₂),
                    (current.step A
                        (profiledRawJointUnitLeftActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)).code A =
                      profiledRawJointOneSidedNext A
                        ((profiledRawJointLeftSiblingFamily A family
                          familyDirection false).incidenceCode A)
                        ((profiledRawJointLeftSiblingFamily A family
                          familyDirection false).move A)
                        (profiledRawJointUnitLeftActualDirection
                          (In₁ := In₁) (In₂ := In₂) row past input)) ∧
        oldMove = profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin
          family familyDirection semanticMember member_eq ∧
        linkedMove =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin state family familyDirection semanticMember
              member_eq

/-- Every present right lane at a reachable one-sided bank state supplies a
payload-linked finite table built from its exact current occurrence. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightLinkedMove_of_oneSided
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove) :
    ∃ linkedMove,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightLinkedIncomingOrigin
        A strategy hwin state
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
            strategy hwin state.1 state.2 hreachable).source
          oldMove linkedMove := by
  have horigin :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.rightIncomingOrigin
      A strategy hwin hreachable code hcode oldMove hmove
  rcases horigin with
    ⟨parent, old, rawDirection, family, familyDirection, semanticMember,
      member_eq, hsource, hannotation, haligned, hold⟩
  let linkedMove :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf A
      strategy hwin state family familyDirection semanticMember member_eq
  refine ⟨linkedMove, parent, old, rawDirection, family, familyDirection,
    semanticMember, member_eq, hsource, hannotation, haligned, hold, rfl⟩

/-- Left live-lane mirror. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftLinkedMove_of_oneSided
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove) :
    ∃ linkedMove,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftLinkedIncomingOrigin
        A strategy hwin state
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
            strategy hwin state.1 state.2 hreachable).source
          oldMove linkedMove := by
  have horigin :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.leftIncomingOrigin
      A strategy hwin hreachable code hcode oldMove hmove
  rcases horigin with
    ⟨parent, old, rawDirection, family, familyDirection, semanticMember,
      member_eq, hsource, hannotation, haligned, hold⟩
  let linkedMove :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf A
      strategy hwin state family familyDirection semanticMember member_eq
  refine ⟨linkedMove, parent, old, rawDirection, family, familyDirection,
    semanticMember, member_eq, hsource, hannotation, haligned, hold, rfl⟩

/-! ## Proof-generated finite rebuild lookup -/

/-- A reachable one-sided bank state cannot carry the fresh-root marker.
The marked invariant would otherwise identify its semantic source as common,
contradicting the stored one-sided public code. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.marker_false_of_oneSided
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code) :
    state.2.1.2.2.1 = false := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  by_contra hfalse
  have htrue : state.2.1.2.2.1 = true :=
    Bool.eq_true_of_not_eq_false hfalse
  have hmarked := packet.marked_current
  simp only [ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible,
    htrue] at hmarked
  have hsource : packet.source = .common
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world := hmarked.1
  have hsourceCode := packet.source_code
  rw [hsource, hcode] at hsourceCode
  simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode

/-- A right linked table is an admissible rebuild exactly when, at some
reachable non-root proof of this finite state, it comes from the same exact
incoming occurrence as the stored old table.  The marker guard is essential:
the common semantic graph can have simultaneous predecessors, but the marked
bank root must still select its canonical seed.  Reachability and the semantic
source are confined to `Prop`; neither is an argument of the executable lookup
below. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds
    (state : BankControl A strategy hwin) (oldMove : OldRightMove A)
    (linkedMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
        strategy hwin) : Prop :=
  state.2.1.2.2.1 = false ∧
    ∃ hreachable : BankReachable A strategy hwin state,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightLinkedIncomingOrigin
        A strategy hwin state
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
            strategy hwin state.1 state.2 hreachable).source
          oldMove linkedMove

/-- Left rebuild relation. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds
    (state : BankControl A strategy hwin) (oldMove : OldLeftMove A)
    (linkedMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
        strategy hwin) : Prop :=
  state.2.1.2.2.1 = false ∧
    ∃ hreachable : BankReachable A strategy hwin state,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftLinkedIncomingOrigin
        A strategy hwin state
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
            strategy hwin state.1 state.2 hreachable).source
          oldMove linkedMove

/-- Compile the semantic right rebuild relation into one finite lookup on the
bank state.  At absent/unreachable lanes it returns the harmless linked seed;
the specification theorem below shows that branch is never used on a live
one-sided lane. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedRightMove
    (state : BankControl A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
      strategy hwin := by
  classical
  let oldMove := state.rightMove A strategy hwin
  exact if h : ∃ linkedMove,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds A
        strategy hwin state oldMove linkedMove then
    h.choose
  else
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove
      A strategy hwin state

/-- Left finite rebuild lookup. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedLeftMove
    (state : BankControl A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
      strategy hwin := by
  classical
  let oldMove := state.leftMove A strategy hwin
  exact if h : ∃ linkedMove,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds A
        strategy hwin state oldMove linkedMove then
    h.choose
  else
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove
      A strategy hwin state

/-! ## Canonical marked-root lookup -/

/-- The freshness bit of a marked bank root is literally `true`. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_marker
    (control :
      ProfiledRawJointHybridCommonControl A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control).2.1.2.2.1 = true := by
  change
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
      hwin control).run []).1.2.2.1 = true
  have hroot := congrArg Prod.fst
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
      A strategy hwin control)
  change
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
      hwin control).run []).1.2.2.1 = true at hroot
  exact hroot

/-- At the marked root the executable right lookup cannot use a predecessor
rebuild and therefore returns the canonical payload-linked seed. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_linkedRightMove_eq_fallback
    (control :
      ProfiledRawJointHybridCommonControl A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control).linkedRightMove A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) := by
  classical
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  have hmarker : state.2.1.2.2.1 = true :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_marker A
      strategy hwin control
  have hnone : ¬ ∃ linkedMove,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds A
        strategy hwin state (state.rightMove A strategy hwin) linkedMove := by
    rintro ⟨linkedMove, hfalse, _hrebuild⟩
    rw [hmarker] at hfalse
    contradiction
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedRightMove]
  split
  · rename_i h
    exact False.elim (hnone h)
  · rfl

/-- Left marked-root lookup mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_linkedLeftMove_eq_fallback
    (control :
      ProfiledRawJointHybridCommonControl A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control).linkedLeftMove A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) := by
  classical
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  have hmarker : state.2.1.2.2.1 = true :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_marker A
      strategy hwin control
  have hnone : ¬ ∃ linkedMove,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds A
        strategy hwin state (state.leftMove A strategy hwin) linkedMove := by
    rintro ⟨linkedMove, hfalse, _hrebuild⟩
    rw [hmarker] at hfalse
    contradiction
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedLeftMove]
  split
  · rename_i h
    exact False.elim (hnone h)
  · rfl

/-- The canonical payload-linked right seed emits the exact enriched first
record of the common occurrence stored at the queried bank entry. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove_initial_first_pair
    (state : BankControl A strategy hwin)
    (anchor : Bool) (first : In₂ × In₁) :
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactRightUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove
        A strategy hwin state
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
          activation children [] first,
        pairedRightSenderStrategy activation.lambda [] first.2) := by
  dsimp only
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove]
    using
      (profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_pair
        A (fun _ : Bool ↦
          profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                A strategy hwin state.1).world))
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                A strategy hwin state.1).world)).lambda)
        (fun _ ↦ rfl) anchor first)

/-- Canonical payload-linked left seed mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove_initial_first_pair
    (state : BankControl A strategy hwin)
    (anchor : Bool) (first : In₁ × In₂) :
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactLeftUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove
        A strategy hwin state
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
          activation children [] first,
        pairedLeftSenderStrategy activation.lambda [] first.2) := by
  dsimp only
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove]
    using
      (profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_pair
        A (fun _ : Bool ↦
          profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                A strategy hwin state.1).world))
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
        (pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                A strategy hwin state.1).world)).lambda)
        (fun _ ↦ rfl) anchor first)

/-- On a live one-sided right lane, the executable lookup is certified to be
a same-occurrence rebuild of the literally stored table. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedRightMove_rebuilds_of_oneSided
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds A
      strategy hwin state oldMove
        (state.linkedRightMove A strategy hwin) := by
  obtain ⟨linkedMove, hlinked⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightLinkedMove_of_oneSided
      A strategy hwin hreachable code hcode oldMove hmove
  have hold : state.rightMove A strategy hwin = oldMove :=
    state.rightMove_eq_of_some A strategy hwin oldMove hmove
  have hexists : ∃ candidate,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds A
        strategy hwin state oldMove candidate :=
    ⟨linkedMove,
      state.marker_false_of_oneSided A strategy hwin hreachable code hcode,
      hreachable, hlinked⟩
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedRightMove]
  rw [hold]
  simp only [dif_pos hexists]
  exact Classical.choose_spec hexists

/-- Left live-lane lookup specification. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedLeftMove_rebuilds_of_oneSided
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds A
      strategy hwin state oldMove
        (state.linkedLeftMove A strategy hwin) := by
  obtain ⟨linkedMove, hlinked⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftLinkedMove_of_oneSided
      A strategy hwin hreachable code hcode oldMove hmove
  have hold : state.leftMove A strategy hwin = oldMove :=
    state.leftMove_eq_of_some A strategy hwin oldMove hmove
  have hexists : ∃ candidate,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds A
        strategy hwin state oldMove candidate :=
    ⟨linkedMove,
      state.marker_false_of_oneSided A strategy hwin hreachable code hcode,
      hreachable, hlinked⟩
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.linkedLeftMove]
  rw [hold]
  simp only [dif_pos hexists]
  exact Classical.choose_spec hexists

end

end DetParityAutomaton

end DistributedSynthesis
