/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFinitePayloadLinkedTargetMove

/-!
# Finite sibling tables carrying an arbitrary pre-narrowed payload

This file applies the repository's unconditional root-family narrowing to the
generic pre-narrowing enrichment.  The finite descriptor stores only a source
slot and the truth table of the exact semantic image.  Every emitted target
therefore has a literal `(row, past, input)` witness and its payload is the
value of `children` at that witness's actual raw direction.

The construction contains no post-narrowing representative or candidate
selection.  No runtime transition receives a graph, hierarchy side, leader
bit, strict-leader bit, semantic history, or view.

The standalone root-family table wrapper below is intentionally retained as
a right-only exploratory scaffold; it is not the recurring operational
table.  The symmetric API in this file supplies the exact right/left
descriptors and receivers consumed by
`LemPairedProfiledRawJointHybridFinitePayloadLiteralPrefixMove`, whose
two-member cross-anchor constructor is the reusable operational route.
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

private abbrev LinkedTarget (Payload : Type p) :=
  ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload

/-! ## Right blocks -/

/-- Finite data on which one payload-linked right block depends. -/
structure ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor
    (Payload : Type p) where
  source : ProfiledRawRightSlot A
  allowed : LinkedTarget A Payload → Bool

noncomputable instance
    {Payload : Type p} [Fintype Payload] :
    Fintype
      (ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload) := by
  classical
  let Rep := ProfiledRawRightSlot A × (LinkedTarget A Payload → Bool)
  let equivalence :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload ≃
        Rep := {
    toFun := fun descriptor ↦ (descriptor.source, descriptor.allowed)
    invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
    left_inv := by intro descriptor; cases descriptor; rfl
    right_inv := by intro descriptor; cases descriptor; rfl
  }
  exact Fintype.ofEquiv Rep equivalence.symm

def profiledRawJointRightFinitePayloadLinkedSiblingAllowed
    {Payload : Type p}
    (descriptor :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload)
    (target : LinkedTarget A Payload) : Prop :=
  descriptor.allowed target = true

noncomputable instance
    {Payload : Type p}
    (descriptor :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload) :
    DecidablePred
      (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor) :=
  fun _ ↦ Classical.propDecidable _

noncomputable abbrev
    profiledRawJointRightFinitePayloadLinkedSiblingMonitor
    {Payload : Type p} [Fintype Payload]
    (descriptor :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload)
    (_member : Bool) :=
  profiledRawJointHybridFinitePayloadRowExactRightBlockMonitor A
    (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source

/-- One finite right move obtained by unconditional universal-thread
narrowing. -/
noncomputable abbrev ProfiledRawJointRightFinitePayloadLinkedSiblingMove
    (Payload : Type p) [Fintype Payload] :=
  Sigma fun descriptor :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload ↦
    { table : FiniteRootFamilyTable
        (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor) //
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor))
        table.toTransitionRationalTree.labeledTree }

noncomputable instance
    {Payload : Type p} [Fintype Payload] :
    Fintype (ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload) := by
  classical
  infer_instance

noncomputable def
    ProfiledRawJointRightFinitePayloadLinkedSiblingMove.memberController
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload)
    (member : Bool) :=
  finiteRootMemberController
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree member

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem
    ProfiledRawJointRightFinitePayloadLinkedSiblingMove.memberController_sender_eq
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload)
    (left right : Bool) (word : List In₁) :
    ((move.memberController A left).labeledTree word).1 =
      ((move.memberController A right).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree left right word

theorem
    ProfiledRawJointRightFinitePayloadLinkedSiblingMove.memberController_wins
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload)
    (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1 member)
      (move.memberController A member).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree move.2.2 member

/-- The projected member play wins the original target monitor. -/
theorem
    ProfiledRawJointRightFinitePayloadLinkedSiblingMove.memberController_projectedWins
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload)
    (member : Bool) (env : Nat → In₂ × In₁) :
    let linkedMonitor :=
      profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree linkedMonitor controller.labeledTree) env
    let base := profiledRawJointTargetRightBlockMonitor A
      (LinkedTarget A Payload)
      (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
      (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A move.1)
      move.1.source
    base.WinsPlay
      (BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        play) := by
  dsimp only
  let linkedMonitor :=
    profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let tree := narrowedInducedTree linkedMonitor controller.labeledTree
  let play := treePlay tree env
  have htree : linkedMonitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin linkedMonitor
      (move.memberController_wins A member)
  have hplay : linkedMonitor.WinsPlay play :=
    (linkedMonitor.lift_winningTree_iff tree).mp htree env
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointTargetRightBlockMonitor A (LinkedTarget A Payload)
      (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
      (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A move.1)
      move.1.source)
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
    play).mp hplay

/-- Every right table target is physically safe, belongs to its descriptor's
exact image, and retains the queried row. -/
theorem
    ProfiledRawJointRightFinitePayloadLinkedSiblingMove.memberController_targetSafe
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let linkedMonitor :=
      profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let linkedPlay := treePlay
      (narrowedInducedTree linkedMonitor controller.labeledTree) env
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
    erasePairedProfiledState A
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A
          (((profiledRawJointTargetRightBlockMonitor A
            (LinkedTarget A Payload)
            (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
            (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A move.1)
            move.1.source).run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      profiledRawJointRightFinitePayloadLinkedSiblingAllowed A move.1
        ((play n).2.1.target row) ∧
      profiledRawJointHybridFinitePayloadLinkedTargetRow A
        ((play n).2.1.target row) = row := by
  dsimp only
  let linkedMonitor :=
    profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let linkedPlay := treePlay
    (narrowedInducedTree linkedMonitor controller.labeledTree) env
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
    linkedPlay
  have hwin :
      (profiledRawJointTargetRightBlockMonitor A (LinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A move.1)
        move.1.source).WinsPlay play :=
    move.memberController_projectedWins A member env
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
    (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A move.1)
    move.1.source play hwin n row
  refine ⟨hsafe.1, hsafe.2, ?_⟩
  exact
    profiledRawJointHybridFinitePayloadRowExactRightTarget_row A
      (linkedPlay n).2.1 row

end

/-! ### Exact semantic materialization -/

noncomputable def profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload) :
    ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A Payload := by
  classical
  exact {
    source := source
    allowed := fun target ↦ decide
      (ProfiledRawJointRightFinitePayloadLinkedTargetAllowed A activation
        children target)
  }

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf_allowed_iff
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (target : LinkedTarget A Payload) :
    profiledRawJointRightFinitePayloadLinkedSiblingAllowed A
        (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
          activation children) target ↔
      ProfiledRawJointRightFinitePayloadLinkedTargetAllowed A activation
        children target := by
  simp [profiledRawJointRightFinitePayloadLinkedSiblingAllowed,
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf]

/-- Re-express the exact enrichment under its materialized finite truth
table. -/
noncomputable def profiledRawJointRightFinitePayloadLinkedSiblingActivation
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload) :
    ProfiledRawJointTargetRightBlockActivation A (LinkedTarget A Payload)
      (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
      (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A
        (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
          activation children))
      source := by
  let linked := activation.linkFinitePayload A children
  exact {
    lambda := linked.lambda
    initial_profile := linked.initial_profile
    forever := linked.forever
    target := linked.target
    target_allowed := fun row past input ↦
      (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf_allowed_iff
        A activation children _).mpr (linked.target_allowed row past input)
    target_state := linked.target_state
  }

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointRightFinitePayloadLinkedSiblingActivation_target_row
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    profiledRawJointHybridFinitePayloadLinkedTargetRow A
        ((profiledRawJointRightFinitePayloadLinkedSiblingActivation A
          activation children).target row past input) = row :=
  rfl

def profiledRawJointRightFinitePayloadLinkedSiblingReceiver
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload) :=
  profiledRawJointHybridFinitePayloadRowExactRightReceiverStrategy A
    (profiledRawJointRightFinitePayloadLinkedSiblingActivation A activation
      children)
    (profiledRawJointRightFinitePayloadLinkedSiblingActivation_target_row A
      activation children)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointRightFinitePayloadLinkedSiblingReceiver_physical
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointRightFinitePayloadLinkedSiblingReceiver A activation
      children past input).physical =
      (profiledRawJointTargetRightReceiverStrategy A activation past
        input).physical :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointRightFinitePayloadLinkedSiblingReceiver_payload
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((profiledRawJointRightFinitePayloadLinkedSiblingReceiver A activation
          children past input).target row).1 =
      children (.strict
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightFinitePayloadLinkedSiblingMonitor_realizable
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (member : Bool) (env : Nat → In₂ × In₁) :
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A
      (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
        children)
      member).WinsPlay
      (pairPlay
        (profiledRawJointRightFinitePayloadLinkedSiblingReceiver A activation
          children)
        (pairedRightSenderStrategy activation.lambda) env) := by
  exact
    profiledRawJointHybridFinitePayloadRowExactRightBlockMonitor_realizable A
      (profiledRawJointRightFinitePayloadLinkedSiblingActivation A activation
        children)
      (profiledRawJointRightFinitePayloadLinkedSiblingActivation_target_row A
        activation children)
      env

/-- Unconditionally narrow the exact payload-enriched semantic receiver. -/
noncomputable def profiledRawJointRightFinitePayloadLinkedSiblingMoveOf
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload) :
    ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload := by
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      children
  let receiver :=
    profiledRawJointRightFinitePayloadLinkedSiblingReceiver A activation
      children
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) :=
    ⟨receiver [] default⟩
  let table := finiteRootFamilyTable
    (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor)
    (fun _member ↦ receiver)
    (pairedRightSenderStrategy activation.lambda)
    (fun member env ↦
      profiledRawJointRightFinitePayloadLinkedSiblingMonitor_realizable A
        activation children member env)
  exact ⟨descriptor, table,
    finiteRootFamilyTable_wins
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor)
      (fun _member ↦ receiver)
      (pairedRightSenderStrategy activation.lambda)
      (fun member env ↦
        profiledRawJointRightFinitePayloadLinkedSiblingMonitor_realizable A
          activation children member env)⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Eliminate target safety at an exact descriptor: every queried target has
an actual semantic `(past,input)` witness at the queried row, and hence its
payload is the corresponding `children actualDirection`. -/
theorem
    ProfiledRawJointRightFinitePayloadLinkedSiblingMove.memberController_target_exists
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (move : ProfiledRawJointRightFinitePayloadLinkedSiblingMove A Payload)
    (hdescriptor : move.1 =
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
        children)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let linkedMonitor :=
      profiledRawJointRightFinitePayloadLinkedSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let linkedPlay := treePlay
      (narrowedInducedTree linkedMonitor controller.labeledTree) env
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
    ∃ past input,
      (play n).2.1.target row =
        (activation.target row past input,
          (row,
            children (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) row past input)))) := by
  dsimp only
  have hsafe := move.memberController_targetSafe A member env n row
  have hallowed := hsafe.2.1
  have hrow := hsafe.2.2
  generalize htarget :
      ((BlockRecordMonitor.projectReceiverPlay
          (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
          (treePlay
            (narrowedInducedTree
              (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A
                move.1 member)
              (move.memberController A member).labeledTree)
            env) n).2.1.target row) = target at hallowed hrow ⊢
  have hallowed' :
      profiledRawJointRightFinitePayloadLinkedSiblingAllowed A
        (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
          activation children) target := by
    rw [← hdescriptor]
    exact hallowed
  have himage :=
    (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf_allowed_iff A
      activation children _).mp hallowed'
  rcases himage with ⟨witnessRow, past, input, hsemantic⟩
  rw [hsemantic] at hrow
  change witnessRow = row at hrow
  subst witnessRow
  exact ⟨past, input, hsemantic⟩

/-! ## Left blocks: the cross-ready semantic mirror

The root-family materialization above is currently needed only on the right.
For the two-record literal-prefix construction, however, both orientations
need the same finite descriptor, exact activation, and realizability API.  We
therefore expose the left semantic mirror here without duplicating the
root-family table wrapper.
-/

/-- Finite data on which one payload-linked left block depends. -/
structure ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor
    (Payload : Type p) where
  source : ProfiledRawLeftSlot A
  allowed : LinkedTarget A Payload → Bool

noncomputable instance
    {Payload : Type p} [Fintype Payload] :
    Fintype
      (ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A Payload) := by
  classical
  let Rep := ProfiledRawLeftSlot A × (LinkedTarget A Payload → Bool)
  let equivalence :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A Payload ≃
        Rep := {
    toFun := fun descriptor ↦ (descriptor.source, descriptor.allowed)
    invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
    left_inv := by intro descriptor; cases descriptor; rfl
    right_inv := by intro descriptor; cases descriptor; rfl
  }
  exact Fintype.ofEquiv Rep equivalence.symm

def profiledRawJointLeftFinitePayloadLinkedSiblingAllowed
    {Payload : Type p}
    (descriptor :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A Payload)
    (target : LinkedTarget A Payload) : Prop :=
  descriptor.allowed target = true

noncomputable instance
    {Payload : Type p}
    (descriptor :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A Payload) :
    DecidablePred
      (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor) :=
  fun _ ↦ Classical.propDecidable _

noncomputable abbrev
    profiledRawJointLeftFinitePayloadLinkedSiblingMonitor
    {Payload : Type p} [Fintype Payload]
    (descriptor :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A Payload)
    (_member : Bool) :=
  profiledRawJointHybridFinitePayloadRowExactLeftBlockMonitor A
    (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source

noncomputable def profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload) :
    ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A Payload := by
  classical
  exact {
    source := source
    allowed := fun target ↦ decide
      (ProfiledRawJointLeftFinitePayloadLinkedTargetAllowed A activation
        children target)
  }

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf_allowed_iff
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (target : LinkedTarget A Payload) :
    profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A
        (profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
          activation children) target ↔
      ProfiledRawJointLeftFinitePayloadLinkedTargetAllowed A activation
        children target := by
  simp [profiledRawJointLeftFinitePayloadLinkedSiblingAllowed,
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf]

/-- Re-express the exact left enrichment under its materialized finite truth
table. -/
noncomputable def profiledRawJointLeftFinitePayloadLinkedSiblingActivation
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload) :
    ProfiledRawJointTargetLeftBlockActivation A (LinkedTarget A Payload)
      (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
      (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A
        (profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
          activation children))
      source := by
  let linked := activation.linkFinitePayload A children
  exact {
    lambda := linked.lambda
    initial_profile := linked.initial_profile
    forever := linked.forever
    target := linked.target
    target_allowed := fun row past input ↦
      (profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf_allowed_iff
        A activation children _).mpr (linked.target_allowed row past input)
    target_state := linked.target_state
  }

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointLeftFinitePayloadLinkedSiblingActivation_target_row
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    profiledRawJointHybridFinitePayloadLinkedTargetRow A
        ((profiledRawJointLeftFinitePayloadLinkedSiblingActivation A
          activation children).target row past input) = row :=
  rfl

def profiledRawJointLeftFinitePayloadLinkedSiblingReceiver
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload) :=
  profiledRawJointHybridFinitePayloadRowExactLeftReceiverStrategy A
    (profiledRawJointLeftFinitePayloadLinkedSiblingActivation A activation
      children)
    (profiledRawJointLeftFinitePayloadLinkedSiblingActivation_target_row A
      activation children)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointLeftFinitePayloadLinkedSiblingReceiver_physical
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A activation
      children past input).physical =
      (profiledRawJointTargetLeftReceiverStrategy A activation past
        input).physical :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointLeftFinitePayloadLinkedSiblingReceiver_payload
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A activation
          children past input).target row).1 =
      children (.strict
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftFinitePayloadLinkedSiblingMonitor_realizable
    {Payload : Type p} [Fintype Payload]
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Payload)
    (member : Bool) (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A
      (profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
        children)
      member).WinsPlay
      (pairPlay
        (profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A activation
          children)
        (pairedLeftSenderStrategy activation.lambda) env) := by
  exact
    profiledRawJointHybridFinitePayloadRowExactLeftBlockMonitor_realizable A
      (profiledRawJointLeftFinitePayloadLinkedSiblingActivation A activation
        children)
      (profiledRawJointLeftFinitePayloadLinkedSiblingActivation_target_row A
        activation children)
      env

end

end DetParityAutomaton

end DistributedSynthesis
