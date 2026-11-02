/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalLinkedTargetMove

/-!
# Finite sibling moves obtained from exact parent-linked targets

This is the operational half of the parent-linked carrier repair.  We first
attach the literal row and the child annotation selected by the same semantic
parent move.  Only then do we materialize its finite image and apply the
unconditional root-family narrowing theorem.  Thus no post-narrowing lookup
from a bare target is used.

The finite descriptor contains only a source slot and a Boolean truth table
on the finite linked target alphabet.  It contains no graph, orientation,
side, leader bit, strict-leader bit, semantic history, view, or policy state.
The two proof-side sibling members are projections of one finite family table;
their sender control and sender output are therefore shared.
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

private abbrev LinkedTarget :=
  ProfiledRawJointHybridPhysicalLinkedTarget A

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

/-! ## Right blocks -/

/-- Finite data on which one exact linked right block depends. -/
structure ProfiledRawJointRightPhysicalLinkedSiblingDescriptor where
  source : ProfiledRawRightSlot A
  allowed : LinkedTarget A → Bool

noncomputable instance :
    Fintype (ProfiledRawJointRightPhysicalLinkedSiblingDescriptor A) := by
  classical
  let Rep := ProfiledRawRightSlot A × (LinkedTarget A → Bool)
  let equivalence :
      ProfiledRawJointRightPhysicalLinkedSiblingDescriptor A ≃ Rep := {
    toFun := fun descriptor ↦ (descriptor.source, descriptor.allowed)
    invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
    left_inv := by intro descriptor; cases descriptor; rfl
    right_inv := by intro descriptor; cases descriptor; rfl
  }
  exact Fintype.ofEquiv Rep equivalence.symm

def profiledRawJointRightPhysicalLinkedSiblingAllowed
    (descriptor : ProfiledRawJointRightPhysicalLinkedSiblingDescriptor A)
    (target : LinkedTarget A) : Prop :=
  descriptor.allowed target = true

noncomputable instance
    (descriptor : ProfiledRawJointRightPhysicalLinkedSiblingDescriptor A) :
    DecidablePred
      (profiledRawJointRightPhysicalLinkedSiblingAllowed A descriptor) :=
  fun _ ↦ Classical.propDecidable _

/-- The same linked monitor at both proof-side sibling roots. -/
noncomputable abbrev profiledRawJointRightPhysicalLinkedSiblingMonitor
    (descriptor : ProfiledRawJointRightPhysicalLinkedSiblingDescriptor A)
    (_member : Bool) :=
  profiledRawJointHybridPhysicalRowExactRightBlockMonitor A
    (profiledRawJointRightPhysicalLinkedSiblingAllowed A descriptor)
    descriptor.source

/-- One finite linked sibling move. -/
noncomputable abbrev ProfiledRawJointRightPhysicalLinkedSiblingMove :=
  Sigma fun descriptor :
      ProfiledRawJointRightPhysicalLinkedSiblingDescriptor A ↦
    { table : FiniteRootFamilyTable
        (profiledRawJointRightPhysicalLinkedSiblingMonitor A descriptor) //
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRawJointRightPhysicalLinkedSiblingMonitor A descriptor))
        table.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (ProfiledRawJointRightPhysicalLinkedSiblingMove A) := by
  classical
  infer_instance

/-- Read one proof-side member.  The member is absent from the transition and
sender control and selects only a receiver component of the common table. -/
noncomputable def
    ProfiledRawJointRightPhysicalLinkedSiblingMove.memberController
    (move : ProfiledRawJointRightPhysicalLinkedSiblingMove A)
    (member : Bool) :=
  finiteRootMemberController
    (profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree member

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem
    ProfiledRawJointRightPhysicalLinkedSiblingMove.memberController_control_eq
    (move : ProfiledRawJointRightPhysicalLinkedSiblingMove A)
    (left right : Bool) (word : List In₁) :
    (move.memberController A left).controlAt word =
      (move.memberController A right).controlAt word := by
  exact finiteRootMemberController_control_eq
    (profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree left right word

theorem
    ProfiledRawJointRightPhysicalLinkedSiblingMove.memberController_sender_eq
    (move : ProfiledRawJointRightPhysicalLinkedSiblingMove A)
    (left right : Bool) (word : List In₁) :
    ((move.memberController A left).labeledTree word).1 =
      ((move.memberController A right).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree left right word

theorem
    ProfiledRawJointRightPhysicalLinkedSiblingMove.memberController_wins
    (move : ProfiledRawJointRightPhysicalLinkedSiblingMove A)
    (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1 member)
      (move.memberController A member).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree move.2.2 member

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Projecting a linked member play gives a winning play of the exact old
target monitor.  This is the bridge used by target safety and the fresh
state/block-priority theorem. -/
theorem
    ProfiledRawJointRightPhysicalLinkedSiblingMove.memberController_projectedWins
    (move : ProfiledRawJointRightPhysicalLinkedSiblingMove A)
    (member : Bool) (env : Nat → In₂ × In₁) :
    let linkedMonitor :=
      profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree linkedMonitor controller.labeledTree) env
    let base := profiledRawJointTargetRightBlockMonitor A (LinkedTarget A)
      (profiledRawJointHybridPhysicalLinkedRightTargetProjection A)
      (profiledRawJointRightPhysicalLinkedSiblingAllowed A move.1)
      move.1.source
    base.WinsPlay
      (BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointHybridPhysicalRowExactRightReceiverProjection A)
        play) := by
  dsimp only
  let linkedMonitor :=
    profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let tree := narrowedInducedTree linkedMonitor controller.labeledTree
  let play := treePlay tree env
  have htree : linkedMonitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin linkedMonitor
      (move.memberController_wins A member)
  have hplay : linkedMonitor.WinsPlay play :=
    (linkedMonitor.lift_winningTree_iff tree).mp htree env
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointTargetRightBlockMonitor A (LinkedTarget A)
      (profiledRawJointHybridPhysicalLinkedRightTargetProjection A)
      (profiledRawJointRightPhysicalLinkedSiblingAllowed A move.1)
      move.1.source)
    (profiledRawJointHybridPhysicalRowExactRightReceiverProjection A)
    play).mp hplay

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every linked right table cell is the literal physical close, belongs to
the finite linked image, and carries its queried row. -/
theorem
    ProfiledRawJointRightPhysicalLinkedSiblingMove.memberController_targetSafe
    (move : ProfiledRawJointRightPhysicalLinkedSiblingMove A)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let linkedMonitor :=
      profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let linkedPlay := treePlay
      (narrowedInducedTree linkedMonitor controller.labeledTree) env
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridPhysicalRowExactRightReceiverProjection A)
      linkedPlay
    erasePairedProfiledState A
        (profiledRawJointHybridPhysicalLinkedRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A
          (((profiledRawJointTargetRightBlockMonitor A (LinkedTarget A)
            (profiledRawJointHybridPhysicalLinkedRightTargetProjection A)
            (profiledRawJointRightPhysicalLinkedSiblingAllowed A move.1)
            move.1.source).run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      profiledRawJointRightPhysicalLinkedSiblingAllowed A move.1
        ((play n).2.1.target row) ∧
      profiledRawJointHybridPhysicalLinkedTargetRow A
        ((play n).2.1.target row) = row := by
  dsimp only
  let linkedMonitor :=
    profiledRawJointRightPhysicalLinkedSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let linkedPlay := treePlay
    (narrowedInducedTree linkedMonitor controller.labeledTree) env
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridPhysicalRowExactRightReceiverProjection A)
    linkedPlay
  have hwin :
      (profiledRawJointTargetRightBlockMonitor A (LinkedTarget A)
        (profiledRawJointHybridPhysicalLinkedRightTargetProjection A)
        (profiledRawJointRightPhysicalLinkedSiblingAllowed A move.1)
        move.1.source).WinsPlay play :=
    move.memberController_projectedWins A member env
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A
    (profiledRawJointHybridPhysicalLinkedRightTargetProjection A)
    (profiledRawJointRightPhysicalLinkedSiblingAllowed A move.1)
    move.1.source play hwin n row
  refine ⟨hsafe.1, hsafe.2, ?_⟩
  exact
    profiledRawJointHybridPhysicalRowExactRightTarget_row A
      (linkedPlay n).2.1 row

/-! ### Exact semantic construction -/

/-- Materialize the finite image of an exact parent-linked activation. -/
noncomputable def profiledRawJointRightPhysicalLinkedSiblingDescriptorOf
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :
    ProfiledRawJointRightPhysicalLinkedSiblingDescriptor A := by
  classical
  exact {
    source := source
    allowed := fun target ↦ decide
      (ProfiledRawJointRightLinkedTargetAllowed A activation children target)
  }

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightPhysicalLinkedSiblingDescriptorOf_allowed_iff
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A)
    (target : LinkedTarget A) :
    profiledRawJointRightPhysicalLinkedSiblingAllowed A
        (profiledRawJointRightPhysicalLinkedSiblingDescriptorOf A activation
          children) target ↔
      ProfiledRawJointRightLinkedTargetAllowed A activation children target := by
  simp [profiledRawJointRightPhysicalLinkedSiblingAllowed,
    profiledRawJointRightPhysicalLinkedSiblingDescriptorOf]

/-- Re-express the exact linked activation under its finite truth table. -/
noncomputable def profiledRawJointRightPhysicalLinkedSiblingActivation
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :
    ProfiledRawJointTargetRightBlockActivation A (LinkedTarget A)
      (profiledRawJointHybridPhysicalLinkedRightTargetProjection A)
      (profiledRawJointRightPhysicalLinkedSiblingAllowed A
        (profiledRawJointRightPhysicalLinkedSiblingDescriptorOf A activation
          children)) source := by
  let linked := activation.linkPhysicalAnnotation A children
  exact {
    lambda := linked.lambda
    initial_profile := linked.initial_profile
    forever := linked.forever
    target := linked.target
    target_allowed := fun row past input ↦
      (profiledRawJointRightPhysicalLinkedSiblingDescriptorOf_allowed_iff A
        activation children _).mpr (linked.target_allowed row past input)
    target_state := linked.target_state
  }

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointRightPhysicalLinkedSiblingActivation_target_row
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    profiledRawJointHybridPhysicalLinkedTargetRow A
        ((profiledRawJointRightPhysicalLinkedSiblingActivation A activation
          children).target row past input) = row :=
  rfl

/-- The exact linked receiver in the row-subtyped alphabet. -/
def profiledRawJointRightPhysicalLinkedSiblingReceiver
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :=
  profiledRawJointHybridPhysicalRowExactRightReceiverStrategy A
    (profiledRawJointRightPhysicalLinkedSiblingActivation A activation
      children)
    (profiledRawJointRightPhysicalLinkedSiblingActivation_target_row A
      activation children)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightPhysicalLinkedSiblingMonitor_realizable
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A)
    (member : Bool) (env : Nat → In₂ × In₁) :
    (profiledRawJointRightPhysicalLinkedSiblingMonitor A
      (profiledRawJointRightPhysicalLinkedSiblingDescriptorOf A activation
        children) member).WinsPlay
      (pairPlay
        (profiledRawJointRightPhysicalLinkedSiblingReceiver A activation
          children)
        (pairedRightSenderStrategy activation.lambda) env) := by
  exact profiledRawJointHybridPhysicalRowExactRightBlockMonitor_realizable A
    (profiledRawJointRightPhysicalLinkedSiblingActivation A activation
      children)
    (profiledRawJointRightPhysicalLinkedSiblingActivation_target_row A
      activation children) env

/-- Unconditionally narrow the exact linked semantic receiver. -/
noncomputable def profiledRawJointRightPhysicalLinkedSiblingMoveOf
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :
    ProfiledRawJointRightPhysicalLinkedSiblingMove A := by
  let descriptor :=
    profiledRawJointRightPhysicalLinkedSiblingDescriptorOf A activation
      children
  let receiver :=
    profiledRawJointRightPhysicalLinkedSiblingReceiver A activation children
  letI : Inhabited
      (ProfiledRawJointHybridPhysicalRowExactRightReceiverOutput A) :=
    ⟨receiver [] default⟩
  let table := finiteRootFamilyTable
    (profiledRawJointRightPhysicalLinkedSiblingMonitor A descriptor)
    (fun _member ↦ receiver)
    (pairedRightSenderStrategy activation.lambda)
    (fun member env ↦
      profiledRawJointRightPhysicalLinkedSiblingMonitor_realizable A
        activation children member env)
  exact ⟨descriptor, table,
    finiteRootFamilyTable_wins
      (profiledRawJointRightPhysicalLinkedSiblingMonitor A descriptor)
      (fun _member ↦ receiver)
      (pairedRightSenderStrategy activation.lambda)
      (fun member env ↦
        profiledRawJointRightPhysicalLinkedSiblingMonitor_realizable A
          activation children member env)⟩

/-! ## Left blocks -/

/-- Finite mirror descriptor. -/
structure ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor where
  source : ProfiledRawLeftSlot A
  allowed : LinkedTarget A → Bool

noncomputable instance :
    Fintype (ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor A) := by
  classical
  let Rep := ProfiledRawLeftSlot A × (LinkedTarget A → Bool)
  let equivalence :
      ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor A ≃ Rep := {
    toFun := fun descriptor ↦ (descriptor.source, descriptor.allowed)
    invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
    left_inv := by intro descriptor; cases descriptor; rfl
    right_inv := by intro descriptor; cases descriptor; rfl
  }
  exact Fintype.ofEquiv Rep equivalence.symm

def profiledRawJointLeftPhysicalLinkedSiblingAllowed
    (descriptor : ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor A)
    (target : LinkedTarget A) : Prop :=
  descriptor.allowed target = true

noncomputable instance
    (descriptor : ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor A) :
    DecidablePred
      (profiledRawJointLeftPhysicalLinkedSiblingAllowed A descriptor) :=
  fun _ ↦ Classical.propDecidable _

noncomputable abbrev profiledRawJointLeftPhysicalLinkedSiblingMonitor
    (descriptor : ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor A)
    (_member : Bool) :=
  profiledRawJointHybridPhysicalRowExactLeftBlockMonitor A
    (profiledRawJointLeftPhysicalLinkedSiblingAllowed A descriptor)
    descriptor.source

noncomputable abbrev ProfiledRawJointLeftPhysicalLinkedSiblingMove :=
  Sigma fun descriptor :
      ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor A ↦
    { table : FiniteRootFamilyTable
        (profiledRawJointLeftPhysicalLinkedSiblingMonitor A descriptor) //
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRawJointLeftPhysicalLinkedSiblingMonitor A descriptor))
        table.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (ProfiledRawJointLeftPhysicalLinkedSiblingMove A) := by
  classical
  infer_instance

noncomputable def
    ProfiledRawJointLeftPhysicalLinkedSiblingMove.memberController
    (move : ProfiledRawJointLeftPhysicalLinkedSiblingMove A)
    (member : Bool) :=
  finiteRootMemberController
    (profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree member

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem
    ProfiledRawJointLeftPhysicalLinkedSiblingMove.memberController_control_eq
    (move : ProfiledRawJointLeftPhysicalLinkedSiblingMove A)
    (left right : Bool) (word : List In₂) :
    (move.memberController A left).controlAt word =
      (move.memberController A right).controlAt word := by
  exact finiteRootMemberController_control_eq
    (profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree left right word

theorem
    ProfiledRawJointLeftPhysicalLinkedSiblingMove.memberController_sender_eq
    (move : ProfiledRawJointLeftPhysicalLinkedSiblingMove A)
    (left right : Bool) (word : List In₂) :
    ((move.memberController A left).labeledTree word).1 =
      ((move.memberController A right).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree left right word

theorem
    ProfiledRawJointLeftPhysicalLinkedSiblingMove.memberController_wins
    (move : ProfiledRawJointLeftPhysicalLinkedSiblingMove A)
    (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1 member)
      (move.memberController A member).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree move.2.2 member

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointLeftPhysicalLinkedSiblingMove.memberController_projectedWins
    (move : ProfiledRawJointLeftPhysicalLinkedSiblingMove A)
    (member : Bool) (env : Nat → In₁ × In₂) :
    let linkedMonitor :=
      profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree linkedMonitor controller.labeledTree) env
    let base := profiledRawJointTargetLeftBlockMonitor A (LinkedTarget A)
      (profiledRawJointHybridPhysicalLinkedLeftTargetProjection A)
      (profiledRawJointLeftPhysicalLinkedSiblingAllowed A move.1)
      move.1.source
    base.WinsPlay
      (BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointHybridPhysicalRowExactLeftReceiverProjection A)
        play) := by
  dsimp only
  let linkedMonitor :=
    profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let tree := narrowedInducedTree linkedMonitor controller.labeledTree
  let play := treePlay tree env
  have htree : linkedMonitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin linkedMonitor
      (move.memberController_wins A member)
  have hplay : linkedMonitor.WinsPlay play :=
    (linkedMonitor.lift_winningTree_iff tree).mp htree env
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointTargetLeftBlockMonitor A (LinkedTarget A)
      (profiledRawJointHybridPhysicalLinkedLeftTargetProjection A)
      (profiledRawJointLeftPhysicalLinkedSiblingAllowed A move.1)
      move.1.source)
    (profiledRawJointHybridPhysicalRowExactLeftReceiverProjection A)
    play).mp hplay

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointLeftPhysicalLinkedSiblingMove.memberController_targetSafe
    (move : ProfiledRawJointLeftPhysicalLinkedSiblingMove A)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let linkedMonitor :=
      profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let linkedPlay := treePlay
      (narrowedInducedTree linkedMonitor controller.labeledTree) env
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridPhysicalRowExactLeftReceiverProjection A)
      linkedPlay
    erasePairedProfiledState A
        (profiledRawJointHybridPhysicalLinkedLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A
          (((profiledRawJointTargetLeftBlockMonitor A (LinkedTarget A)
            (profiledRawJointHybridPhysicalLinkedLeftTargetProjection A)
            (profiledRawJointLeftPhysicalLinkedSiblingAllowed A move.1)
            move.1.source).run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      profiledRawJointLeftPhysicalLinkedSiblingAllowed A move.1
        ((play n).2.1.target row) ∧
      profiledRawJointHybridPhysicalLinkedTargetRow A
        ((play n).2.1.target row) = row := by
  dsimp only
  let linkedMonitor :=
    profiledRawJointLeftPhysicalLinkedSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let linkedPlay := treePlay
    (narrowedInducedTree linkedMonitor controller.labeledTree) env
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridPhysicalRowExactLeftReceiverProjection A)
    linkedPlay
  have hwin :
      (profiledRawJointTargetLeftBlockMonitor A (LinkedTarget A)
        (profiledRawJointHybridPhysicalLinkedLeftTargetProjection A)
        (profiledRawJointLeftPhysicalLinkedSiblingAllowed A move.1)
        move.1.source).WinsPlay play :=
    move.memberController_projectedWins A member env
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A
    (profiledRawJointHybridPhysicalLinkedLeftTargetProjection A)
    (profiledRawJointLeftPhysicalLinkedSiblingAllowed A move.1)
    move.1.source play hwin n row
  refine ⟨hsafe.1, hsafe.2, ?_⟩
  exact
    profiledRawJointHybridPhysicalRowExactLeftTarget_row A
      (linkedPlay n).2.1 row

noncomputable def profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :
    ProfiledRawJointLeftPhysicalLinkedSiblingDescriptor A := by
  classical
  exact {
    source := source
    allowed := fun target ↦ decide
      (ProfiledRawJointLeftLinkedTargetAllowed A activation children target)
  }

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf_allowed_iff
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A)
    (target : LinkedTarget A) :
    profiledRawJointLeftPhysicalLinkedSiblingAllowed A
        (profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf A activation
          children) target ↔
      ProfiledRawJointLeftLinkedTargetAllowed A activation children target := by
  simp [profiledRawJointLeftPhysicalLinkedSiblingAllowed,
    profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf]

noncomputable def profiledRawJointLeftPhysicalLinkedSiblingActivation
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :
    ProfiledRawJointTargetLeftBlockActivation A (LinkedTarget A)
      (profiledRawJointHybridPhysicalLinkedLeftTargetProjection A)
      (profiledRawJointLeftPhysicalLinkedSiblingAllowed A
        (profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf A activation
          children)) source := by
  let linked := activation.linkPhysicalAnnotation A children
  exact {
    lambda := linked.lambda
    initial_profile := linked.initial_profile
    forever := linked.forever
    target := linked.target
    target_allowed := fun row past input ↦
      (profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf_allowed_iff A
        activation children _).mpr (linked.target_allowed row past input)
    target_state := linked.target_state
  }

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointLeftPhysicalLinkedSiblingActivation_target_row
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    profiledRawJointHybridPhysicalLinkedTargetRow A
        ((profiledRawJointLeftPhysicalLinkedSiblingActivation A activation
          children).target row past input) = row :=
  rfl

def profiledRawJointLeftPhysicalLinkedSiblingReceiver
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :=
  profiledRawJointHybridPhysicalRowExactLeftReceiverStrategy A
    (profiledRawJointLeftPhysicalLinkedSiblingActivation A activation
      children)
    (profiledRawJointLeftPhysicalLinkedSiblingActivation_target_row A
      activation children)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalLinkedSiblingMonitor_realizable
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A)
    (member : Bool) (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftPhysicalLinkedSiblingMonitor A
      (profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf A activation
        children) member).WinsPlay
      (pairPlay
        (profiledRawJointLeftPhysicalLinkedSiblingReceiver A activation
          children)
        (pairedLeftSenderStrategy activation.lambda) env) := by
  exact profiledRawJointHybridPhysicalRowExactLeftBlockMonitor_realizable A
    (profiledRawJointLeftPhysicalLinkedSiblingActivation A activation
      children)
    (profiledRawJointLeftPhysicalLinkedSiblingActivation_target_row A
      activation children) env

noncomputable def profiledRawJointLeftPhysicalLinkedSiblingMoveOf
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      PhysicalAnnotation A) :
    ProfiledRawJointLeftPhysicalLinkedSiblingMove A := by
  let descriptor :=
    profiledRawJointLeftPhysicalLinkedSiblingDescriptorOf A activation
      children
  let receiver :=
    profiledRawJointLeftPhysicalLinkedSiblingReceiver A activation children
  letI : Inhabited
      (ProfiledRawJointHybridPhysicalRowExactLeftReceiverOutput A) :=
    ⟨receiver [] default⟩
  let table := finiteRootFamilyTable
    (profiledRawJointLeftPhysicalLinkedSiblingMonitor A descriptor)
    (fun _member ↦ receiver)
    (pairedLeftSenderStrategy activation.lambda)
    (fun member env ↦
      profiledRawJointLeftPhysicalLinkedSiblingMonitor_realizable A
        activation children member env)
  exact ⟨descriptor, table,
    finiteRootFamilyTable_wins
      (profiledRawJointLeftPhysicalLinkedSiblingMonitor A descriptor)
      (fun _member ↦ receiver)
      (pairedLeftSenderStrategy activation.lambda)
      (fun member env ↦
        profiledRawJointLeftPhysicalLinkedSiblingMonitor_realizable A
          activation children member env)⟩

end

end DetParityAutomaton

end DistributedSynthesis
