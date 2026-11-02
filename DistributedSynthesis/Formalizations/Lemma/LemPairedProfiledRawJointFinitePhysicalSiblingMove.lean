/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingTreeTransitionAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointTargetPhysicalPriority

/-!
# A fixed finite move alphabet for semantic sibling blocks

The semantic sibling-family construction is indexed by exact histories.  Its
*operational* block monitor, however, depends only on two finite pieces of
data: the current profiled source slot and the truth table of the finite
allowed-target relation.  We package those pieces as a finite descriptor and
put the state-controlled narrowed table in a dependent sum over descriptors.

This is the finite outer move that was missing from the direct presentation.
The arbitrary `List` fields of `ProfiledRawJointFamilyDirection` occur only
when constructing a semantic witness.  They are absent from this move type.
Once a move is selected, its block history is carried by the finite controller
state and advanced only by the sender's current input.

For the common/strict sibling pair, both proof-side members produce the same
descriptor and are projected from one table.  Their sender controls and
outputs are therefore literally equal.  The Boolean member remains only a
receiver-side monitor tag; no graph, orientation, or strict-leader signal is
available to the sender.
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

abbrev ProfiledRawJointUnitTarget :=
  ProfiledRawJointIncidenceCode A (I := Unit)

/-! ## Right blocks -/

/-- All finite data on which a target-parametric right monitor depends. -/
structure ProfiledRawJointRightPhysicalSiblingDescriptor where
  source : ProfiledRawRightSlot A
  allowed : ProfiledRawJointUnitTarget A → Bool

noncomputable instance :
    Fintype (ProfiledRawJointRightPhysicalSiblingDescriptor A) := by
  classical
  letI : Fintype A.State := A.stateFinite
  letI : Fintype (ProfiledRawRightSlot A) := Fintype.ofFinite _
  let Rep := ProfiledRawRightSlot A ×
    (ProfiledRawJointUnitTarget A → Bool)
  let e : ProfiledRawJointRightPhysicalSiblingDescriptor A ≃ Rep :=
    { toFun := fun descriptor ↦ (descriptor.source, descriptor.allowed)
      invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
      left_inv := by intro descriptor; cases descriptor; rfl
      right_inv := by intro descriptor; cases descriptor; rfl }
  exact Fintype.ofEquiv Rep e.symm

def profiledRawJointRightPhysicalSiblingAllowed
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A)
    (target : ProfiledRawJointUnitTarget A) : Prop :=
  descriptor.allowed target = true

noncomputable instance
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A) :
    DecidablePred (profiledRawJointRightPhysicalSiblingAllowed A descriptor) :=
  fun _ ↦ Classical.propDecidable _

/-- The fixed Boolean sibling monitor below one finite right descriptor. -/
abbrev profiledRawJointRightPhysicalSiblingMonitor
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A)
    (_member : Bool) :=
  profiledRawJointTargetRightBlockMonitor A
    (ProfiledRawJointUnitTarget A)
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
    descriptor.source

/-- A literal finite outer move for a right block: a finite descriptor and
one accepted state-controlled table for both hidden sibling members. -/
noncomputable abbrev ProfiledRawJointRightPhysicalSiblingMove :=
  Sigma fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
    { table : FiniteRootFamilyTable
        (profiledRawJointRightPhysicalSiblingMonitor A descriptor) //
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRawJointRightPhysicalSiblingMonitor A descriptor))
        table.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (ProfiledRawJointRightPhysicalSiblingMove A) := by
  classical
  infer_instance

/-- Read either hidden sibling member from the one finite right move.

After materializing the common target relation, the two member monitors are
definitionally the same.  We therefore always use the `false` projection of
the simultaneous table.  In particular the Boolean is not consulted by the
runtime controller at all; it remains only a proof-side name for the two
semantic explanations of the same physical block. -/
noncomputable def ProfiledRawJointRightPhysicalSiblingMove.memberController
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (_member : Bool) :=
  finiteRootMemberController
    (profiledRawJointRightPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree false

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The complete right block controller, including its receiver certificate
table, is independent of the hidden sibling explanation. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_eq
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool) :
    move.memberController A left = move.memberController A right :=
  rfl

/-- The member tag cannot affect the sender control. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_control_eq
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool) (word : List In₁) :
    (move.memberController A left).controlAt word =
      (move.memberController A right).controlAt word :=
  rfl

/-- The two common/strict projections emit the same blind process-one output
at every sender-input word. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_sender_eq
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool) (word : List In₁) :
    ((move.memberController A left).labeledTree word).1 =
      ((move.memberController A right).labeledTree word).1 :=
  rfl

/-- Pointwise form of `memberController_eq`, convenient for local carrier
interfaces that consume the complete narrowed label. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_label_eq
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool) (word : List In₁) :
    (move.memberController A left).labeledTree word =
      (move.memberController A right).labeledTree word :=
  rfl

/-- State-local form of the shared-table law.  It is the interface needed by
an executable carrier that keeps the table alive for an entire homogeneous
epoch: the hidden semantic member cannot change even the next finite control,
at an arbitrary already-reached control. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_step_eq
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool)
    (control : (move.memberController A false).Control) (input : In₁) :
    (move.memberController A left).step control input =
      (move.memberController A right).step control input :=
  rfl

/-- The complete narrowed label is likewise member-independent at an
arbitrary shared finite control, before any independently selected recurrent
controller is entered. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_labelAt_eq
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool)
    (control : (move.memberController A false).Control) :
    (move.memberController A left).labelOf control =
      (move.memberController A right).labelOf control :=
  rfl

/-- Both projections inherit the checked universal-thread guarantee. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_wins
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 member)
      (move.memberController A member).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (profiledRawJointRightPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree move.2.2 false

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every receiver target emitted by a right physical move is a literal
physical close and belongs to the move's finite allowed-target truth table. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_targetSafe
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      profiledRawJointRightPhysicalSiblingAllowed A move.1
        ((play n).2.1.target row) := by
  dsimp only
  exact profiledRawJointTargetRight_narrowedTargetSafe A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A move.1)
    move.1.source
    (move.memberController A member).labeledTree
    (move.memberController_wins A member) env n row

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The priority carried by every emitted right target is exactly the minimum
priority of the literal physical block prefix.  Thus the finite descriptor
packaging loses no epoch-parity information. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_targetPriority
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    pairedProfiledEntryPriority A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row move.1.source.1.1)
          (profiledRawJointTargetRightPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  dsimp only
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (move.memberController_wins A member)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  exact profiledRawJointTargetRight_targetPriority_eq_blockMin_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A move.1)
    move.1.source play hplay n row

/-! ### Constructing the finite right move from one semantic sibling pair -/

/-- The semantic shared relation materialized as a finite Boolean truth
table.  It is independent of the hidden common/strict member. -/
noncomputable def profiledRawJointRightPhysicalSiblingDescriptorOf
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State) :
    ProfiledRawJointRightPhysicalSiblingDescriptor A := by
  classical
  exact {
    source := profiledRawRightSlotOfSemanticPair A semanticMember
    allowed := fun target ↦ decide
      (ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
        target) }

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointRightPhysicalSiblingAllowed A
        (profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
          semanticMember) target ↔
      ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
        target := by
  simp [profiledRawJointRightPhysicalSiblingAllowed,
    profiledRawJointRightPhysicalSiblingDescriptorOf]

/-- Re-express the semantic activation with the common finite truth table.
Only its proof of target admissibility changes. -/
noncomputable def profiledRawJointRightPhysicalSiblingActivation
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) :
    ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A
        (profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
          semanticMember))
      (profiledRawRightSlotOfSemanticPair A semanticMember) := by
  let base := profiledRawJointRightSiblingActivation A hwin family direction
    semanticMember hmember member
  refine {
    lambda := base.lambda
    initial_profile := base.initial_profile
    forever := base.forever
    target := base.target
    target_allowed := ?_
    target_state := base.target_state }
  intro row past input
  rw [profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff A]
  exact (profiledRawJointRightSiblingAllowedTarget_iff_shared A family
    direction member _).mp (base.target_allowed row past input)

def profiledRawJointRightPhysicalSiblingReceiver
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂)
        (ProfiledRawJointUnitTarget A)) :=
  profiledRawJointTargetRightReceiverStrategy A
    (profiledRawJointRightPhysicalSiblingActivation A hwin family direction
      semanticMember hmember member)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightPhysicalSiblingMonitor_realizable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (env : Nat → In₂ × In₁) :
    (profiledRawJointRightPhysicalSiblingMonitor A
      (profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
        semanticMember) member).WinsPlay
      (pairPlay
        (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember member)
        (profiledRawJointRightSiblingSender A semanticMember) env) := by
  simpa [profiledRawJointRightPhysicalSiblingMonitor,
    profiledRawJointRightPhysicalSiblingReceiver,
    profiledRawJointRightSiblingSender,
    profiledRawJointRightPhysicalSiblingActivation] using
    (profiledRawJointTargetRightBlockMonitor_realizable A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A
      (profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
        semanticMember))
    (profiledRawRightSlotOfSemanticPair A semanticMember)
    (profiledRawJointRightPhysicalSiblingActivation A hwin family direction
      semanticMember hmember member) env)

/-- The semantic common/strict pair produces one member of the fixed finite
right move alphabet.  There is no direction/history in the result type. -/
noncomputable def profiledRawJointRightPhysicalSiblingMoveOf
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ProfiledRawJointRightPhysicalSiblingMove A := by
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let descriptor := profiledRawJointRightPhysicalSiblingDescriptorOf A family
    direction semanticMember
  let table := finiteRootFamilyTable
    (profiledRawJointRightPhysicalSiblingMonitor A descriptor)
    (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember)
    (profiledRawJointRightSiblingSender A semanticMember)
    (profiledRawJointRightPhysicalSiblingMonitor_realizable A hwin family
      direction semanticMember hmember)
  exact ⟨descriptor, table,
    finiteRootFamilyTable_wins
      (profiledRawJointRightPhysicalSiblingMonitor A descriptor)
      (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember)
      (profiledRawJointRightSiblingSender A semanticMember)
      (profiledRawJointRightPhysicalSiblingMonitor_realizable A hwin family
        direction semanticMember hmember)⟩

/-- For the semantic move, the finite descriptor truth table is exactly the
common/strict shared target relation. -/
theorem profiledRawJointRightPhysicalSiblingMoveOf_targetSafe_shared
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointRightPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
        ((play n).2.1.target row) := by
  dsimp only
  let move := profiledRawJointRightPhysicalSiblingMoveOf A hwin family
    direction semanticMember hmember
  obtain ⟨hclose, hallowed⟩ := move.memberController_targetSafe A member env n row
  refine ⟨hclose, ?_⟩
  change profiledRawJointRightPhysicalSiblingAllowed A
      (profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
        semanticMember) _ at hallowed
  exact (profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff A
    family direction semanticMember _).mp hallowed

/-- Thus every target exposed by the finite right move has a literal
recursive semantic representative. -/
theorem profiledRawJointRightPhysicalSiblingMoveOf_target_representable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointRightPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ child : ProfiledRawJointSemanticFamily A strategy (I := Unit),
      child.incidenceCode A = (play n).2.1.target row := by
  dsimp only
  have hsafe := profiledRawJointRightPhysicalSiblingMoveOf_targetSafe_shared
    A hwin family direction semanticMember hmember member env n row
  exact profiledRawJointRightSiblingTargetsRepresentable A family direction
    _ hsafe.2

/-! ## Left blocks -/

structure ProfiledRawJointLeftPhysicalSiblingDescriptor where
  source : ProfiledRawLeftSlot A
  allowed : ProfiledRawJointUnitTarget A → Bool

noncomputable instance :
    Fintype (ProfiledRawJointLeftPhysicalSiblingDescriptor A) := by
  classical
  letI : Fintype A.State := A.stateFinite
  letI : Fintype (ProfiledRawLeftSlot A) := Fintype.ofFinite _
  let Rep := ProfiledRawLeftSlot A ×
    (ProfiledRawJointUnitTarget A → Bool)
  let e : ProfiledRawJointLeftPhysicalSiblingDescriptor A ≃ Rep :=
    { toFun := fun descriptor ↦ (descriptor.source, descriptor.allowed)
      invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
      left_inv := by intro descriptor; cases descriptor; rfl
      right_inv := by intro descriptor; cases descriptor; rfl }
  exact Fintype.ofEquiv Rep e.symm

def profiledRawJointLeftPhysicalSiblingAllowed
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A)
    (target : ProfiledRawJointUnitTarget A) : Prop :=
  descriptor.allowed target = true

noncomputable instance
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A) :
    DecidablePred (profiledRawJointLeftPhysicalSiblingAllowed A descriptor) :=
  fun _ ↦ Classical.propDecidable _

abbrev profiledRawJointLeftPhysicalSiblingMonitor
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A)
    (_member : Bool) :=
  profiledRawJointTargetLeftBlockMonitor A
    (ProfiledRawJointUnitTarget A)
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
    descriptor.source

noncomputable abbrev ProfiledRawJointLeftPhysicalSiblingMove :=
  Sigma fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
    { table : FiniteRootFamilyTable
        (profiledRawJointLeftPhysicalSiblingMonitor A descriptor) //
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRawJointLeftPhysicalSiblingMonitor A descriptor))
        table.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (ProfiledRawJointLeftPhysicalSiblingMove A) := by
  classical
  infer_instance

noncomputable def ProfiledRawJointLeftPhysicalSiblingMove.memberController
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (_member : Bool) :=
  finiteRootMemberController
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree false

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_eq
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool) :
    move.memberController A left = move.memberController A right :=
  rfl

theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_control_eq
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool) (word : List In₂) :
    (move.memberController A left).controlAt word =
      (move.memberController A right).controlAt word :=
  rfl

theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_sender_eq
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool) (word : List In₂) :
    ((move.memberController A left).labeledTree word).1 =
      ((move.memberController A right).labeledTree word).1 :=
  rfl

theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_label_eq
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool) (word : List In₂) :
    (move.memberController A left).labeledTree word =
      (move.memberController A right).labeledTree word :=
  rfl

/-- Left-block state-local shared transition law. -/
theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_step_eq
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool)
    (control : (move.memberController A false).Control) (input : In₂) :
    (move.memberController A left).step control input =
      (move.memberController A right).step control input :=
  rfl

/-- Left-block state-local shared complete-label law. -/
theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_labelAt_eq
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool)
    (control : (move.memberController A false).Control) :
    (move.memberController A left).labelOf control =
      (move.memberController A right).labelOf control :=
  rfl

theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_wins
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member)
      (move.memberController A member).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree move.2.2 false

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_targetSafe
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      profiledRawJointLeftPhysicalSiblingAllowed A move.1
        ((play n).2.1.target row) := by
  dsimp only
  exact profiledRawJointTargetLeft_narrowedTargetSafe A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
    move.1.source
    (move.memberController A member).labeledTree
    (move.memberController_wins A member) env n row

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_targetPriority
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    pairedProfiledEntryPriority A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row move.1.source.1.1)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  dsimp only
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (move.memberController_wins A member)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  exact profiledRawJointTargetLeft_targetPriority_eq_blockMin_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
    move.1.source play hplay n row

noncomputable def profiledRawJointLeftPhysicalSiblingDescriptorOf
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State) :
    ProfiledRawJointLeftPhysicalSiblingDescriptor A := by
  classical
  exact {
    source := profiledRawLeftSlotOfSemanticPair A semanticMember
    allowed := fun target ↦ decide
      (ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
        target) }

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointLeftPhysicalSiblingAllowed A
        (profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
          semanticMember) target ↔
      ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
        target := by
  simp [profiledRawJointLeftPhysicalSiblingAllowed,
    profiledRawJointLeftPhysicalSiblingDescriptorOf]

noncomputable def profiledRawJointLeftPhysicalSiblingActivation
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) :
    ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A
        (profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
          semanticMember))
      (profiledRawLeftSlotOfSemanticPair A semanticMember) := by
  let base := profiledRawJointLeftSiblingActivation A hwin family direction
    semanticMember hmember member
  refine {
    lambda := base.lambda
    initial_profile := base.initial_profile
    forever := base.forever
    target := base.target
    target_allowed := ?_
    target_state := base.target_state }
  intro row past input
  rw [profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff A]
  exact (profiledRawJointLeftSiblingAllowedTarget_iff_shared A family
    direction member _).mp (base.target_allowed row past input)

def profiledRawJointLeftPhysicalSiblingReceiver
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂)
        (ProfiledRawJointUnitTarget A)) :=
  profiledRawJointTargetLeftReceiverStrategy A
    (profiledRawJointLeftPhysicalSiblingActivation A hwin family direction
      semanticMember hmember member)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingMonitor_realizable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftPhysicalSiblingMonitor A
      (profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
        semanticMember) member).WinsPlay
      (pairPlay
        (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember member)
        (profiledRawJointLeftSiblingSender A semanticMember) env) := by
  simpa [profiledRawJointLeftPhysicalSiblingMonitor,
    profiledRawJointLeftPhysicalSiblingReceiver,
    profiledRawJointLeftSiblingSender,
    profiledRawJointLeftPhysicalSiblingActivation] using
    (profiledRawJointTargetLeftBlockMonitor_realizable A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A
      (profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
        semanticMember))
    (profiledRawLeftSlotOfSemanticPair A semanticMember)
    (profiledRawJointLeftPhysicalSiblingActivation A hwin family direction
      semanticMember hmember member) env)

noncomputable def profiledRawJointLeftPhysicalSiblingMoveOf
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ProfiledRawJointLeftPhysicalSiblingMove A := by
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let descriptor := profiledRawJointLeftPhysicalSiblingDescriptorOf A family
    direction semanticMember
  let table := finiteRootFamilyTable
    (profiledRawJointLeftPhysicalSiblingMonitor A descriptor)
    (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember)
    (profiledRawJointLeftSiblingSender A semanticMember)
    (profiledRawJointLeftPhysicalSiblingMonitor_realizable A hwin family
      direction semanticMember hmember)
  exact ⟨descriptor, table,
    finiteRootFamilyTable_wins
      (profiledRawJointLeftPhysicalSiblingMonitor A descriptor)
      (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember)
      (profiledRawJointLeftSiblingSender A semanticMember)
      (profiledRawJointLeftPhysicalSiblingMonitor_realizable A hwin family
        direction semanticMember hmember)⟩

theorem profiledRawJointLeftPhysicalSiblingMoveOf_targetSafe_shared
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointLeftPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
        ((play n).2.1.target row) := by
  dsimp only
  let move := profiledRawJointLeftPhysicalSiblingMoveOf A hwin family
    direction semanticMember hmember
  obtain ⟨hclose, hallowed⟩ := move.memberController_targetSafe A member env n row
  refine ⟨hclose, ?_⟩
  change profiledRawJointLeftPhysicalSiblingAllowed A
      (profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
        semanticMember) _ at hallowed
  exact (profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff A
    family direction semanticMember _).mp hallowed

theorem profiledRawJointLeftPhysicalSiblingMoveOf_target_representable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointLeftPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ child : ProfiledRawJointSemanticFamily A strategy (I := Unit),
      child.incidenceCode A = (play n).2.1.target row := by
  dsimp only
  have hsafe := profiledRawJointLeftPhysicalSiblingMoveOf_targetSafe_shared
    A hwin family direction semanticMember hmember member env n row
  exact profiledRawJointLeftSiblingTargetsRepresentable A family direction
    _ hsafe.2

/-! ## Finite outer alphabets -/

/-- A physical block choice is one of the two finite, already-coupled table
types.  The side is a proof-level choice of which block is being executed; it
is not passed to either member controller. -/
noncomputable abbrev ProfiledRawJointPhysicalSiblingMove :=
  ProfiledRawJointRightPhysicalSiblingMove A ⊕
    ProfiledRawJointLeftPhysicalSiblingMove A

noncomputable instance :
    Fintype (ProfiledRawJointPhysicalSiblingMove A) := by
  classical
  infer_instance

/-- The outer construction may branch on actual finite environment rounds.
In particular no accumulated strict history occurs in the branch type. -/
abbrev ProfiledRawJointPhysicalBranch := EnvironmentRound In₁ In₂

noncomputable instance :
    Fintype (ProfiledRawJointPhysicalBranch (In₁ := In₁) (In₂ := In₂)) :=
  inferInstance

end

end DetParityAutomaton

end DistributedSynthesis
