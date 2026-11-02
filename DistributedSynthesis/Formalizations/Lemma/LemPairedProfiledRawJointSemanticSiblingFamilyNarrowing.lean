/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointTargetBlockHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPolicyTargetProjection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedActualChild

/-!
# Pre-policy narrowing of the semantic common/strict sibling pair

At an ambiguous receive, the simultaneous semantic child and the matching
strict child are distinct global families.  The process which is blind in the
following block nevertheless sees literally the same semantic lane in both
families.  This module narrows those two roots *together*, before selecting an
outer finite-code policy.

The hidden Boolean below is only the index of the two proof-side block
monitors.  `finiteRootFamilyMonitor` puts it in the full-information receiver
alphabet and erases it from the sender alphabet.  Consequently the two
projected controllers have definitionally the same blind control and sender
table.  No graph, orientation, or strict-leader bit is a runtime field of the
sender.

Targets are finite raw-joint incidence codes.  Each member monitor checks
that its receiver emits a literal one-sided semantic successor of that
member.  Thus the later outer policy may be built around this already-shared
finite table, instead of independently choosing actions at the two sibling
states.
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

/-! ## The two semantic sibling families -/

/-- `false` is the simultaneous child; `true` is its strict-left sibling.
The Boolean is proof-side and will be hidden from the right blind sender. -/
def profiledRawJointRightSiblingFamily
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) : ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  if member then family.leftActualChild A direction
  else family.semanticChild A direction

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Both right-sibling roots retain literally the same process-one lane. -/
@[simp] theorem profiledRawJointRightSiblingFamily_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) :
    (profiledRawJointRightSiblingFamily A family direction member).right =
      (family.semanticChild A direction).right := by
  cases member with
  | false => rfl
  | true =>
      exact (family.semanticChild_right_eq_leftActual A direction).symm

/-- `false` is the simultaneous child; `true` is its strict-right sibling.
The Boolean is hidden from the left blind sender. -/
def profiledRawJointLeftSiblingFamily
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) : ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  if member then family.rightActualChild A direction
  else family.semanticChild A direction

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Both left-sibling roots retain literally the same process-two lane. -/
@[simp] theorem profiledRawJointLeftSiblingFamily_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool) :
    (profiledRawJointLeftSiblingFamily A family direction member).left =
      (family.semanticChild A direction).left := by
  cases member with
  | false => rfl
  | true =>
      exact (family.semanticChild_left_eq_rightActual A direction).symm

/-! ## Finite target relations, before any outer policy -/

/-- A target is allowed at a right sibling root exactly when it is one of
that semantic root's literal physical right-block successors. -/
def ProfiledRawJointRightSiblingAllowedTarget
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  let root := profiledRawJointRightSiblingFamily A family direction member
  ∃ row past input,
    target = profiledRawJointOneSidedNext A (root.incidenceCode A)
      (root.move A)
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)

/-- Left-block mirror. -/
def ProfiledRawJointLeftSiblingAllowedTarget
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (member : Bool)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  let root := profiledRawJointLeftSiblingFamily A family direction member
  ∃ row past input,
    target = profiledRawJointOneSidedNext A (root.incidenceCode A)
      (root.move A)
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)

/-! ## Right sibling activations -/

/-- The common and strict-left semantic roots both realize a target-parametric
right monitor using the very same literal blind lambda. -/
noncomputable def profiledRawJointRightSiblingActivation
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
      (ProfiledRawJointIncidenceCode A (I := Unit))
      (profiledRawJointUnitRightTargetProjection A)
      (ProfiledRawJointRightSiblingAllowedTarget A family direction member)
      (profiledRawRightSlotOfSemanticPair A semanticMember) := by
  let root := profiledRawJointRightSiblingFamily A family direction member
  let source := profiledRawRightSlotOfSemanticPair A semanticMember
  let lambda := semanticMember.1.lambdaOfStrategy
  have hrootMember : root.right () = some semanticMember := by
    change (profiledRawJointRightSiblingFamily A family direction member).right
      () = some semanticMember
    rw [profiledRawJointRightSiblingFamily_right]
    exact hmember
  have hsource : (root.incidenceCode A).family.right () = some source := by
    change (root.code A).right () = some source
    exact congrArg
      (Option.map fun member ↦
        ((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy)) hrootMember
  have hlambda : (root.move A).rightLambda () = some lambda := by
    exact congrArg (Option.map fun member ↦ member.1.lambdaOfStrategy)
      hrootMember
  refine {
    lambda := lambda
    initial_profile := rfl
    forever := pairedRightForeverAccepts_of_winning A strategy hwin
      semanticMember.1
    target := fun row past input ↦
      profiledRawJointOneSidedNext A (root.incidenceCode A) (root.move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)
    target_allowed := ?_
    target_state := ?_ }
  · intro row past input
    exact ⟨row, past, input, rfl⟩
  · intro row past input
    have hfunctional := root.rightPattern_rowFunctionalAt A ((), row)
    have hreflexive :
        (root.incidenceCode A).family.rightPattern ((), row) ((), row) =
          true := by
      simp [ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.rightPattern, hrootMember]
    rw [profiledRawJointUnitRightTargetProjection_next A
      (root.incidenceCode A) (root.move A) row past input source lambda
      hsource hlambda hfunctional hreflexive,
      pairedProfiledOneChild_eq_profiledRawRightChildSlot A source lambda row
        past input]

/-! ## One finite right table shared by the sibling roots -/

/-- The two target-parametric monitors folded by the hidden-root
construction.  Their target relations may be read with different proof-side
roots, while their physical source slot is literally common. -/
abbrev profiledRawJointRightSiblingBlockMonitor
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (member : Bool) :=
  profiledRawJointTargetRightBlockMonitor A
    (ProfiledRawJointIncidenceCode A (I := Unit))
    (profiledRawJointUnitRightTargetProjection A)
    (ProfiledRawJointRightSiblingAllowedTarget A family direction member)
    (profiledRawRightSlotOfSemanticPair A semanticMember)

/-- Semantic receiver for one proof-side sibling member. -/
def profiledRawJointRightSiblingReceiver
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
        (ProfiledRawJointIncidenceCode A (I := Unit))) :=
  profiledRawJointTargetRightReceiverStrategy A
    (profiledRawJointRightSiblingActivation A hwin family direction
      semanticMember hmember member)

/-- The sender supplied to the family extraction contains only the original
process-one blind strategy. -/
def profiledRawJointRightSiblingSender
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (semanticMember : ProcOnePairedEntryRep strategy × A.State) :
    SenderBlockStrategy In₁ Out₁ :=
  pairedRightSenderStrategy semanticMember.1.lambdaOfStrategy

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightSiblingBlockMonitor_realizable
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
    (profiledRawJointRightSiblingBlockMonitor A family direction
      semanticMember member).WinsPlay
      (pairPlay
        (profiledRawJointRightSiblingReceiver A hwin family direction
          semanticMember hmember member)
        (profiledRawJointRightSiblingSender A semanticMember) env) := by
  exact profiledRawJointTargetRightBlockMonitor_realizable A
    (profiledRawJointUnitRightTargetProjection A)
    (ProfiledRawJointRightSiblingAllowedTarget A family direction member)
    (profiledRawRightSlotOfSemanticPair A semanticMember)
    (profiledRawJointRightSiblingActivation A hwin family direction
      semanticMember hmember member) env

/-- Finite move alphabet for the already-coupled right sibling extraction. -/
abbrev ProfiledRawJointRightSiblingTable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State) :=
  FiniteRootFamilyTable
    (fun member : Bool ↦
      profiledRawJointRightSiblingBlockMonitor A family direction
        semanticMember member)

/-- Perform the single state-controlled extraction before the outer policy is
chosen. -/
noncomputable def profiledRawJointRightSiblingTable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ProfiledRawJointRightSiblingTable A family direction semanticMember := by
  let Target := ProfiledRawJointIncidenceCode A (I := Unit)
  letI : Inhabited Target :=
    ⟨(profiledRawJointRightSiblingFamily A family direction false
      ).incidenceCode A⟩
  exact finiteRootFamilyTable
    (fun member : Bool ↦
      profiledRawJointRightSiblingBlockMonitor A family direction
        semanticMember member)
    (profiledRawJointRightSiblingReceiver A hwin family direction
      semanticMember hmember)
    (profiledRawJointRightSiblingSender A semanticMember)
    (profiledRawJointRightSiblingBlockMonitor_realizable A hwin family
      direction semanticMember hmember)

/-- Project the shared family table to either proof-side root. -/
abbrev profiledRawJointRightSiblingMemberController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) :=
  finiteRootMemberController
    (fun root : Bool ↦
      profiledRawJointRightSiblingBlockMonitor A family direction
        semanticMember root)
    (profiledRawJointRightSiblingTable A hwin family direction semanticMember
      hmember).toTransitionRationalTree member

/-- Both projected right controllers win their own member monitor. -/
theorem profiledRawJointRightSiblingMemberController_wins
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
    NarrowedAllThreadsWin
      (profiledRawJointRightSiblingBlockMonitor A family direction
        semanticMember member)
      (profiledRawJointRightSiblingMemberController A hwin family direction
        semanticMember hmember member).labeledTree := by
  let Target := ProfiledRawJointIncidenceCode A (I := Unit)
  letI : Inhabited Target :=
    ⟨(profiledRawJointRightSiblingFamily A family direction false
      ).incidenceCode A⟩
  apply finiteRootMemberController_allThreadsWin
    (fun root : Bool ↦
      profiledRawJointRightSiblingBlockMonitor A family direction
        semanticMember root)
  exact finiteRootFamilyTable_wins
    (fun root : Bool ↦
      profiledRawJointRightSiblingBlockMonitor A family direction
        semanticMember root)
    (profiledRawJointRightSiblingReceiver A hwin family direction
      semanticMember hmember)
    (profiledRawJointRightSiblingSender A semanticMember)
    (profiledRawJointRightSiblingBlockMonitor_realizable A hwin family
      direction semanticMember hmember)

/-- The blind sender table is definitionally shared by the simultaneous and
strict-left projections. -/
theorem profiledRawJointRightSiblingMemberController_sender_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (left right : Bool) (word : List In₁) :
    ((profiledRawJointRightSiblingMemberController A hwin family direction
      semanticMember hmember left).labeledTree word).1 =
    ((profiledRawJointRightSiblingMemberController A hwin family direction
      semanticMember hmember right).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (fun root : Bool ↦
      profiledRawJointRightSiblingBlockMonitor A family direction
        semanticMember root)
    (profiledRawJointRightSiblingTable A hwin family direction semanticMember
      hmember).toTransitionRationalTree left right word

/-- Every target emitted by either projected controller is a literal
one-sided successor of that proof-side sibling root, in addition to matching
the physical block close. -/
theorem profiledRawJointRightSiblingMemberController_targetSafe
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
    let targetState := profiledRawJointUnitRightTargetProjection A
    let Allowed := ProfiledRawJointRightSiblingAllowedTarget A family
      direction member
    let monitor := profiledRawJointRightSiblingBlockMonitor A family direction
      semanticMember member
    let controller := profiledRawJointRightSiblingMemberController A hwin
      family direction semanticMember hmember member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      Allowed ((play n).2.1.target row) := by
  dsimp only
  exact profiledRawJointTargetRight_narrowedTargetSafe A
    (profiledRawJointUnitRightTargetProjection A)
    (ProfiledRawJointRightSiblingAllowedTarget A family direction member)
    (profiledRawRightSlotOfSemanticPair A semanticMember)
    (profiledRawJointRightSiblingMemberController A hwin family direction
      semanticMember hmember member).labeledTree
    (profiledRawJointRightSiblingMemberController_wins A hwin family direction
      semanticMember hmember member) env n row

/-! ## Left sibling activations -/

/-- Mirror construction: the simultaneous and strict-right roots realize two
left monitors with one literal process-two blind lambda. -/
noncomputable def profiledRawJointLeftSiblingActivation
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
      (ProfiledRawJointIncidenceCode A (I := Unit))
      (profiledRawJointUnitLeftTargetProjection A)
      (ProfiledRawJointLeftSiblingAllowedTarget A family direction member)
      (profiledRawLeftSlotOfSemanticPair A semanticMember) := by
  let root := profiledRawJointLeftSiblingFamily A family direction member
  let source := profiledRawLeftSlotOfSemanticPair A semanticMember
  let lambda := semanticMember.1.lambdaOfStrategy
  have hrootMember : root.left () = some semanticMember := by
    change (profiledRawJointLeftSiblingFamily A family direction member).left
      () = some semanticMember
    rw [profiledRawJointLeftSiblingFamily_left]
    exact hmember
  have hsource : (root.incidenceCode A).family.left () = some source := by
    change (root.code A).left () = some source
    exact congrArg
      (Option.map fun member ↦
        ((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy)) hrootMember
  have hlambda : (root.move A).leftLambda () = some lambda := by
    exact congrArg (Option.map fun member ↦ member.1.lambdaOfStrategy)
      hrootMember
  refine {
    lambda := lambda
    initial_profile := rfl
    forever := pairedLeftForeverAccepts_of_winning A strategy hwin
      semanticMember.1
    target := fun row past input ↦
      profiledRawJointOneSidedNext A (root.incidenceCode A) (root.move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)
    target_allowed := ?_
    target_state := ?_ }
  · intro row past input
    exact ⟨row, past, input, rfl⟩
  · intro row past input
    have hfunctional := root.leftPattern_rowFunctionalAt A ((), row)
    have hreflexive :
        (root.incidenceCode A).family.leftPattern ((), row) ((), row) =
          true := by
      simp [ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.leftPattern, hrootMember]
    rw [profiledRawJointUnitLeftTargetProjection_next A
      (root.incidenceCode A) (root.move A) row past input source lambda
      hsource hlambda hfunctional hreflexive,
      pairedProfiledTwoChild_eq_profiledRawLeftChildSlot A source lambda row
        past input]

/-! ## One finite left table shared by the sibling roots -/

abbrev profiledRawJointLeftSiblingBlockMonitor
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (member : Bool) :=
  profiledRawJointTargetLeftBlockMonitor A
    (ProfiledRawJointIncidenceCode A (I := Unit))
    (profiledRawJointUnitLeftTargetProjection A)
    (ProfiledRawJointLeftSiblingAllowedTarget A family direction member)
    (profiledRawLeftSlotOfSemanticPair A semanticMember)

def profiledRawJointLeftSiblingReceiver
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
        (ProfiledRawJointIncidenceCode A (I := Unit))) :=
  profiledRawJointTargetLeftReceiverStrategy A
    (profiledRawJointLeftSiblingActivation A hwin family direction
      semanticMember hmember member)

def profiledRawJointLeftSiblingSender
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State) :
    SenderBlockStrategy In₂ Out₂ :=
  pairedLeftSenderStrategy semanticMember.1.lambdaOfStrategy

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftSiblingBlockMonitor_realizable
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
    (profiledRawJointLeftSiblingBlockMonitor A family direction
      semanticMember member).WinsPlay
      (pairPlay
        (profiledRawJointLeftSiblingReceiver A hwin family direction
          semanticMember hmember member)
        (profiledRawJointLeftSiblingSender A semanticMember) env) := by
  exact profiledRawJointTargetLeftBlockMonitor_realizable A
    (profiledRawJointUnitLeftTargetProjection A)
    (ProfiledRawJointLeftSiblingAllowedTarget A family direction member)
    (profiledRawLeftSlotOfSemanticPair A semanticMember)
    (profiledRawJointLeftSiblingActivation A hwin family direction
      semanticMember hmember member) env

abbrev ProfiledRawJointLeftSiblingTable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State) :=
  FiniteRootFamilyTable
    (fun member : Bool ↦
      profiledRawJointLeftSiblingBlockMonitor A family direction
        semanticMember member)

noncomputable def profiledRawJointLeftSiblingTable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ProfiledRawJointLeftSiblingTable A family direction semanticMember := by
  let Target := ProfiledRawJointIncidenceCode A (I := Unit)
  letI : Inhabited Target :=
    ⟨(profiledRawJointLeftSiblingFamily A family direction false
      ).incidenceCode A⟩
  exact finiteRootFamilyTable
    (fun member : Bool ↦
      profiledRawJointLeftSiblingBlockMonitor A family direction
        semanticMember member)
    (profiledRawJointLeftSiblingReceiver A hwin family direction
      semanticMember hmember)
    (profiledRawJointLeftSiblingSender A semanticMember)
    (profiledRawJointLeftSiblingBlockMonitor_realizable A hwin family
      direction semanticMember hmember)

abbrev profiledRawJointLeftSiblingMemberController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) :=
  finiteRootMemberController
    (fun root : Bool ↦
      profiledRawJointLeftSiblingBlockMonitor A family direction
        semanticMember root)
    (profiledRawJointLeftSiblingTable A hwin family direction semanticMember
      hmember).toTransitionRationalTree member

theorem profiledRawJointLeftSiblingMemberController_wins
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
    NarrowedAllThreadsWin
      (profiledRawJointLeftSiblingBlockMonitor A family direction
        semanticMember member)
      (profiledRawJointLeftSiblingMemberController A hwin family direction
        semanticMember hmember member).labeledTree := by
  let Target := ProfiledRawJointIncidenceCode A (I := Unit)
  letI : Inhabited Target :=
    ⟨(profiledRawJointLeftSiblingFamily A family direction false
      ).incidenceCode A⟩
  apply finiteRootMemberController_allThreadsWin
    (fun root : Bool ↦
      profiledRawJointLeftSiblingBlockMonitor A family direction
        semanticMember root)
  exact finiteRootFamilyTable_wins
    (fun root : Bool ↦
      profiledRawJointLeftSiblingBlockMonitor A family direction
        semanticMember root)
    (profiledRawJointLeftSiblingReceiver A hwin family direction
      semanticMember hmember)
    (profiledRawJointLeftSiblingSender A semanticMember)
    (profiledRawJointLeftSiblingBlockMonitor_realizable A hwin family
      direction semanticMember hmember)

theorem profiledRawJointLeftSiblingMemberController_sender_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (left right : Bool) (word : List In₂) :
    ((profiledRawJointLeftSiblingMemberController A hwin family direction
      semanticMember hmember left).labeledTree word).1 =
    ((profiledRawJointLeftSiblingMemberController A hwin family direction
      semanticMember hmember right).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (fun root : Bool ↦
      profiledRawJointLeftSiblingBlockMonitor A family direction
        semanticMember root)
    (profiledRawJointLeftSiblingTable A hwin family direction semanticMember
      hmember).toTransitionRationalTree left right word

theorem profiledRawJointLeftSiblingMemberController_targetSafe
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
    let targetState := profiledRawJointUnitLeftTargetProjection A
    let Allowed := ProfiledRawJointLeftSiblingAllowedTarget A family direction
      member
    let monitor := profiledRawJointLeftSiblingBlockMonitor A family direction
      semanticMember member
    let controller := profiledRawJointLeftSiblingMemberController A hwin
      family direction semanticMember hmember member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      Allowed ((play n).2.1.target row) := by
  dsimp only
  exact profiledRawJointTargetLeft_narrowedTargetSafe A
    (profiledRawJointUnitLeftTargetProjection A)
    (ProfiledRawJointLeftSiblingAllowedTarget A family direction member)
    (profiledRawLeftSlotOfSemanticPair A semanticMember)
    (profiledRawJointLeftSiblingMemberController A hwin family direction
      semanticMember hmember member).labeledTree
    (profiledRawJointLeftSiblingMemberController_wins A hwin family direction
      semanticMember hmember member) env n row

end

end DetParityAutomaton

end DistributedSynthesis
