/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeSidewiseBankAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter

/-!
# Fail-fast dependent member/root pair test

The public fixed value and controller query do not expose which proof-side
descriptor/root evaluation represents the current receipt.  This file tests
the required physical homogeneity directly.

First we prove the strongest fact already supplied by the shape-free fibre:
any two projected members of one source use the same complete physical
receiver strategy at the same physical past and sticky row.  The blind sender
is common by construction.  No leader, orientation, or hidden-bit recovery
test occurs in the statement or proof.

The operational test then passes.  Re-anchoring two evaluations at one
literal current descriptor forces their dependent descriptor members to be
equal.  The retained semantic-table provenance therefore supplies one common
past for the complete table containing both roots, and the same-past theorem
closes the arbitrary reachable-query pair on both sides.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
theorem profiledOpenCanonicalRightRootOfEq_rootToEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.right source table)
    (root : ProfiledOpenCanonicalRightRootOfMove A I move) :
    profiledOpenCanonicalRightRootOfEqOfMove A move source table hmove
        (profiledOpenCanonicalRightRootToEqOfMove A move source table hmove
          root) = root := by
  cases move with
  | sink => exact nomatch root.down
  | left source table => exact nomatch root.down
  | right oldSource oldTable =>
      cases hmove
      rfl

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
theorem profiledOpenCanonicalLeftRootOfEq_rootToEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.left source table)
    (root : ProfiledOpenCanonicalLeftRootOfMove A I move) :
    profiledOpenCanonicalLeftRootOfEqOfMove A move source table hmove
        (profiledOpenCanonicalLeftRootToEqOfMove A move source table hmove
          root) = root := by
  cases move with
  | sink => exact nomatch root.down
  | right source table => exact nomatch root.down
  | left oldSource oldTable =>
      cases hmove
      rfl

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenHiddenDescriptorRightRootOfEq_rootToEq
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : descriptor.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right source table)
    (root : ProfiledOpenHiddenDescriptorRightRoot A descriptor) :
    profiledOpenHiddenDescriptorRightRootOfEq A descriptor source table hmove
        (profiledOpenHiddenDescriptorRightRootToEq A descriptor source table
          hmove root) = root := by
  exact profiledOpenCanonicalRightRootOfEq_rootToEqOfMove A
    descriptor.moveIdentity.1 source table hmove root

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenHiddenDescriptorLeftRootOfEq_rootToEq
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : descriptor.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left source table)
    (root : ProfiledOpenHiddenDescriptorLeftRoot A descriptor) :
    profiledOpenHiddenDescriptorLeftRootOfEq A descriptor source table hmove
        (profiledOpenHiddenDescriptorLeftRootToEq A descriptor source table
          hmove root) = root := by
  exact profiledOpenCanonicalLeftRootOfEq_rootToEqOfMove A
    descriptor.moveIdentity.2 source table hmove root

/-! ## All projected members lie in one literal local fibre -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveRightProjectedPoint_pair_rel
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (left right : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source)) :
    ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin basis
      initialCode
      (profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
        source left)
      (profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
        source right) := by
  let leftMember :
      ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨left.1, by
      simpa [profiledOpenActiveRightProjectedFamily,
        profiledOpenActiveRightProjectedClass] using left.2⟩
  let rightMember :
      ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨right.1, by
      simpa [profiledOpenActiveRightProjectedFamily,
        profiledOpenActiveRightProjectedClass] using right.2⟩
  apply (profiledOpenIndexedActiveRightControlledLocalFibreRel_transitive A
    strategy hwin basis initialCode).trans _ _ _
    (profiledOpenIndexedActiveRightControlledLocalFibreRel_symmetric A
      strategy hwin basis initialCode
      (profiledOpenActiveRightControlledSourceFibrePoint_rel A strategy hwin
        basis initialCode source leftMember))
  exact profiledOpenActiveRightControlledSourceFibrePoint_rel A strategy hwin
    basis initialCode source rightMember

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveLeftProjectedPoint_pair_rel
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (left right : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source)) :
    ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode
      (profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
        source left)
      (profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
        source right) := by
  let leftMember :
      ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨left.1, by
      simpa [profiledOpenActiveLeftProjectedFamily,
        profiledOpenActiveLeftProjectedClass] using left.2⟩
  let rightMember :
      ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨right.1, by
      simpa [profiledOpenActiveLeftProjectedFamily,
        profiledOpenActiveLeftProjectedClass] using right.2⟩
  apply (profiledOpenIndexedActiveLeftControlledLocalFibreRel_transitive A
    strategy hwin basis initialCode).trans _ _ _
    (profiledOpenIndexedActiveLeftControlledLocalFibreRel_symmetric A strategy
      hwin basis initialCode
      (profiledOpenActiveLeftControlledSourceFibrePoint_rel A strategy hwin
        basis initialCode source leftMember))
  exact profiledOpenActiveLeftControlledSourceFibrePoint_rel A strategy hwin
    basis initialCode source rightMember

/-! ## Same-past physical member/root homogeneity -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveRightProjectedReceiver_physical_pair
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (left right : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenActiveRightProjectedFamily A strategy hwin basis
          initialCode source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    pairedRightInformedForRow row
        ((profiledOpenActiveRightProjectedReceiver A strategy hwin basis
          initialCode source left past move).1.physical) =
      pairedRightInformedForRow row
        ((profiledOpenActiveRightProjectedReceiver A strategy hwin basis
          initialCode source right past move).1.physical) := by
  let leftPoint := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source left.1
  let rightPoint := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source right.1
  let leftRoot := profiledOpenActiveRightProjectedRoot A strategy hwin basis
    initialCode source left.1 left.2
  let rightRoot := profiledOpenActiveRightProjectedRoot A strategy hwin basis
    initialCode source right.1 right.2
  have hrel := profiledOpenActiveRightProjectedPoint_pair_rel A strategy hwin
    basis initialCode source left.1 right.1
  have hbehavior :=
    profiledOpenIndexedActiveRightCompleteBehaviorEq_of_decoratedRel A strategy
      hwin basis hrel
  have hreceiver := hbehavior.2 leftRoot rightRoot row
  have hat := congrFun (congrFun hreceiver past) move
  cases row <;>
    simpa [profiledOpenActiveRightProjectedReceiver,
      profiledOpenRightSemanticClassifiedReceiver,
      profiledRightReceiverStrategy, pairedRightInformedForRow,
      pairedRightReceiverStrategy, ProcOnePairedEntryRep.lambdaOfStrategy,
      procOnePairedEntryRightReceiverForRow, leftPoint, rightPoint, leftRoot,
      rightRoot] using hat

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveLeftProjectedReceiver_physical_pair
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (left right : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenActiveLeftProjectedFamily A strategy hwin basis
          initialCode source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    pairedLeftInformedForRow row
        ((profiledOpenActiveLeftProjectedReceiver A strategy hwin basis
          initialCode source left past move).1.physical) =
      pairedLeftInformedForRow row
        ((profiledOpenActiveLeftProjectedReceiver A strategy hwin basis
          initialCode source right past move).1.physical) := by
  let leftPoint := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source left.1
  let rightPoint := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source right.1
  let leftRoot := profiledOpenActiveLeftProjectedRoot A strategy hwin basis
    initialCode source left.1 left.2
  let rightRoot := profiledOpenActiveLeftProjectedRoot A strategy hwin basis
    initialCode source right.1 right.2
  have hrel := profiledOpenActiveLeftProjectedPoint_pair_rel A strategy hwin
    basis initialCode source left.1 right.1
  have hbehavior :=
    profiledOpenIndexedActiveLeftCompleteBehaviorEq_of_decoratedRel A strategy
      hwin basis hrel
  have hreceiver := hbehavior.2 leftRoot rightRoot row
  have hat := congrFun (congrFun hreceiver past) move
  cases row <;>
    simpa [profiledOpenActiveLeftProjectedReceiver,
      profiledOpenLeftSemanticClassifiedReceiver,
      profiledLeftReceiverStrategy, pairedLeftInformedForRow,
      pairedLeftReceiverStrategy, ProcTwoPairedEntryRep.lambdaOfStrategy,
      procTwoPairedEntryLeftReceiverForRow, leftPoint, rightPoint, leftRoot,
      rightRoot] using hat

/-! ## The literal finite-query test

At the operational layer the two evaluations share the fixed value, the
reachable controller query, the sticky row, and the current input.  The blind
sender equality is definitional.  The informed receiver equality first
reduces exactly to equality of two dependent entries in the queried receiver
table; the final section discharges that equality from retained shape-free
provenance. -/

section
omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenFixedRightReanchoredRowEvaluation_member_eq
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query) :
    left.1.1 = right.1.1 := by
  rcases left.2 with ⟨leftWitness, hleftMember, _⟩
  rcases right.2 with ⟨rightWitness, hrightMember, _⟩
  apply Subtype.ext
  exact (congrArg Subtype.val hleftMember).symm.trans
    (leftWitness.member_eq.trans
      (rightWitness.member_eq.symm.trans
        (congrArg Subtype.val hrightMember)))

theorem profiledOpenFixedLeftReanchoredRowEvaluation_member_eq
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query) :
    left.1.1 = right.1.1 := by
  rcases left.2 with ⟨leftWitness, hleftMember, _⟩
  rcases right.2 with ⟨rightWitness, hrightMember, _⟩
  apply Subtype.ext
  exact (congrArg Subtype.val hleftMember).symm.trans
    (leftWitness.member_eq.trans
      (rightWitness.member_eq.symm.trans
        (congrArg Subtype.val hrightMember)))

theorem profiledOpenFixedRightQueryResponses_dependentEvaluation_physical_pair
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    (hprovenance :
      ProfiledOpenActiveRightFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value)
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedRightInformedForRow row
        (profiledOpenFixedRightQueryResponses A initialCode value query
          left.1.1 ((left.1.2, inputTwo), inputOne)).1.physical =
      pairedRightInformedForRow row
        (profiledOpenFixedRightQueryResponses A initialCode value query
          right.1.1 ((right.1.2, inputTwo), inputOne)).1.physical := by
  rcases hprovenance with ⟨provenance, rfl⟩
  rcases left with ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
  rcases right with ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  have hmember : leftMember = rightMember :=
    profiledOpenFixedRightReanchoredRowEvaluation_member_eq A strategy hwin
      basis initialCode ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
        ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  cases hmember
  rcases reachable with ⟨word, hword⟩
  unfold profiledOpenFixedRightQueryResponses
  rw [← hword]
  have hsemantic := provenance.2 word query.2 leftMember
  unfold profiledOpenFixedRightQueryResponses at hsemantic
  unfold profiledOpenActiveRightProjectedSemanticAllowed at hsemantic
  rcases hsemantic with ⟨past, hpast⟩
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source leftMember
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveRightProjectedPoint_moveIdentity A strategy
    hwin basis initialCode source leftMember
  let leftRoot := profiledOpenHiddenDescriptorRightRootToEq A leftMember.1
    point.1.lane.source table hmove leftHiddenRoot
  let rightRoot := profiledOpenHiddenDescriptorRightRootToEq A leftMember.1
    point.1.lane.source table hmove rightHiddenRoot
  have hleft := congrFun hpast ((leftRoot, inputTwo), inputOne)
  have hright := congrFun hpast ((rightRoot, inputTwo), inputOne)
  have hleftPhysical := congrArg
    (fun output : ProfiledOpenRightClassifiedOutput A ↦
      pairedRightInformedForRow row output.1.physical) hleft
  have hrightPhysical := congrArg
    (fun output : ProfiledOpenRightClassifiedOutput A ↦
      pairedRightInformedForRow row output.1.physical) hright
  let physicalPast := past.map (fun old ↦ (old.1.2, old.2))
  have hpair := profiledOpenActiveRightProjectedReceiver_physical_pair A
    strategy hwin basis initialCode source
      ⟨leftMember, leftHiddenRoot⟩ ⟨leftMember, rightHiddenRoot⟩ row physicalPast
      (inputTwo, inputOne)
  cases row <;>
    simpa [point, table, hmove, leftRoot, rightRoot, physicalPast,
      profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenActiveRightProjectedReceiver,
      profiledOpenActiveRightProjectedRoot,
      profiledOpenRightSemanticClassifiedReceiver,
      profiledRightReceiverStrategy, pairedRightInformedForRow,
      profiledOpenHiddenDescriptorRightRootOfEq_rootToEq] using
      (hleftPhysical.trans (hpair.trans hrightPhysical.symm))

theorem profiledOpenFixedLeftQueryResponses_dependentEvaluation_physical_pair
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    (hprovenance :
      ProfiledOpenActiveLeftFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value)
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedLeftInformedForRow row
        (profiledOpenFixedLeftQueryResponses A initialCode value query
          left.1.1 ((left.1.2, inputOne), inputTwo)).1.physical =
      pairedLeftInformedForRow row
        (profiledOpenFixedLeftQueryResponses A initialCode value query
          right.1.1 ((right.1.2, inputOne), inputTwo)).1.physical := by
  rcases hprovenance with ⟨provenance, rfl⟩
  rcases left with ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
  rcases right with ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  have hmember : leftMember = rightMember :=
    profiledOpenFixedLeftReanchoredRowEvaluation_member_eq A strategy hwin
      basis initialCode ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
        ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  cases hmember
  rcases reachable with ⟨word, hword⟩
  unfold profiledOpenFixedLeftQueryResponses
  rw [← hword]
  have hsemantic := provenance.2 word query.2 leftMember
  unfold profiledOpenFixedLeftQueryResponses at hsemantic
  unfold profiledOpenActiveLeftProjectedSemanticAllowed at hsemantic
  rcases hsemantic with ⟨past, hpast⟩
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source leftMember
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy
    hwin basis initialCode source leftMember
  let leftRoot := profiledOpenHiddenDescriptorLeftRootToEq A leftMember.1
    point.1.lane.source table hmove leftHiddenRoot
  let rightRoot := profiledOpenHiddenDescriptorLeftRootToEq A leftMember.1
    point.1.lane.source table hmove rightHiddenRoot
  have hleft := congrFun hpast ((leftRoot, inputOne), inputTwo)
  have hright := congrFun hpast ((rightRoot, inputOne), inputTwo)
  have hleftPhysical := congrArg
    (fun output : ProfiledOpenLeftClassifiedOutput A ↦
      pairedLeftInformedForRow row output.1.physical) hleft
  have hrightPhysical := congrArg
    (fun output : ProfiledOpenLeftClassifiedOutput A ↦
      pairedLeftInformedForRow row output.1.physical) hright
  let physicalPast := past.map (fun old ↦ (old.1.2, old.2))
  have hpair := profiledOpenActiveLeftProjectedReceiver_physical_pair A
    strategy hwin basis initialCode source
      ⟨leftMember, leftHiddenRoot⟩ ⟨leftMember, rightHiddenRoot⟩ row physicalPast
      (inputOne, inputTwo)
  cases row <;>
    simpa [point, table, hmove, leftRoot, rightRoot, physicalPast,
      profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenActiveLeftProjectedReceiver,
      profiledOpenActiveLeftProjectedRoot,
      profiledOpenLeftSemanticClassifiedReceiver,
      profiledLeftReceiverStrategy, pairedLeftInformedForRow,
      profiledOpenHiddenDescriptorLeftRootOfEq_rootToEq] using
      (hleftPhysical.trans (hpair.trans hrightPhysical.symm))

end

section
omit [Inhabited I]

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenWitnessedRightSenderOutput_dependentEvaluation_pair
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) :
    profiledOpenWitnessedRightSenderOutput A initialCode
        (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable left row) inputOne =
      profiledOpenWitnessedRightSenderOutput A initialCode
        (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable right row) inputOne :=
  rfl

theorem profiledOpenWitnessedLeftSenderOutput_dependentEvaluation_pair
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (row : PairedEntryRow) (inputTwo : In₂) :
    profiledOpenWitnessedLeftSenderOutput A initialCode
        (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable left row) inputTwo =
      profiledOpenWitnessedLeftSenderOutput A initialCode
        (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable right row) inputTwo :=
  rfl

/-- Exact right receiver gate at one public query.  There is no hidden
orientation premise behind this equivalence. -/
theorem profiledOpenWitnessedRightReceiverOutput_dependentEvaluation_pair_iff
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightReceiverOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
        profiledOpenWitnessedRightReceiverOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo ↔
      pairedRightInformedForRow row
          (profiledOpenFixedRightQueryResponses A initialCode value query
            left.1.1 ((left.1.2, inputTwo), inputOne)).1.physical =
        pairedRightInformedForRow row
          (profiledOpenFixedRightQueryResponses A initialCode value query
            right.1.1 ((right.1.2, inputTwo), inputOne)).1.physical :=
  Iff.rfl

/-- Left exact receiver gate. -/
theorem profiledOpenWitnessedLeftReceiverOutput_dependentEvaluation_pair_iff
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
        profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo ↔
      pairedLeftInformedForRow row
          (profiledOpenFixedLeftQueryResponses A initialCode value query
            left.1.1 ((left.1.2, inputOne), inputTwo)).1.physical =
        pairedLeftInformedForRow row
          (profiledOpenFixedLeftQueryResponses A initialCode value query
            right.1.1 ((right.1.2, inputOne), inputTwo)).1.physical :=
  Iff.rfl

end

end

/-! ## The exact reachable pair passes for retained shape-free provenance -/

section
omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenWitnessedRightReceiverOutput_dependentEvaluation_pair
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    (hprovenance :
      ProfiledOpenActiveRightFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value)
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightReceiverOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedRightReceiverOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo := by
  apply (profiledOpenWitnessedRightReceiverOutput_dependentEvaluation_pair_iff
    A strategy hwin basis initialCode reachable left right row inputOne
      inputTwo).2
  exact profiledOpenFixedRightQueryResponses_dependentEvaluation_physical_pair
    A strategy hwin basis initialCode source hprovenance reachable left right
      row inputOne inputTwo

theorem profiledOpenWitnessedLeftReceiverOutput_dependentEvaluation_pair
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    (hprovenance :
      ProfiledOpenActiveLeftFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value)
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo := by
  apply (profiledOpenWitnessedLeftReceiverOutput_dependentEvaluation_pair_iff
    A strategy hwin basis initialCode reachable left right row inputOne
      inputTwo).2
  exact profiledOpenFixedLeftQueryResponses_dependentEvaluation_physical_pair
    A strategy hwin basis initialCode source hprovenance reachable left right
      row inputOne inputTwo

theorem profiledOpenWitnessedRightPhysicalOutput_dependentEvaluation_pair
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    (hprovenance :
      ProfiledOpenActiveRightFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value)
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightPhysicalOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedRightPhysicalOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo := by
  apply Prod.ext
  · exact profiledOpenWitnessedRightSenderOutput_dependentEvaluation_pair A
      strategy hwin basis initialCode reachable left right row inputOne
  · exact profiledOpenWitnessedRightReceiverOutput_dependentEvaluation_pair
      A strategy hwin basis initialCode source hprovenance reachable left right
        row inputOne inputTwo

theorem profiledOpenWitnessedLeftPhysicalOutput_dependentEvaluation_pair
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    (hprovenance :
      ProfiledOpenActiveLeftFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value)
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftPhysicalOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedLeftPhysicalOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo := by
  apply Prod.ext
  · exact profiledOpenWitnessedLeftReceiverOutput_dependentEvaluation_pair A
      strategy hwin basis initialCode source hprovenance reachable left right
        row inputOne inputTwo
  · exact profiledOpenWitnessedLeftSenderOutput_dependentEvaluation_pair A
      strategy hwin basis initialCode reachable left right row inputTwo

end

end

end DetParityAutomaton

end DistributedSynthesis
