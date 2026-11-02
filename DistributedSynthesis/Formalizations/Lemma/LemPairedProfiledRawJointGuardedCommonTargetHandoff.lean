/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedPhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBothRestart
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalDirection

/-!
# Merging the two one-sided targets at a simultaneous close

The right sibling monitor emits only the new left lane and the left sibling
monitor emits only the new right lane.  At a genuine simultaneous close the
two directions have the same non-dummy data as one `both` restart.  Hence the
two finite targets reconstruct the complete common incidence code, including
the cross-incidence matrix.

This is deliberately only a finite-code handoff.  An incidence code does not
determine the semantic world's blind lambdas, so it does not by itself select
the next guarded sibling tables.  A provenance-free recursive carrier must
therefore put those finite guarded-move indices in its target alphabet as
additional data; choosing a fresh semantic world with the reconstructed code
would reintroduce the representative mismatch.
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

/-! ## The finite merge -/

/-- Combine the live marginal lane of each one-sided target and recompute the
cross-incidence matrix from the joint simultaneous direction.  The arguments
are ordered by the physical block that emitted them: right-block target first,
left-block target second. -/
noncomputable def profiledRawJointBothTargetMerge
    (input : In₁ × In₂)
    (rightTarget leftTarget : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  let direction := profiledRawJointBothRestartDirection input
  let right := leftTarget.family.right
  let left := rightTarget.family.left
  { family :=
      { right := right
        left := left
        rightPattern := leftTarget.family.rightPattern
        leftPattern := rightTarget.family.leftPattern }
    cross := profiledRawJointSuccessorCrossIncidence A direction right left }

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The pair of literal one-sided `.both` targets reconstructs exactly the
full source-free common successor.  No semantic representative is chosen in
this calculation. -/
theorem profiledRawJointBothTargetMerge_oneSidedNext
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (input : In₁ × In₂) :
    profiledRawJointBothTargetMerge A input
        (profiledRawJointOneSidedNext A code move
          (profiledRawJointUnitRightActualDirection
            (In₁ := In₁) (In₂ := In₂) .both [] (input.2, input.1)))
        (profiledRawJointOneSidedNext A code move
          (profiledRawJointUnitLeftActualDirection
            (In₁ := In₁) (In₂ := In₂) .both [] input)) =
      profiledRawJointIncidenceNext A code.family move
        (profiledRawJointBothRestartDirection input) := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Semantic form: when the source is one literal common world, the merged
targets are the incidence code of its literal next common world. -/
theorem profiledRawJointBothTargetMerge_eq_commonWorldAfterBoth
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (input : In₁ × In₂) :
    let family := profiledRawJointCommonWorldFamily A world
    profiledRawJointBothTargetMerge A input
        (profiledRawJointOneSidedNext A (family.incidenceCode A)
          (family.move A)
          (profiledRawJointUnitRightActualDirection
            (In₁ := In₁) (In₂ := In₂) .both [] (input.2, input.1)))
        (profiledRawJointOneSidedNext A (family.incidenceCode A)
          (family.move A)
          (profiledRawJointUnitLeftActualDirection
            (In₁ := In₁) (In₂ := In₂) .both [] input)) =
      (profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A world input)).incidenceCode A := by
  dsimp only
  rw [profiledRawJointBothTargetMerge_oneSidedNext A]
  exact (profiledRawJointCommonWorldAfterBoth_incidenceCode A world input).symm

/-! ## Reading the guarded semantic records -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- The target stored in the literal guarded right root is the corresponding
one-sided successor of the common sibling (`false`) root. -/
theorem profiledRawJointRightSiblingLiteralRootRecord_target_both
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (input : In₂ × In₁) :
    (profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
      semanticMember hmember input).2.1.target .both =
      profiledRawJointOneSidedNext A
        ((family.semanticChild A direction).incidenceCode A)
        ((family.semanticChild A direction).move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) .both [] input) := by
  rfl

/-- Left mirror. -/
theorem profiledRawJointLeftSiblingLiteralRootRecord_target_both
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (input : In₁ × In₂) :
    (profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
      semanticMember hmember input).2.1.target .both =
      profiledRawJointOneSidedNext A
        ((family.semanticChild A direction).incidenceCode A)
        ((family.semanticChild A direction).move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) .both [] input) := by
  rfl

/-- Consequently the two complete literal guarded roots of one semantic
common child merge to the exact finite code of its next literal common child.
This statement still carries no independently selected representative. -/
theorem profiledRawJointSiblingLiteralRootRecords_merge_eq_commonWorldAfterBoth
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (hchild : family.semanticChild A direction =
      profiledRawJointCommonWorldFamily A world)
    (input : In₁ × In₂) :
    let hright : (family.semanticChild A direction).right () =
        some (world.procOneMember A) := by rw [hchild]; rfl
    let hleft : (family.semanticChild A direction).left () =
        some (world.procTwoMember A) := by rw [hchild]; rfl
    profiledRawJointBothTargetMerge A input
        ((profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
          (world.procOneMember A) hright (input.2, input.1)).2.1.target .both)
        ((profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
          (world.procTwoMember A) hleft input).2.1.target .both) =
      (profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A world input)).incidenceCode A := by
  dsimp only
  rw [profiledRawJointRightSiblingLiteralRootRecord_target_both A,
    profiledRawJointLeftSiblingLiteralRootRecord_target_both A]
  rw [hchild]
  exact profiledRawJointBothTargetMerge_eq_commonWorldAfterBoth A world input

end

/-- Actual-controller form of the handoff.  The records below are read from
the narrowed finite guarded controllers, not from the semantic strategies.
The first-record guards replace both records by the literal sibling records;
the preceding theorem then performs the common-code merge. -/
theorem
    profiledRawJointGuardedSiblingControllerRootRecords_merge_eq_commonWorldAfterBoth
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (hchild : family.semanticChild A direction =
      profiledRawJointCommonWorldFamily A world)
    (rightMember leftMember : Bool) (input : In₁ × In₂) :
    let hright : (family.semanticChild A direction).right () =
        some (world.procOneMember A) := by rw [hchild]; rfl
    let hleft : (family.semanticChild A direction).left () =
        some (world.procTwoMember A) := by rw [hchild]; rfl
    let rightMove := profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin
      family direction (world.procOneMember A) hright
    let leftMove := profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin
      family direction (world.procTwoMember A) hleft
    let rightRecord := narrowedRecord
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember)
      ((rightMove.memberController A rightMember).labeledTree [])
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember).initial (input.2, input.1)
    let leftRecord := narrowedRecord
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember)
      ((leftMove.memberController A leftMember).labeledTree [])
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember).initial input
    profiledRawJointBothTargetMerge A input
        (rightRecord.2.1.target .both) (leftRecord.2.1.target .both) =
      (profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A world input)).incidenceCode A := by
  dsimp only
  rw [profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record A,
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record A]
  exact
    profiledRawJointSiblingLiteralRootRecords_merge_eq_commonWorldAfterBoth A
      hwin family direction world hchild input

/-! ## The matching physical simultaneous round -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The informed `.both` projections in the two literal sibling records are
the two outputs of one literal original-strategy round at the common world.
The equality is definitional once both semantic members are taken from that
same world. -/
theorem profiledRawJointSiblingLiteralRootRecords_bothOutput_eq_literal
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (hchild : family.semanticChild A direction =
      profiledRawJointCommonWorldFamily A world)
    (input : In₁ × In₂) :
    let hright : (family.semanticChild A direction).right () =
        some (world.procOneMember A) := by rw [hchild]; rfl
    let hleft : (family.semanticChild A direction).left () =
        some (world.procTwoMember A) := by rw [hchild]; rfl
    let rightRecord :=
      profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
        (world.procOneMember A) hright (input.2, input.1)
    let leftRecord :=
      profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
        (world.procTwoMember A) hleft input
    (pairedLeftInformedForRow .both leftRecord.2.1.physical,
        pairedRightInformedForRow .both rightRecord.2.1.physical) =
      let round := nextRound strategy (world.procOne A).bothHistory
        ⟨input.1, input.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  rfl

/-- Actual narrowed-controller form of the physical equation.  Together with
`profiledRawJointGuardedSiblingControllerRootRecords_merge_eq_commonWorldAfterBoth`
this says that the same two finite root records reproduce both the literal
physical round and its exact next common incidence code. -/
theorem
    profiledRawJointGuardedSiblingControllerRootRecords_bothOutput_eq_literal
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (hchild : family.semanticChild A direction =
      profiledRawJointCommonWorldFamily A world)
    (rightMember leftMember : Bool) (input : In₁ × In₂) :
    let hright : (family.semanticChild A direction).right () =
        some (world.procOneMember A) := by rw [hchild]; rfl
    let hleft : (family.semanticChild A direction).left () =
        some (world.procTwoMember A) := by rw [hchild]; rfl
    let rightMove := profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin
      family direction (world.procOneMember A) hright
    let leftMove := profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin
      family direction (world.procTwoMember A) hleft
    let rightRecord := narrowedRecord
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember)
      ((rightMove.memberController A rightMember).labeledTree [])
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember).initial (input.2, input.1)
    let leftRecord := narrowedRecord
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember)
      ((leftMove.memberController A leftMember).labeledTree [])
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember).initial input
    (pairedLeftInformedForRow .both leftRecord.2.1.physical,
        pairedRightInformedForRow .both rightRecord.2.1.physical) =
      let round := nextRound strategy (world.procOne A).bothHistory
        ⟨input.1, input.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  dsimp only
  rw [profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record A,
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record A]
  exact profiledRawJointSiblingLiteralRootRecords_bothOutput_eq_literal A
    hwin family direction world hchild input

end

end DetParityAutomaton

end DistributedSynthesis
