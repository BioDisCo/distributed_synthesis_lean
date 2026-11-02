/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTwoProcessClockPolicyClassification
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove

/-!
# The actual target constraint excludes the clock obstruction for alwaysGrant

The closing target stores the strict successor as well as the simultaneous
successor. For the constant winning source `alwaysGrant`, every allowed
semantic target has strict successor `true`. Target safety therefore forces
every strict letter of every accepted physical sibling move to grant, in
either row and either hidden sibling member.

This is a source-specific audit of the physical moves. It does not establish
acceptance of the mixed owner runtime, nor a replacement theorem for arbitrary
winning sources, which can have non-granting finite prefixes.
-/

namespace DistributedSynthesis
namespace TwoProcessPhysicalTargetAudit

open DetParityAutomaton TwoProcessNoResetReversalObstruction

noncomputable section

/-- Read the strict DPA successor; a missing entry has no grant. -/
def strictState : PairedEntryTreeState objective → Bool
  | .inl _ => false
  | .inr (.inl slot) => slot.1.1
  | .inr (.inr slot) => slot.1.1

theorem strictState_rightClose (scan : PairedRightScanState objective)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := Unit) (In₂ := Unit) (Out₁ := Bool) (Out₂ := Bool)) :
    strictState (pairedRightCloseTarget objective scan row letter) =
      grant (pairedRightRecordForRow row letter) := by
  cases row <;> rfl

theorem strictState_leftClose (scan : PairedLeftScanState objective)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := Unit) (In₂ := Unit) (Out₁ := Bool) (Out₂ := Bool)) :
    strictState (pairedLeftCloseTarget objective scan row letter) =
      grant (pairedLeftRecordForRow row letter) := by
  cases row <;> rfl

/-- Even when the root DPA state is rejecting, every allowed strict successor
of the constant source is accepting. No condition on the block minimum is
needed for this implication. -/
theorem right_allowed_strictState
    (family : ProfiledRawJointSemanticFamily objective alwaysGrant (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (semanticMember : ProcOnePairedEntryRep alwaysGrant × objective.State)
    (hmember : (family.semanticChild objective direction).right () =
      some semanticMember)
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget objective
      family direction target) :
    strictState (erasePairedProfiledState objective
      (profiledRawJointUnitRightTargetProjection objective target)) = true := by
  obtain ⟨row, past, input, rfl⟩ := hallowed
  have h := (profiledRawJointRightSiblingActivation objective alwaysGrant_wins
    family direction semanticMember hmember false).target_state row past input
  change profiledRawJointUnitRightTargetProjection objective
    (profiledRawJointOneSidedNext objective
      ((profiledRawJointRightSiblingFamily objective family direction false
        ).incidenceCode objective)
      ((profiledRawJointRightSiblingFamily objective family direction false
        ).move objective)
      (profiledRawJointUnitRightActualDirection row past input)) =
    .inr (.inr (profiledRawRightChildSlot objective
      (profiledRawRightSlotOfSemanticPair objective semanticMember)
      semanticMember.1.lambdaOfStrategy row past input)) at h
  rw [h]
  cases row <;> rfl

theorem left_allowed_strictState
    (family : ProfiledRawJointSemanticFamily objective alwaysGrant (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (semanticMember : ProcTwoPairedEntryRep alwaysGrant × objective.State)
    (hmember : (family.semanticChild objective direction).left () =
      some semanticMember)
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointLeftSiblingSharedAllowedTarget objective
      family direction target) :
    strictState (erasePairedProfiledState objective
      (profiledRawJointUnitLeftTargetProjection objective target)) = true := by
  obtain ⟨row, past, input, rfl⟩ := hallowed
  have h := (profiledRawJointLeftSiblingActivation objective alwaysGrant_wins
    family direction semanticMember hmember false).target_state row past input
  change profiledRawJointUnitLeftTargetProjection objective
    (profiledRawJointOneSidedNext objective
      ((profiledRawJointLeftSiblingFamily objective family direction false
        ).incidenceCode objective)
      ((profiledRawJointLeftSiblingFamily objective family direction false
        ).move objective)
      (profiledRawJointUnitLeftActualDirection row past input)) =
    .inr (.inl (profiledRawLeftChildSlot objective
      (profiledRawLeftSlotOfSemanticPair objective semanticMember)
      semanticMember.1.lambdaOfStrategy row past input)) at h
  rw [h]
  cases row <;> rfl

/-- Every accepted finite table with this semantic descriptor grants on
every strict letter. This does not depend on which rationalization is chosen. -/
theorem right_physical_grants
    (family : ProfiledRawJointSemanticFamily objective alwaysGrant (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (semanticMember : ProcOnePairedEntryRep alwaysGrant × objective.State)
    (hmember : (family.semanticChild objective direction).right () =
      some semanticMember)
    (move : ProfiledRawJointRightPhysicalSiblingMove objective)
    (hdescriptor : move.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction semanticMember)
    (member : Bool) (env : Nat → Unit × Unit) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointRightPhysicalSiblingMonitor objective
      move.1 member
    let play := treePlay (narrowedInducedTree monitor
      (move.memberController objective member).labeledTree) env
    grant (pairedRightRecordForRow row
      (profiledRawJointTargetRightPhysicalLetter objective (play n))) = true := by
  obtain ⟨hclose, hallowed⟩ := move.memberController_targetSafe objective
    member env n row
  nth_rw 1 [hdescriptor] at hallowed
  rw [profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff] at hallowed
  have hgrant := right_allowed_strictState family direction semanticMember
    hmember _ hallowed
  rw [hclose, strictState_rightClose] at hgrant
  exact hgrant

theorem left_physical_grants
    (family : ProfiledRawJointSemanticFamily objective alwaysGrant (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (semanticMember : ProcTwoPairedEntryRep alwaysGrant × objective.State)
    (hmember : (family.semanticChild objective direction).left () =
      some semanticMember)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hdescriptor : move.1 = profiledRawJointLeftPhysicalSiblingDescriptorOf
      objective family direction semanticMember)
    (member : Bool) (env : Nat → Unit × Unit) (n : Nat)
    (row : PairedEntryRow) :
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor objective
      move.1 member
    let play := treePlay (narrowedInducedTree monitor
      (move.memberController objective member).labeledTree) env
    grant (pairedLeftRecordForRow row
      (profiledRawJointTargetLeftPhysicalLetter objective (play n))) = true := by
  obtain ⟨hclose, hallowed⟩ := move.memberController_targetSafe objective
    member env n row
  nth_rw 1 [hdescriptor] at hallowed
  rw [profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff] at hallowed
  have hgrant := left_allowed_strictState family direction semanticMember
    hmember _ hallowed
  rw [hclose, strictState_leftClose] at hgrant
  exact hgrant

/-! ## The exclusion really depends on the source -/

/-- Both endpoints grant on the same recurring clock phase. -/
def pulsedSource : StrategyPair Unit Unit Bool Bool where
  one := clock
  two := clock

theorem pulsedSource_wins (env : EnvironmentSequence Unit Unit) :
    objective.Accepts (execution pulsedSource env) := by
  let policy : TwoProcessClockPolicyClassification.Policy := ⟨id, id, id, id⟩
  have heq : TwoProcessClockPolicyClassification.strategy policy =
      pulsedSource := by
    simp [TwoProcessClockPolicyClassification.strategy, policy, pulsedSource]
  rw [← heq]
  exact TwoProcessClockPolicyClassification.jointlyGood_wins policy
    ⟨true, rfl, rfl⟩ env

theorem pulsedSource_right_blind_toggles
    (entry : ProcOnePairedEntryRep pulsedSource) :
    entry.lambdaOfStrategy.blind [()] () =
      !entry.lambdaOfStrategy.blind [] () := by
  change clock (nextView .one
      (extendPrefix pulsedSource entry.leftHistory [rightEnvironment ((), ())])
      (rightEnvironment ((), ()))) =
    !clock (nextView .one entry.leftHistory (rightEnvironment ((), ())))
  simp only [extendPrefix, List.foldl_cons, List.foldl_nil]
  rw [nextView_one_of_graph_right _ _ rfl, currentView_append_nextRound,
    clock_noRecv]

/-- A genuine winning source can have allowed targets with rejecting strict
successors. At any live right entry, one of the first two strict letters of
the pulsed source supplies such a target, with its actual stored profile and
block minimum intact. This is not a losing physical-move construction. -/
theorem pulsedSource_has_nonGranting_allowed_right_target
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (semanticMember : ProcOnePairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).right () =
      some semanticMember) :
    ∃ target : ProfiledRawJointUnitTarget objective,
      ProfiledRawJointRightSiblingSharedAllowedTarget objective
        family direction target ∧
      strictState (erasePairedProfiledState objective
        (profiledRawJointUnitRightTargetProjection objective target)) = false := by
  have hex : ∃ past : List (Unit × Unit),
      semanticMember.1.lambdaOfStrategy.blind (senderWord past) () = false := by
    cases h : semanticMember.1.lambdaOfStrategy.blind [] () with
    | false => exact ⟨[], h⟩
    | true =>
      refine ⟨[((), ())], ?_⟩
      change semanticMember.1.lambdaOfStrategy.blind [()] () = false
      rw [pulsedSource_right_blind_toggles, h]
      rfl
  obtain ⟨past, hpast⟩ := hex
  let activation := profiledRawJointRightSiblingActivation objective
    pulsedSource_wins family direction semanticMember hmember false
  refine ⟨activation.target .first past ((), ()),
    activation.target_allowed .first past ((), ()), ?_⟩
  rw [activation.target_state]
  change (semanticMember.1.lambdaOfStrategy.blind (senderWord past) () &&
    semanticMember.1.lambdaOfStrategy.informedLeft past ((), ())) = false
  rw [hpast]
  rfl

end
end TwoProcessPhysicalTargetAudit
end DistributedSynthesis
