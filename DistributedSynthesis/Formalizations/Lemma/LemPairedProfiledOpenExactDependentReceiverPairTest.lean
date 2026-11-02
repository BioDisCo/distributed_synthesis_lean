/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenDependentMemberPairTest

/-!
# Exact dependent receiver pair test

This is the operational fail-fast test for the last member/root ambiguity.
Two erased re-anchored evaluations of the same physical descriptor, value,
and query must emit the same informed physical output.  The proof opens only
one evaluation's semantic-table witness and compares both dependent roots at
its single common semantic past.  It neither selects nor reconstructs a
leader, orientation, member, or root.
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

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- **PASS, right side.**  All dependent member/root evaluations of one
reachable fixed query have the same literal process-two output. -/
theorem profiledOpenWitnessedRightReceiverOutput_exactDependent_pair
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
            basis initialCode reachable right row) inputOne inputTwo := by
  rcases left with ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
  rcases right with ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  have hmember : leftMember = rightMember :=
    profiledOpenFixedRightReanchoredRowEvaluation_member_eq A strategy hwin
      basis initialCode ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
        ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  cases hmember
  change pairedRightInformedForRow row
        (profiledOpenFixedRightQueryResponses A initialCode value query
          leftMember ((leftHiddenRoot, inputTwo), inputOne)).1.physical =
      pairedRightInformedForRow row
        (profiledOpenFixedRightQueryResponses A initialCode value query
          leftMember ((rightHiddenRoot, inputTwo), inputOne)).1.physical
  rcases hleftEvaluation with
    ⟨witness, _hmember, lane, hlane, _hdescriptor, hmove, _hroot,
      hsemantic⟩
  rcases hsemantic with ⟨past, hpast⟩
  let leftRoot := profiledOpenHiddenDescriptorRightRootToEq A leftMember.1
    lane.source
    ((lane.realization.coherentTable A).table.toClassified A lane.source)
    hmove leftHiddenRoot
  let rightRoot := profiledOpenHiddenDescriptorRightRootToEq A leftMember.1
    lane.source
    ((lane.realization.coherentTable A).table.toClassified A lane.source)
    hmove rightHiddenRoot
  have hleft := congrFun hpast ((leftRoot, inputTwo), inputOne)
  have hright := congrFun hpast ((rightRoot, inputTwo), inputOne)
  have hview :
      currentView Proc.one
          (lane.realization.entry leftRoot).leftHistory =
        currentView Proc.one
          (lane.realization.entry rightRoot).leftHistory :=
    (lane.realization.view_eq leftRoot).trans
      (lane.realization.view_eq rightRoot).symm
  have hreceiver :=
    procOnePairedEntry_rightReceiverForRow_eq_of_fresh_view_eq strategy
      (lane.realization.entry leftRoot)
      (lane.realization.entry rightRoot)
      (witness.state.1.rightFresh lane hlane leftRoot)
      (witness.state.1.rightFresh lane hlane rightRoot) hview row
  let physicalPast := past.map (fun old ↦ (old.1.2, old.2))
  have hat := congrFun (congrFun hreceiver physicalPast)
    (inputTwo, inputOne)
  have hleftPhysical := congrArg
    (fun output : ProfiledOpenRightClassifiedOutput A ↦
      pairedRightInformedForRow row output.1.physical) hleft
  have hrightPhysical := congrArg
    (fun output : ProfiledOpenRightClassifiedOutput A ↦
      pairedRightInformedForRow row output.1.physical) hright
  cases row <;>
    simpa [leftRoot, rightRoot, physicalPast,
      profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenRightSemanticClassifiedReceiver,
      profiledRightReceiverStrategy, pairedRightInformedForRow,
      procOnePairedEntryRightReceiverForRow,
      ProcOnePairedEntryRep.lambdaOfStrategy,
      profiledOpenHiddenDescriptorRightRootOfEq_rootToEq] using
      (hleftPhysical.trans (hat.trans hrightPhysical.symm))

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- **PASS, left side.**  Mirror of the exact right pair test. -/
theorem profiledOpenWitnessedLeftReceiverOutput_exactDependent_pair
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo := by
  rcases left with ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
  rcases right with ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  have hmember : leftMember = rightMember :=
    profiledOpenFixedLeftReanchoredRowEvaluation_member_eq A strategy hwin
      basis initialCode ⟨⟨leftMember, leftHiddenRoot⟩, hleftEvaluation⟩
        ⟨⟨rightMember, rightHiddenRoot⟩, hrightEvaluation⟩
  cases hmember
  change pairedLeftInformedForRow row
        (profiledOpenFixedLeftQueryResponses A initialCode value query
          leftMember ((leftHiddenRoot, inputOne), inputTwo)).1.physical =
      pairedLeftInformedForRow row
        (profiledOpenFixedLeftQueryResponses A initialCode value query
          leftMember ((rightHiddenRoot, inputOne), inputTwo)).1.physical
  rcases hleftEvaluation with
    ⟨witness, _hmember, lane, hlane, _hdescriptor, hmove, _hroot,
      hsemantic⟩
  rcases hsemantic with ⟨past, hpast⟩
  let leftRoot := profiledOpenHiddenDescriptorLeftRootToEq A leftMember.1
    lane.source
    ((lane.realization.coherentTable A).table.toClassified A lane.source)
    hmove leftHiddenRoot
  let rightRoot := profiledOpenHiddenDescriptorLeftRootToEq A leftMember.1
    lane.source
    ((lane.realization.coherentTable A).table.toClassified A lane.source)
    hmove rightHiddenRoot
  have hleft := congrFun hpast ((leftRoot, inputOne), inputTwo)
  have hright := congrFun hpast ((rightRoot, inputOne), inputTwo)
  have hview :
      currentView Proc.two
          (lane.realization.entry leftRoot).rightHistory =
        currentView Proc.two
          (lane.realization.entry rightRoot).rightHistory :=
    (lane.realization.view_eq leftRoot).trans
      (lane.realization.view_eq rightRoot).symm
  have hreceiver :=
    procTwoPairedEntry_leftReceiverForRow_eq_of_fresh_view_eq strategy
      (lane.realization.entry leftRoot)
      (lane.realization.entry rightRoot)
      (witness.state.1.leftFresh lane hlane leftRoot)
      (witness.state.1.leftFresh lane hlane rightRoot) hview row
  let physicalPast := past.map (fun old ↦ (old.1.2, old.2))
  have hat := congrFun (congrFun hreceiver physicalPast)
    (inputOne, inputTwo)
  have hleftPhysical := congrArg
    (fun output : ProfiledOpenLeftClassifiedOutput A ↦
      pairedLeftInformedForRow row output.1.physical) hleft
  have hrightPhysical := congrArg
    (fun output : ProfiledOpenLeftClassifiedOutput A ↦
      pairedLeftInformedForRow row output.1.physical) hright
  cases row <;>
    simpa [leftRoot, rightRoot, physicalPast,
      profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenLeftSemanticClassifiedReceiver,
      profiledLeftReceiverStrategy, pairedLeftInformedForRow,
      procTwoPairedEntryLeftReceiverForRow,
      ProcTwoPairedEntryRep.lambdaOfStrategy,
      profiledOpenHiddenDescriptorLeftRootOfEq_rootToEq] using
      (hleftPhysical.trans (hat.trans hrightPhysical.symm))

end

end DetParityAutomaton

end DistributedSynthesis
