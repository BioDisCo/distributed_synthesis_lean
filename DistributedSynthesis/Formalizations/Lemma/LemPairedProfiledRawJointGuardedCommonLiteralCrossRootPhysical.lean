/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossBothPhysical
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSwitchConstructorPinning

/-!
# Full root records of the retained literal cross tables

The simultaneous-output readback only projects the `informedBoth` fields of
the two retained tables.  The tail switch needs one more coordinate: the
`closingBoth` field of the table which is continued across the switch.  Both
coordinates are already fixed by the literal first-record guard.  This file
exposes that stronger, full-record statement without adding any runtime
information.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Literal roots before comparison with the guarded pair -/

/-- The complete physical receiver record at the root of the retained right
literal table is the record of the exact semantic activation from which the
table was extracted. -/
theorem profiledRawJointGuardedCommonRightLiteralCrossOfPoint_rootPhysical
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiver
      input.2 input.1).1.physical =
        (profiledRawJointTargetRightReceiverStrategy A
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point)) []
          (input.2, input.1)).physical := by
  classical
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
      installed
  let baseMonitor :=
    profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin
      installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  let move :=
    profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy hwin
      point
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  let firstRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial (input.2, input.1)
  have hallowed :=
    move.memberController_records_allowed monitor anchor
      (input.2, input.1) default
  have hrecord : firstRecord =
      ((input.2, input.1),
        profiledRawJointTargetRightReceiverStrategy A activation []
          (input.2, input.1),
        pairedRightSenderStrategy activation.lambda [] (input.2, input.1).2) := by
    have hfirst : finiteCrossAnchorLiteralFirstAllowed
        (profiledRawJointTargetRightReceiverStrategy A activation)
        (pairedRightSenderStrategy activation.lambda) firstRecord = true := by
      simpa [move, monitor, monitorFamily, firstAllowed, secondAllowed,
        profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint,
        finiteCrossAnchorLiteralPrefixMove, descriptor, baseMonitor,
        activation, installed] using hallowed.1
    exact of_decide_eq_true hfirst
  change firstRecord.2.1.physical = _
  rw [hrecord]

/-- Left mirror. -/
theorem profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_rootPhysical
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy hwin
        point
    let receiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiver
      input.1 input.2).1.physical =
        (profiledRawJointTargetLeftReceiverStrategy A
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point)) []
          input).physical := by
  classical
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  let move :=
    profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy hwin
      point
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  let firstRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial input
  have hallowed :=
    move.memberController_records_allowed monitor anchor input default
  have hrecord : firstRecord =
      (input,
        profiledRawJointTargetLeftReceiverStrategy A activation [] input,
        pairedLeftSenderStrategy activation.lambda [] input.2) := by
    have hfirst : finiteCrossAnchorLiteralFirstAllowed
        (profiledRawJointTargetLeftReceiverStrategy A activation)
        (pairedLeftSenderStrategy activation.lambda) firstRecord = true := by
      simpa [move, monitor, monitorFamily, firstAllowed, secondAllowed,
        profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint,
        finiteCrossAnchorLiteralPrefixMove, descriptor, baseMonitor,
        activation, installed,
        profiledRawJointGuardedCommonLeftLiteralCrossMonitor] using hallowed.1
    exact of_decide_eq_true hfirst
  change firstRecord.2.1.physical = _
  rw [hrecord]

/-! ## Identification with the represented guarded pair -/

/-- The right literal table and the right guarded root extracted at the same
semantic occurrence have the same complete physical receiver record. -/
theorem
    profiledRawJointGuardedCommonRightLiteralCrossOfPoint_rootPhysical_eq_pair
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiver
      input.2 input.1).1.physical =
        ((point.move A strategy hwin).rightRootRecord A strategy hwin input
          ).2.1.physical := by
  dsimp only
  rw [profiledRawJointGuardedCommonRightLiteralCrossOfPoint_rootPhysical]
  change pairedRightReceiverStrategy
      (profiledRawJointHybridExactRightActivation A hwin
        (profiledRawJointGuardedCommonPointInstalled A strategy point)).lambda
      [] (input.2, input.1) = _
  rw [profiledRawJointHybridExactRightActivation_lambda_eq]
  unfold ProfiledRawJointGuardedCommonSemanticPoint.move
    ProfiledRawJointGuardedCommonPair.rightRootRecord
    profiledRawJointGuardedCommonPairOfWorld
    profiledRawJointGuardedCommonRightMoveOfWorld
  rw [profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record]
  rfl

/-- Left mirror. -/
theorem
    profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_rootPhysical_eq_pair
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy hwin
        point
    let receiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiver
      input.1 input.2).1.physical =
        ((point.move A strategy hwin).leftRootRecord A strategy hwin input
          ).2.1.physical := by
  dsimp only
  rw [profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_rootPhysical]
  change pairedLeftReceiverStrategy
      (profiledRawJointHybridExactLeftActivation A hwin
        (profiledRawJointGuardedCommonPointInstalled A strategy point)).lambda
      [] input = _
  rw [profiledRawJointHybridExactLeftActivation_lambda_eq]
  unfold ProfiledRawJointGuardedCommonSemanticPoint.move
    ProfiledRawJointGuardedCommonPair.leftRootRecord
    profiledRawJointGuardedCommonPairOfWorld
    profiledRawJointGuardedCommonLeftMoveOfWorld
  rw [profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record]
  rfl

/-! ## Operational successor readback -/

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

/-- At a reachable decorated-policy successor, the two retained literal
receiver roots are the complete two receiver roots of `nextPairAt`.  This is
the full-record strengthening of
`successorLiteralCross_bothPhysicalOutputs_eq_nextPairCut`. -/
theorem successorLiteralCross_rootPhysical_eq_nextPairRoots
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) :
    let extra := package.nextExtraAt A strategy hwin state incoming
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        rightReceiver blockInput.2 blockInput.1).1.physical,
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        leftReceiver blockInput.1 blockInput.2).1.physical) =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical) := by
  rcases package.exists_point_of_nextLiteralCrossInitial A strategy hwin
      hreachable incoming with ⟨point, _hcode, hmove, hextra⟩
  dsimp only
  rw [← hextra, ← hmove]
  apply Prod.ext
  · exact
      profiledRawJointGuardedCommonRightLiteralCrossOfPoint_rootPhysical_eq_pair
        A strategy hwin point rightAnchor blockInput
  · exact
      profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_rootPhysical_eq_pair
        A strategy hwin point leftAnchor blockInput

/-! ## Small adapter into the live-tail pinning interface -/

/-- Exact constructor-side obligation: the two physical records selected by
the live-tail successor are the two retained literal roots at the same
decorated-policy successor.  This statement mentions only finite runtime
data.  In particular it does not reveal the current hierarchy side to either
process. -/
def TailNextMatchesLiteralCrossRoots
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming : In₁ × In₂)
    (tag : Tag A strategy hwin)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag)
    (rightAnchor leftAnchor : Bool) : Prop :=
  ∀ blockInput : In₁ × In₂,
    let extra := package.nextExtraAt A strategy hwin state incoming
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    (profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy
        hwin tag fallbackRight next.1 next.2 blockInput).physical =
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
          rightReceiver blockInput.2 blockInput.1).1.physical ∧
      (profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy
        hwin tag fallbackLeft next.1 next.2 blockInput).physical =
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
          leftReceiver blockInput.1 blockInput.2).1.physical

/-- Once the live-tail constructor installs exactly the retained literal
roots, the already-proved same-occurrence theorem supplies the complete
`TailSuccessorPinnedToPair` packet.  Thus the remaining implementation task
is only the finite constructor match above, not a new semantic equality. -/
theorem tailSuccessorPinnedToPair_of_matchesLiteralCrossRoots
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming : In₁ × In₂)
    (tag : Tag A strategy hwin)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag)
    (rightAnchor leftAnchor : Bool)
    (hmatch : package.TailNextMatchesLiteralCrossRoots A strategy hwin state
      incoming tag fallbackLeft fallbackRight next rightAnchor leftAnchor) :
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair A strategy
      hwin tag fallbackLeft fallbackRight next
        (package.nextPairAt A strategy hwin state incoming) := by
  intro blockInput
  have hroots := package.successorLiteralCross_rootPhysical_eq_nextPairRoots
    A strategy hwin hreachable incoming blockInput rightAnchor leftAnchor
  exact ⟨(hmatch blockInput).1.trans (congrArg Prod.fst hroots),
    (hmatch blockInput).2.trans (congrArg Prod.snd hroots)⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
