/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossMismatchPhase

/-!
# Simultaneous physical outputs of the retained literal cross tables

The right and left tables stored at one guarded common occurrence were
selected independently, but their first-record truth tables were extracted
from the same literal semantic world.  Consequently, if both endpoints take
their local receive transition at the installed roots, the two projected
physical outputs are exactly the two simultaneous outputs of that world.

The executable receiver maps remain completely local.  The semantic point is
used only in this readback theorem; no graph, orientation, leader bit, or
history is supplied to a runtime transition.
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

/-! ## Pointwise physical readback -/

/-- At the literal occurrence from which the right table was extracted, its
root receiver transition emits the process-two simultaneous output.  The
private anchor may be either member: the literal first-record predicate is
stored in both members of the table. -/
theorem profiledRawJointGuardedCommonRightLiteralCrossOfPoint_bothOutput
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
      receiver input.2 input.1).1 =
        (profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputTwo A input := by
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
  change pairedRightInformedForRow .both firstRecord.2.1.physical = _
  rw [hrecord]
  exact profiledRawJointHybridExactRightActivation_bothOutput A installed
    (profiledRawJointHybridExactRightPolicy A hwin installed)
    (profiledRawJointHybridExactRightActivation A hwin installed) input

/-- Process-one mirror of the preceding theorem. -/
theorem profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_bothOutput
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy hwin
        point
    let receiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
      receiver input.1 input.2).1 =
        (profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputOne A input := by
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
  change pairedLeftInformedForRow .both firstRecord.2.1.physical = _
  rw [hrecord]
  exact profiledRawJointHybridExactLeftActivation_bothOutput A installed
    (profiledRawJointHybridExactLeftPolicy A hwin installed)
    (profiledRawJointHybridExactLeftActivation A hwin installed) input

/-- Strong simultaneous-`both` compatibility: arbitrary private members of
the two independently selected literal tables emit the one coherent output
pair of their common semantic occurrence. -/
theorem profiledRawJointGuardedCommonLiteralCrossOfPoint_bothPhysicalOutputs
    (point : CommonPoint A strategy) (rightAnchor leftAnchor : Bool)
    (input : In₁ × In₂) :
    let extra :=
      profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
        point
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        leftReceiver input.1 input.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        rightReceiver input.2 input.1).1) =
      ((profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputOne A input,
        (profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputTwo A input) := by
  apply Prod.ext
  · exact profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_bothOutput
      A strategy hwin point leftAnchor input
  · exact profiledRawJointGuardedCommonRightLiteralCrossOfPoint_bothOutput
      A strategy hwin point rightAnchor input

/-- The old guarded pair attached to the same semantic occurrence describes
the very same simultaneous output.  This is the proof-side bridge from the
new literal table to the existing common-cut carrier. -/
theorem profiledRawJointGuardedCommonPoint_move_bothReceiverOutputs
    (point : CommonPoint A strategy) (input : In₁ × In₂) :
    (pairedLeftInformedForRow .both
        ((point.move A strategy hwin).leftRootRecord A strategy hwin input
          ).2.1.physical,
      pairedRightInformedForRow .both
        ((point.move A strategy hwin).rightRootRecord A strategy hwin input
          ).2.1.physical) =
      ((profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputOne A input,
        (profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputTwo A input) := by
  unfold ProfiledRawJointGuardedCommonSemanticPoint.move
    ProfiledRawJointGuardedCommonPair.rightRootRecord
    ProfiledRawJointGuardedCommonPair.leftRootRecord
    profiledRawJointGuardedCommonPairOfWorld
    profiledRawJointGuardedCommonRightMoveOfWorld
    profiledRawJointGuardedCommonLeftMoveOfWorld
  rw [profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record,
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record]
  rfl

/-- Direct common-cut form: the simultaneous outputs of the new literal
receiver roots are the two closing predictions of the old guarded pair from
the same occurrence. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossOfPoint_bothPhysicalOutputs_eq_cut
    (point : CommonPoint A strategy) (rightAnchor leftAnchor : Bool)
    (input : In₁ × In₂) :
    let extra :=
      profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
        point
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        leftReceiver input.1 input.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        rightReceiver input.2 input.1).1) =
      (((point.move A strategy hwin).rightRootRecord A strategy hwin input
          ).2.1.physical.closingBoth,
        ((point.move A strategy hwin).leftRootRecord A strategy hwin input
          ).2.1.physical.closingBoth) := by
  calc
    _ = ((profiledRawJointGuardedCommonPointInstalled A strategy point
            ).bothOutputOne A input,
          (profiledRawJointGuardedCommonPointInstalled A strategy point
            ).bothOutputTwo A input) :=
      profiledRawJointGuardedCommonLiteralCrossOfPoint_bothPhysicalOutputs
        A strategy hwin point rightAnchor leftAnchor input
    _ = (pairedLeftInformedForRow .both
            ((point.move A strategy hwin).leftRootRecord A strategy hwin input
              ).2.1.physical,
          pairedRightInformedForRow .both
            ((point.move A strategy hwin).rightRootRecord A strategy hwin
              input).2.1.physical) :=
      (profiledRawJointGuardedCommonPoint_move_bothReceiverOutputs A strategy
        hwin point input).symm
    _ = (((point.move A strategy hwin).rightRootRecord A strategy hwin input
            ).2.1.physical.closingBoth,
          ((point.move A strategy hwin).leftRootRecord A strategy hwin input
            ).2.1.physical.closingBoth) := by
      apply Prod.ext
      · exact ((point.move A strategy hwin).root_outputOne A strategy hwin
          input).symm
      · exact ((point.move A strategy hwin).root_outputTwo A strategy hwin
          input).symm

/-! ## Operational successor refresh -/

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

/-- At a reachable common-policy state, the annotation stored by the policy
successor passes the simultaneous-receive anti-mosaic test.  The witness
point is proof-only.  Operationally both receiver roots are built solely
from `extraAt (policy.successor state incoming)`, i.e. exactly the same ID as
`nextExtraAt state incoming`. -/
theorem exists_point_of_successorLiteralCross_bothPhysicalOutputs
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) :
    ∃ point : CommonPoint A strategy,
      point.code A strategy =
          (package.pairAt A strategy hwin state).bothNextCode A strategy hwin
            incoming ∧
        point.move A strategy hwin =
            package.nextPairAt A strategy hwin state incoming ∧
        let extra := package.extraAt A strategy hwin
          (package.policy.successor state incoming)
        let rightReceiver :=
          profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
            extra.1 rightAnchor
        let leftReceiver :=
          profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
            extra.2 leftAnchor
        ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
            leftReceiver blockInput.1 blockInput.2).1,
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
            rightReceiver blockInput.2 blockInput.1).1) =
          ((profiledRawJointGuardedCommonPointInstalled A strategy point
              ).bothOutputOne A blockInput,
            (profiledRawJointGuardedCommonPointInstalled A strategy point
              ).bothOutputTwo A blockInput) := by
  rcases package.exists_point_of_nextLiteralCrossInitial A strategy hwin
      hreachable incoming with ⟨point, hcode, hmove, hextra⟩
  refine ⟨point, hcode, hmove, ?_⟩
  change
    let extra := package.nextExtraAt A strategy hwin state incoming
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
          leftReceiver blockInput.1 blockInput.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
          rightReceiver blockInput.2 blockInput.1).1) =
      ((profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputOne A blockInput,
        (profiledRawJointGuardedCommonPointInstalled A strategy point
          ).bothOutputTwo A blockInput)
  rw [← hextra]
  exact
    profiledRawJointGuardedCommonLiteralCrossOfPoint_bothPhysicalOutputs
      A strategy hwin point rightAnchor leftAnchor blockInput

/-- Witness-free operational anti-mosaic handoff.  After one decorated
policy successor, the freshly stored literal table pair emits exactly the
existing guarded common cut advertised by `nextPairAt`.  This is the equation
consumed by the common-cut refresh: no semantic witness remains in its
statement. -/
theorem successorLiteralCross_bothPhysicalOutputs_eq_nextPairCut
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) :
    let extra := package.extraAt A strategy hwin
      (package.policy.successor state incoming)
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        leftReceiver blockInput.1 blockInput.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        rightReceiver blockInput.2 blockInput.1).1) =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  rcases package.exists_point_of_nextLiteralCrossInitial A strategy hwin
      hreachable incoming with ⟨point, _hcode, hmove, hextra⟩
  change
    let extra := package.nextExtraAt A strategy hwin state incoming
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
          leftReceiver blockInput.1 blockInput.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
          rightReceiver blockInput.2 blockInput.1).1) =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth)
  rw [← hextra, ← hmove]
  exact
    profiledRawJointGuardedCommonLiteralCrossOfPoint_bothPhysicalOutputs_eq_cut
      A strategy hwin point rightAnchor leftAnchor blockInput

/-- Consumption form for a refreshed right-phase mismatch shell.  On a
simultaneous receive, process one locally switches to the retained left table
with its fixed internal anchor and process two continues the installed right
table.  Their actual shell outputs are the successor common cut. -/
theorem currentRightLiteralCrossMismatchInitial_successor_bothOutput_eq_cut
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂) (anchor : Bool) :
    let initialState :=
      package.currentRightLiteralCrossMismatchInitial A strategy hwin
        (package.policy.successor state incoming) anchor
    let result :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
        initialState.1 initialState.2 blockInput .both
    (result.1.1, result.2.1) =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  change
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
          (package.nextExtraAt A strategy hwin state incoming).2 false)
        blockInput.1 blockInput.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
          (package.nextExtraAt A strategy hwin state incoming).1 anchor)
        blockInput.2 blockInput.1).1) = _
  exact package.successorLiteralCross_bothPhysicalOutputs_eq_nextPairCut
    A strategy hwin hreachable incoming blockInput anchor false

/-- Left-phase mirror. -/
theorem currentLeftLiteralCrossMismatchInitial_successor_bothOutput_eq_cut
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂) (anchor : Bool) :
    let initialState :=
      package.currentLeftLiteralCrossMismatchInitial A strategy hwin
        (package.policy.successor state incoming) anchor
    let result :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
        initialState.1 initialState.2 blockInput .both
    (result.1.1, result.2.1) =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  change
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
          (package.nextExtraAt A strategy hwin state incoming).2 anchor)
        blockInput.1 blockInput.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
          (package.nextExtraAt A strategy hwin state incoming).1 false)
        blockInput.2 blockInput.1).1) = _
  exact package.successorLiteralCross_bothPhysicalOutputs_eq_nextPairCut
    A strategy hwin hreachable incoming blockInput false anchor

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
