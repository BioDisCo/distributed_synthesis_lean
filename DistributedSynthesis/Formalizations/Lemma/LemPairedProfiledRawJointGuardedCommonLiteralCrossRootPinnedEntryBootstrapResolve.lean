/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBootstrapReceive

/-!
# The first resolving records of the root-pinned entry bootstrap

The entry bootstrap consumes the entry input in both retained literal-cross
tables before exposing its two hidden members.  The first-two guards of those
tables therefore have one remaining occurrence-sensitive consequence: the
next synchronized local round is exactly the second literal record extracted
at the represented predecessor occurrence.

The two record equations below retain the complete receiver certificate, not
only its physical output.  In particular, the `.both` target needed by the
subsequent common close remains available.  Their endpoint-facing corollaries
state the exact strict-right and strict-left output pairs produced by the
bootstrap.  No executable transition receives a graph, orientation, leader
bit, semantic history, or proof of alignment.
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

private noncomputable abbrev RightBaseMonitor
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A) :=
  profiledRawJointRightPhysicalSiblingMonitor A descriptor false

private noncomputable abbrev RightMonitor :=
  finiteCrossAnchorLiteralPrefixMonitor (RightBaseMonitor A)

private abbrev RightFirstAllowed :=
  finiteCrossAnchorLiteralPrefixFirstAllowed (RightBaseMonitor A)

private abbrev RightSecondAllowed :=
  finiteCrossAnchorLiteralPrefixSecondAllowed (RightBaseMonitor A)

private noncomputable abbrev RightGuard
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily
    (fun member => RightMonitor A (move.1.descriptor member)) move.1.start
    (RightFirstAllowed A move.1) (RightSecondAllowed A move.1) anchor

private noncomputable abbrev LeftBaseMonitor
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A) :=
  profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor

private noncomputable abbrev LeftMonitor :=
  finiteCrossAnchorLiteralPrefixMonitor (LeftBaseMonitor A)

private abbrev LeftFirstAllowed :=
  finiteCrossAnchorLiteralPrefixFirstAllowed (LeftBaseMonitor A)

private abbrev LeftSecondAllowed :=
  finiteCrossAnchorLiteralPrefixSecondAllowed (LeftBaseMonitor A)

private noncomputable abbrev LeftGuard
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily
    (fun member => LeftMonitor A (move.1.descriptor member)) move.1.start
    (LeftFirstAllowed A move.1) (LeftSecondAllowed A move.1) anchor

/-! ## Complete second-record equations -/

/-- The second right-oriented table round is the literal second receiver and
sender record of the occurrence from which the table was extracted. -/
theorem profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondRecord
    (point : CommonPoint A strategy) (anchor : Bool)
    (first second : In₂ × In₁) :
    let move :=
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy
        hwin point
    let senderRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    let senderAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A senderRoot
        first.2).2
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverRoot first.1 first.2).2
    (second,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
        senderAfterFirst second.2).1) =
      (second,
        profiledRawJointTargetRightReceiverStrategy A
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point))
          [first] second,
        pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point)
            ).lambda
          [first.2] second.2) := by
  classical
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let baseMonitor :=
    profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
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
    guard.initial first
  let secondRecord := narrowedRecord guard
    (controller.labeledTree [first.2])
    (guard.step guard.initial firstRecord) second
  have hallowed :=
    move.memberController_records_allowed monitor anchor first second
  have hsecond : finiteCrossAnchorLiteralSecondAllowed
      (profiledRawJointTargetRightReceiverStrategy A activation)
      (pairedRightSenderStrategy activation.lambda) firstRecord secondRecord =
        true := by
    simpa [move, guard, controller, firstRecord, secondRecord, monitor,
      firstAllowed, secondAllowed, monitorFamily,
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint,
      finiteCrossAnchorLiteralPrefixMove, descriptor, baseMonitor, activation,
      installed] using hallowed.2
  have hrecord : secondRecord =
      (second,
        profiledRawJointTargetRightReceiverStrategy A activation [first]
          second,
        pairedRightSenderStrategy activation.lambda [first.2] second.2) := by
    simpa [finiteCrossAnchorLiteralSecondAllowed, firstRecord] using
      (of_decide_eq_true hsecond)
  change secondRecord = _
  exact hrecord

/-- Left-oriented mirror of the complete second-record equation. -/
theorem profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondRecord
    (point : CommonPoint A strategy) (anchor : Bool)
    (first second : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy hwin
        point
    let senderRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor
    let senderAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A senderRoot
        first.2).2
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).2
    (second,
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1,
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
        senderAfterFirst second.2).1) =
      (second,
        profiledRawJointTargetLeftReceiverStrategy A
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point))
          [first] second,
        pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point)
            ).lambda
          [first.2] second.2) := by
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
    guard.initial first
  let secondRecord := narrowedRecord guard
    (controller.labeledTree [first.2])
    (guard.step guard.initial firstRecord) second
  have hallowed :=
    move.memberController_records_allowed monitor anchor first second
  have hsecond : finiteCrossAnchorLiteralSecondAllowed
      (profiledRawJointTargetLeftReceiverStrategy A activation)
      (pairedLeftSenderStrategy activation.lambda) firstRecord secondRecord =
        true := by
    simpa [move, guard, controller, firstRecord, secondRecord, monitor,
      firstAllowed, secondAllowed, monitorFamily,
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint,
      finiteCrossAnchorLiteralPrefixMove, descriptor, baseMonitor,
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor, activation,
      installed] using hallowed.2
  have hrecord : secondRecord =
      (second,
        profiledRawJointTargetLeftReceiverStrategy A activation [first]
          second,
        pairedLeftSenderStrategy activation.lambda [first.2] second.2) := by
    simpa [finiteCrossAnchorLiteralSecondAllowed, firstRecord] using
      (of_decide_eq_true hsecond)
  change secondRecord = _
  exact hrecord

/-! ## Endpoint-facing resolving equations -/

/-- The selected right receiver exposes the exact `.both` target of the
second literal record.  This is the finite target consumed by a simultaneous
close after the entry round. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictRight_target
    (point : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin point entry member
    ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
      (two.2.2.candidate two.1) input.2 input.1).1.target .both) =
      (profiledRawJointHybridExactRightUniformActivation A strategy hwin
        (profiledRawJointGuardedCommonPointInstalled A strategy point)).target
          .both [(entry.2, entry.1)] (input.2, input.1) := by
  have hrecord :=
    profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondRecord A
      strategy hwin point member (entry.2, entry.1) (input.2, input.1)
  have htarget := congrArg (fun record ↦ record.2.1.target .both) hrecord
  cases member <;>
    simpa [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra,
      profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical,
      profiledRawJointTargetRightReceiverResultPhysicalOutput] using htarget

/-- Left-oriented mirror of the exact resolving target. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictLeft_target
    (point : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin point entry member
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
      (one.2.2.candidate one.1) input.1 input.2).1.target .both) =
      (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
        (profiledRawJointGuardedCommonPointInstalled A strategy point)).target
          .both [entry] input := by
  have hrecord :=
    profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondRecord A
      strategy hwin point member entry input
  have htarget := congrArg (fun record ↦ record.2.1.target .both) hrecord
  cases member <;>
    simpa [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra,
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical,
      profiledRawJointTargetLeftReceiverResultPhysicalOutput] using htarget

/-- Starting from either hidden bootstrap member, the first strict-right
round emits exactly the physical projection of the right table's second
literal record.  The member bit does not occur on the right-hand side. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictRight_outputs
    (point : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin point entry member
    let two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin point entry member
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A one
        input.1).2,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo A
        two input.2 one input.1).2) =
      (pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point)
            ).lambda
          [entry.1] input.1,
        profiledRawJointTargetRightReceiverBothPhysicalOutput
          (profiledRawJointTargetRightReceiverStrategy A
            (profiledRawJointHybridExactRightUniformActivation A strategy
              hwin
              (profiledRawJointGuardedCommonPointInstalled A strategy point))
            [(entry.2, entry.1)] (input.2, input.1))) := by
  have hrecord :=
    profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondRecord A
      strategy hwin point member (entry.2, entry.1) (input.2, input.1)
  have hphysical := congrArg
    (fun record ↦
      (record.2.2,
        profiledRawJointTargetRightReceiverBothPhysicalOutput record.2.1))
    hrecord
  cases member <;>
    simpa [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate,
      profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical,
      profiledRawJointTargetRightReceiverResultPhysicalOutput] using hphysical

/-- Strict-left mirror of the resolving physical-output equation. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictLeft_outputs
    (point : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin point entry member
    let two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin point entry member
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne A one
        input.1 two input.2).2,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A two
        input.2).2) =
      (profiledRawJointTargetLeftReceiverBothPhysicalOutput
          (profiledRawJointTargetLeftReceiverStrategy A
            (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
              (profiledRawJointGuardedCommonPointInstalled A strategy point))
            [entry] input),
        pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointGuardedCommonPointInstalled A strategy point)
            ).lambda
          [entry.2] input.2) := by
  have hrecord :=
    profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondRecord A
      strategy hwin point member entry input
  have hphysical := congrArg
    (fun record ↦
      (profiledRawJointTargetLeftReceiverBothPhysicalOutput record.2.1,
        record.2.2)) hrecord
  cases member <;>
    simpa [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate,
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical,
      profiledRawJointTargetLeftReceiverResultPhysicalOutput] using hphysical

end

end DetParityAutomaton

end DistributedSynthesis
