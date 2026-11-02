/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRetainedCarrierTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTargetHandoff

/-!
# Mixed strict/simultaneous closure of the retained literal carrier

The retained carrier does not reinstall two fresh `.both` receivers at a
simultaneous event.  Each endpoint uses the row selected by its own preceding
local receive bit.  Thus a simultaneous event after a strict-right event uses
the row pair `(left .first, right .both)`; after a strict-left event it uses
`(left .both, right .first)`.  This is exactly what local
indistinguishability requires.

This file packages the three graph cases around the authoritative common
relay.  The simultaneous field is deliberately only the exact row-parametric
output equation plus post-round synchronization.  It does not assert an
anti-mosaic equation for two arbitrary independently rationalized tables;
that semantic equation belongs to a same-occurrence marked packet.
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

private abbrev Relay :=
  ProfiledRawJointHybridLiteralPrefixRetainedRelay A

private abbrev OneControl :=
  ProfiledRawJointHybridLiteralPrefixRetainedOneControl A

private abbrev TwoControl :=
  ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A

/-! ## The exact simultaneous continuation packet -/

/-- Everything supplied by one simultaneous event from an authoritative
retained state.  `output_eq` is the exact cross-table output at the two
endpoint-local rows.  The remaining fields say that the event synchronizes
the finite relay and makes both subsequent receive rows `.both`.

No equality between the right and left table records is included: such an
equality is valid only with same-occurrence provenance. -/
structure ProfiledRawJointHybridLiteralPrefixRetainedBothContinuationAt
    (expected : Relay A) (state : OneControl A × TwoControl A)
    (input : In₁ × In₂) where
  output_eq :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input
    (next.1.1, next.2.1) =
      (pairedLeftInformedForRow
          (if state.1.2.1 then .both else .first)
          (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
            expected.2.2 input.1 input.2).1.physical,
        pairedRightInformedForRow
          (if state.2.2.1 then .both else .first)
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
            expected.1.2 input.2 input.1).1.physical)
  next_one_row :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input
    (if next.1.2.1 then PairedEntryRow.both else PairedEntryRow.first) =
      PairedEntryRow.both
  next_two_row :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input
    (if next.2.2.1 then PairedEntryRow.both else PairedEntryRow.first) =
      PairedEntryRow.both
  next_one_relay :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input
    next.1.2.2 =
      profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected input
  next_two_relay :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input
    next.2.2.2 =
      profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected input
  next_authority :
    ProfiledRawJointHybridLiteralPrefixRetainedAuthority A
      (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected input)
      (profiledRawJointHybridLiteralPrefixRetainedBothStep A state input)

/-- The authority invariant discharges the complete simultaneous
continuation packet. -/
noncomputable def
    profiledRawJointHybridLiteralPrefixRetainedBothContinuationAt_of_authority
    (expected : Relay A) (state : OneControl A × TwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedBothContinuationAt A expected
      state input := by
  have houtput :=
    profiledRawJointHybridLiteralPrefixRetainedBoth_authority_output A expected
      state hauthority input
  have hsync :=
    profiledRawJointHybridLiteralPrefixRetainedBoth_synchronizes A expected
      state hauthority input
  refine {
    output_eq := houtput
    next_one_row := ?_
    next_two_row := ?_
    next_one_relay := hsync.2.2.1
    next_two_relay := hsync.2.2.2
    next_authority :=
      profiledRawJointHybridLiteralPrefixRetainedAuthority_step A expected
        state hauthority .both input }
  · dsimp only
    rw [hsync.1]
    rfl
  · dsimp only
    rw [hsync.2.1]
    rfl

/-! ## One reusable three-constructor closure -/

/-- The exact operational closure required by a mixed retained trace.  The
strict fields use the existing one-table output equations.  The simultaneous
field retains both endpoint-local rows and the synchronization facts instead
of pretending that two fresh `.both` tables were installed. -/
structure ProfiledRawJointHybridLiteralPrefixRetainedMixedConstructorClosure
    (expected : Relay A) (state : OneControl A × TwoControl A) where
  authority :
    ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state
  strictRight : ∀ input : In₁ × In₂,
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A state input
    (next.1.1, next.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedRightOutput A
        (if state.2.2.1 then .both else .first) expected input
  strictLeft : ∀ input : In₁ × In₂,
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A state input
    (next.1.1, next.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedLeftOutput A
        (if state.1.2.1 then .both else .first) expected input
  both : ∀ input : In₁ × In₂,
    ProfiledRawJointHybridLiteralPrefixRetainedBothContinuationAt A expected
      state input

/-- Authority is the only premise of the operational mixed closure. -/
noncomputable def
    profiledRawJointHybridLiteralPrefixRetainedMixedConstructorClosure_of_authority
    (expected : Relay A) (state : OneControl A × TwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state) :
    ProfiledRawJointHybridLiteralPrefixRetainedMixedConstructorClosure A
      expected state where
  authority := hauthority
  strictRight := fun input ↦
    profiledRawJointHybridLiteralPrefixRetainedStrictRight_authority_output A
      expected state hauthority input
  strictLeft := fun input ↦
    profiledRawJointHybridLiteralPrefixRetainedStrictLeft_authority_output A
      expected state hauthority input
  both := fun input ↦
    profiledRawJointHybridLiteralPrefixRetainedBothContinuationAt_of_authority
      A expected state hauthority input

/-! ## Fail-fast row timing after a strict event -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- A simultaneous event immediately after strict-right reads the fresh left
row and the continued right row.  This is a definitional local calculation,
not a semantic compatibility assumption. -/
theorem profiledRawJointHybridLiteralPrefixRetained_strictRight_both_rows
    (state : OneControl A × TwoControl A) (first second : In₁ × In₂) :
    let afterRight :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A state first
    let afterBoth :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A afterRight second
    (if afterRight.1.2.1 then .both else .first,
        if afterRight.2.2.1 then .both else .first) =
      (PairedEntryRow.first, PairedEntryRow.both) ∧
    afterBoth.1.2.1 = true ∧ afterBoth.2.2.1 = true := by
  simp [profiledRawJointHybridLiteralPrefixRetainedStrictRightStep,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvOne,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo,
    profiledRawJointHybridLiteralPrefixRetainedBothStep,
    profiledRawJointHybridLiteralPrefixRetainedRecvOne]

/-- Strict-left mirror. -/
theorem profiledRawJointHybridLiteralPrefixRetained_strictLeft_both_rows
    (state : OneControl A × TwoControl A) (first second : In₁ × In₂) :
    let afterLeft :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A state first
    let afterBoth :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A afterLeft second
    (if afterLeft.1.2.1 then .both else .first,
        if afterLeft.2.2.1 then .both else .first) =
      (PairedEntryRow.both, PairedEntryRow.first) ∧
    afterBoth.1.2.1 = true ∧ afterBoth.2.2.1 = true := by
  simp [profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo,
    profiledRawJointHybridLiteralPrefixRetainedRecvOne,
    profiledRawJointHybridLiteralPrefixRetainedBothStep,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo]

/-- Exact mixed output after `strict-right; both`.  The two controls are
advanced from the relay selected by the authority invariant; no endpoint is
told which of the two global events occurred. -/
theorem
    profiledRawJointHybridLiteralPrefixRetained_strictRight_both_output_of_authority
    (expected : Relay A) (state : OneControl A × TwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (first second : In₁ × In₂) :
    let afterRight :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A state first
    let advanced :=
      profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected first
    let afterBoth :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A afterRight second
    (afterBoth.1.1, afterBoth.2.1) =
      (pairedLeftInformedForRow .first
          (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
            advanced.2.2 second.1 second.2).1.physical,
        pairedRightInformedForRow .both
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
            advanced.1.2 second.2 second.1).1.physical) := by
  dsimp only
  have hnext :=
    profiledRawJointHybridLiteralPrefixRetainedAuthority_step A expected state
      hauthority .right first
  have houtput :=
    profiledRawJointHybridLiteralPrefixRetainedBoth_authority_output A _ _
      hnext second
  simpa [profiledRawJointHybridLiteralPrefixRetainedStrictRightStep,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvOne,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo] using houtput

/-- Exact mixed output after `strict-left; both`. -/
theorem
    profiledRawJointHybridLiteralPrefixRetained_strictLeft_both_output_of_authority
    (expected : Relay A) (state : OneControl A × TwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (first second : In₁ × In₂) :
    let afterLeft :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A state first
    let advanced :=
      profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected first
    let afterBoth :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A afterLeft second
    (afterBoth.1.1, afterBoth.2.1) =
      (pairedLeftInformedForRow .both
          (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
            advanced.2.2 second.1 second.2).1.physical,
        pairedRightInformedForRow .first
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
            advanced.1.2 second.2 second.1).1.physical) := by
  dsimp only
  have hnext :=
    profiledRawJointHybridLiteralPrefixRetainedAuthority_step A expected state
      hauthority .left first
  have houtput :=
    profiledRawJointHybridLiteralPrefixRetainedBoth_authority_output A _ _
      hnext second
  simpa [profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo,
    profiledRawJointHybridLiteralPrefixRetainedRecvOne] using houtput

end

/-! ## Same-occurrence public target merge

The two bare target codes below are intentionally not equated: a right close
carries the new left marginal and a left close carries the new right
marginal.  Their ordered merge is the public code shared by the common-child
selector after a genuine simultaneous event. -/

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

/-- The public `.both` target in the retained right table is the exact
one-sided right-close child of the occurrence from which that table was
extracted. -/
theorem profiledRawJointGuardedCommonRightLiteralCrossOfPoint_bothTarget
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiver
        input.2 input.1).1.target .both =
      profiledRawJointOneSidedNext A
        (profiledRawJointGuardedCommonPointInstalled A strategy point
          ).incidenceCode
        (profiledRawJointGuardedCommonPointInstalled A strategy point).rawMove
        (profiledRawJointCommonOneRoundStrictRight input) := by
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
  change firstRecord.2.1.target .both = _
  rw [hrecord]
  change
    ((profiledRawJointGuardedFirstRightReceiverStrategy A
      (profiledRawJointHybridExactRightActivation A hwin installed) []
      (input.2, input.1)).target .both).1 = _
  exact profiledRawJointHybridExactRightActivation_strictChild A installed
    (profiledRawJointHybridExactRightPolicy A hwin installed)
    (profiledRawJointHybridExactRightActivation A hwin installed) input

/-- Left-target mirror. -/
theorem profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_bothTarget
    (point : CommonPoint A strategy) (anchor : Bool)
    (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy hwin
        point
    let receiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiver
        input.1 input.2).1.target .both =
      profiledRawJointOneSidedNext A
        (profiledRawJointGuardedCommonPointInstalled A strategy point
          ).incidenceCode
        (profiledRawJointGuardedCommonPointInstalled A strategy point).rawMove
        (profiledRawJointCommonOneRoundStrictLeft input) := by
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
  change firstRecord.2.1.target .both = _
  rw [hrecord]
  change
    ((profiledRawJointGuardedFirstLeftReceiverStrategy A
      (profiledRawJointHybridExactLeftActivation A hwin installed) []
      input).target .both).1 = _
  exact profiledRawJointHybridExactLeftActivation_strictChild A installed
    (profiledRawJointHybridExactLeftPolicy A hwin installed)
    (profiledRawJointHybridExactLeftActivation A hwin installed) input

/-- The selector-facing public theorem.  Two one-sided targets from the same
marked occurrence and complete input reconstruct one exact common-child code.
This ordered merge, rather than equality of the two marginals, is what both
endpoints may feed to the same deterministic common-successor selector. -/
theorem profiledRawJointGuardedCommonLiteralCrossOfPoint_bothTargets_merge
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
    profiledRawJointBothTargetMerge A input
        ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
          rightReceiver input.2 input.1).1.target .both)
        ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
          leftReceiver input.1 input.2).1.target .both) =
      (profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A (point.world A strategy) input)
        ).incidenceCode A := by
  dsimp only
  simp only [profiledRawJointGuardedCommonLiteralCrossExtraOfPoint]
  rw [profiledRawJointGuardedCommonRightLiteralCrossOfPoint_bothTarget A
      strategy hwin point rightAnchor input,
    profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_bothTarget A strategy
      hwin point leftAnchor input]
  simpa [profiledRawJointGuardedCommonPointInstalled,
    profiledRawJointCommonOneRoundStrictRight,
    profiledRawJointCommonOneRoundStrictLeft] using
    (profiledRawJointBothTargetMerge_eq_commonWorldAfterBoth A
      (point.world A strategy) input)

end

end DetParityAutomaton

end DistributedSynthesis
