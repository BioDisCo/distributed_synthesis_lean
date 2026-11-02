/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveRootController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseSwitchActivation

/-!
# One-way activation of the checked recurrent kernel

The phase-live table is needed only until a locally certified left-to-right
switch.  At that switch the two endpoint-local maps of
`literalCombinedFreshRightPhaseSwitch_exact_pair` enter the two halves of one
checked tagged recurrent control.  Afterwards the already proved indexed
leader-free kernel handles every graph pattern.

This file packages that dispatch as one finite paired controller.  Pending
controls inspect only their stored phase bit and locally delivered finite
control.  Recurrent controls use only the tagged kernel maps.  Mixed branches
are totalized but are not produced by the exact switch pair.  No executable
map receives a graph, orientation, hierarchy side, leader bit, strict-leader
bit, history, or semantic view.
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

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev RightOne (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
    package

private abbrev RightTwo (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
    package

private abbrev OneShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package (RightOne A strategy hwin package)

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package (RightTwo A strategy hwin package)

/-! ## The locally checkable joint-activation guard -/

/-- Inspect the fresh entry row of the retained stage.  The surrounding
receiver keeps the old source row used by the table scan. -/
def literalCombinedFreshRightFreshStageReady
    (package : Package A strategy hwin (initial := initial))
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package) : Bool :=
  match receiver.2.2.2 with
  | some stage => stage.row == .first
  | none => false

/-- Process one may leave the pending table only when its stored phase says
that a left block just ran and its retained stage has the canonical fresh
`.first` entry row. -/
def literalCombinedFreshRightActivationReadyOne
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) : Bool :=
  let receiver := package.literalCombinedFreshOneReceiver A strategy hwin
    one.1 one.2.1
  one.2.1.1.2 &&
    package.literalCombinedFreshRightFreshStageReady A strategy hwin receiver

/-- Process two checks its own phase and the same stage in the delivered
process-one control.  Thus the two endpoints agree on honest selected states
without being told an orientation or a leader. -/
def literalCombinedFreshRightActivationReadyTwo
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package) : Bool :=
  let receiver := package.literalCombinedFreshOneReceiver A strategy hwin
    one.1 one.2.1
  two.2.1.1.2 &&
    package.literalCombinedFreshRightFreshStageReady A strategy hwin receiver

/-- Equal local phase tags make the two independently evaluated guards
literally equal, because both inspect the same receiver stage carried in the
delivered process-one control. -/
theorem literalCombinedFreshRightActivationReady_eq_of_phase_eq
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = two.2.1.1.2) :
    package.literalCombinedFreshRightActivationReadyOne A strategy hwin one =
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin two
        one := by
  simp only [literalCombinedFreshRightActivationReadyOne,
    literalCombinedFreshRightActivationReadyTwo, hphase]

/-- A stage-free receiver disables both guards even in the intentionally
asymmetric `true,false` phase used at the common/simultaneous root. -/
theorem literalCombinedFreshRightActivationReady_eq_false_of_no_stage
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstage :
      (package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1).2.2.2 = none) :
    package.literalCombinedFreshRightActivationReadyOne A strategy hwin one =
        false ∧
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin two
        one = false := by
  simp [literalCombinedFreshRightActivationReadyOne,
    literalCombinedFreshRightActivationReadyTwo,
    literalCombinedFreshRightFreshStageReady, hstage]

/-! ## Endpoint-local no-receive maps -/

/-- Process one activates the checked right kernel exactly when its stored
phase requests the already verified switch. -/
noncomputable def literalCombinedFreshPhaseActivatedNoRecvOne
    (package : Package A strategy hwin (initial := initial)) :
    OneControl A strategy hwin package → In₁ →
      OneControl A strategy hwin package × Out₁
  | .inl pending, input =>
      if package.literalCombinedFreshRightActivationReadyOne A strategy hwin
          pending then
        package.literalCombinedFreshRightSwitchNoRecvOne A strategy hwin
          pending input
      else
        let next := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (package.literalCombinedFreshOnePendingStep A strategy hwin) pending
            input
        (.inl next.1, next.2)
  | .inr recurrent, input =>
      let next := package.literalRightSeamTaggedNoRecvOne A strategy hwin
        recurrent input
      (.inr next.1, next.2)

/-- Process two has no pending activation on a no-receive event; after
activation it uses the recurrent kernel. -/
noncomputable def literalCombinedFreshPhaseActivatedNoRecvTwo
    (package : Package A strategy hwin (initial := initial)) :
    TwoControl A strategy hwin package → In₂ →
      TwoControl A strategy hwin package × Out₂
  | .inl pending, input =>
      let next := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalCombinedFreshTwoPendingStep A strategy hwin) pending
          input
      (.inl next.1, next.2)
  | .inr recurrent, input =>
      let next := package.literalRightSeamTaggedNoRecvTwo A strategy hwin
        recurrent input
      (.inr next.1, next.2)

/-! ## Endpoint-local open receives -/

/-- Before activation, process one's ordinary receive is the corrected
phase-live receive.  Recurrent pairs dispatch to the tagged kernel. -/
noncomputable def literalCombinedFreshPhaseActivatedOpenRecvOne
    (package : Package A strategy hwin (initial := initial)) :
    OneControl A strategy hwin package → In₁ →
      TwoControl A strategy hwin package → In₂ →
        OneControl A strategy hwin package × Out₁
  | .inl one, own, .inl two, delivered =>
      let next := package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
        one own two delivered
      (.inl next.1.openControl, next.2)
  | .inr one, own, .inr two, delivered =>
      let next := package.literalRightSeamTaggedRecvOne A strategy hwin one own
        two delivered
      (.inr next.1, next.2)
  | .inl one, _, .inr _, _ => (.inl one, default)
  | .inr one, _, .inl _, _ => (.inr one, default)

/-- On a pending strict-right receive, process two uses its own stored phase.
The switching branch enters the exact recurrent half; the same-direction
branch keeps the corrected live table. -/
noncomputable def literalCombinedFreshPhaseActivatedOpenRecvTwo
    (package : Package A strategy hwin (initial := initial)) :
    TwoControl A strategy hwin package → In₂ →
      OneControl A strategy hwin package → In₁ →
        TwoControl A strategy hwin package × Out₂
  | .inl two, own, .inl one, delivered =>
      if package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
          two one then
        package.literalCombinedFreshRightSwitchRecvTwo A strategy hwin two own
          one delivered
      else
        let next := package.literalCombinedFreshPhaseLiveRecvTwo A strategy
          hwin two own one delivered
        (.inl next.1.openControl, next.2)
  | .inr two, own, .inr one, delivered =>
      let next := package.literalRightSeamTaggedRecvTwo A strategy hwin two own
        one delivered
      (.inr next.1, next.2)
  | .inl two, _, .inr _, _ => (.inl two, default)
  | .inr two, _, .inl _, _ => (.inr two, default)

/-! ## One exact simultaneous close -/

/-- Pending simultaneous rounds retain the corrected exact-close behavior.
Once recurrent, both endpoint controls advance through the same tagged-kernel
round.  Mixed cases are unreachable totalizations. -/
noncomputable def literalCombinedFreshPhaseActivatedClose
    (package : Package A strategy hwin (initial := initial)) :
    OneControl A strategy hwin package → In₁ →
      TwoControl A strategy hwin package → In₂ →
        OneControl A strategy hwin package ×
          TwoControl A strategy hwin package
  | .inl one, own, .inl two, delivered =>
      let nextOne := package.literalCombinedFreshPhaseLiveRecvOne A strategy
        hwin one own two delivered
      let nextTwo := package.literalCombinedFreshPhaseLiveRecvTwo A strategy
        hwin two delivered one own
      (.inl nextOne.1.closedControl, .inl nextTwo.1.closedControl)
  | .inr one, own, .inr two, delivered =>
      let nextOne := package.literalRightSeamTaggedRecvOne A strategy hwin one
        own two delivered
      let nextTwo := package.literalRightSeamTaggedRecvTwo A strategy hwin two
        delivered one own
      (.inr nextOne.1, .inr nextTwo.1)
  | .inl one, _, .inr two, _ => (.inl one, .inr two)
  | .inr one, _, .inl two, _ => (.inr one, .inl two)

/-! ## The finite controller -/

/-- Stay in the finite phase-live table until one certified switch, then stay
forever in the finite indexed leader-free recurrent kernel. -/
noncomputable def literalCombinedFreshPhaseActivatedController
    (package : Package A strategy hwin (initial := initial)) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin) :
      OneControl A strategy hwin package)
    (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) :
      TwoControl A strategy hwin package)
    (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)

/-- Moore presentation of the activated controller used by the physical
trace and readback layers.  Mooreization only stores each endpoint's last
locally emitted output; it adds no observation or regime test. -/
noncomputable def literalCombinedFreshPhaseActivatedPhysicalController
    (package : Package A strategy hwin (initial := initial)) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (package.literalCombinedFreshPhaseActivatedController A strategy hwin
    ).mooreize

/-! ## The checked activation pair survives controller assembly -/

@[simp] theorem literalCombinedFreshPhaseActivatedNoRecvOne_pending
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (input : In₁)
    (hready : package.literalCombinedFreshRightActivationReadyOne A strategy
      hwin one = true) :
    package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin
        (.inl one) input =
      package.literalCombinedFreshRightSwitchNoRecvOne A strategy hwin one
        input := by
  simp [literalCombinedFreshPhaseActivatedNoRecvOne, hready]

@[simp] theorem literalCombinedFreshPhaseActivatedOpenRecvTwo_pending_true
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁)
    (hready : package.literalCombinedFreshRightActivationReadyTwo A strategy
      hwin two one = true) :
    package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
        (.inl two) own (.inl one) delivered =
      package.literalCombinedFreshRightSwitchRecvTwo A strategy hwin two own
        one delivered := by
  simp [literalCombinedFreshPhaseActivatedOpenRecvTwo, hready]

theorem literalCombinedFreshRightActivationReady_of_live_pair
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (stage :
      ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
        package)
    (hstage :
      (package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1).2.2.2 = some stage)
    (hrow : stage.row = .first)
    (hphaseOne : one.2.1.1.2 = true)
    (hphaseTwo : two.2.1.1.2 = true) :
    package.literalCombinedFreshRightActivationReadyOne A strategy hwin one =
        true ∧
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin two
        one = true := by
  simp [literalCombinedFreshRightActivationReadyOne,
    literalCombinedFreshRightActivationReadyTwo,
    literalCombinedFreshRightFreshStageReady, hstage, hrow, hphaseOne,
    hphaseTwo]

/-- The common root cannot activate unilaterally: process one's phase is
`true`, but its retained receiver has no live stage; process two's phase is
`false`. -/
@[simp] theorem literalCombinedFreshRightActivationReady_initial
    (package : Package A strategy hwin (initial := initial)) :
    package.literalCombinedFreshRightActivationReadyOne A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin) =
        false ∧
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin) =
        false := by
  constructor <;> rfl

/-- A simultaneous close likewise installs stage-free fresh roots, so the
following strict event cannot trigger a one-sided switch merely from the
ambiguous local phase bit. -/
theorem literalCombinedFreshRightActivationReady_after_both
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (input : In₁ × In₂) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.closedControl
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.closedControl
    package.literalCombinedFreshRightActivationReadyOne A strategy hwin
        oneNext = false ∧
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
        twoNext oneNext = false := by
  constructor <;> rfl

/-- The first honest strict-left record from the common root installs the
exact false-branch live stage. -/
theorem literalCombinedFreshRightStage_after_initial_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    let one := package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
    let two := package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.openControl
    (package.literalCombinedFreshOneReceiver A strategy hwin oneNext.1
      oneNext.2.1).2.2.2 =
      some (package.literalRightSeamExactStageAt A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
        .both .first [] input) := by
  dsimp only
  change
    (package.literalCombinedFreshOneReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
        input.1
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
        input.2).1.openControl.2.1).2.2.2 = _
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A strategy
    hwin _ _ (by rfl)]
  change
    (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
        .both false) input.1 input.2).2.2.2.2 = _
  exact package.literalRightSeamBranchRestartedReceiverFirst_false_stage A
    strategy hwin _ .both input

/-- Consequently a strict-right record immediately after that first
strict-left record is jointly ready at both endpoints. -/
theorem literalCombinedFreshRightActivationReady_after_initial_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    let one := package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
    let two := package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.openControl
    let twoNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
          input.2).1
    package.literalCombinedFreshRightActivationReadyOne A strategy hwin
        oneNext = true ∧
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
        twoNext oneNext = true := by
  dsimp only
  let stage := package.literalRightSeamExactStageAt A strategy hwin
    (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
    .both .first [] input
  apply package.literalCombinedFreshRightActivationReady_of_live_pair A
    strategy hwin _ _ stage
  · exact package.literalCombinedFreshRightStage_after_initial_strictLeft A
      strategy hwin input
  · rfl
  · rfl
  · rfl

/-- The controller-level strict-right switch is exactly one recurrent-kernel
step from the same matched pair at both endpoints. -/
theorem literalCombinedFreshPhaseActivated_switch_exact_pair
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (stage :
      ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
        package)
    (hstage :
      (package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1).2.2.2 = some stage)
    (hrow : stage.row = .first)
    (hphaseOne : one.2.1.1.2 = true)
    (hphaseTwo : two.2.1.1.2 = true)
    (input : In₁ × In₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin
        (.inl one) input.1 =
        (.inr
            (package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
              input.1).1,
          (package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
            input.1).2) ∧
      package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
          (.inl two) input.2 (.inl one) input.1 =
        (.inr
            (package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
              input.2 matched.1 input.1).1,
          (package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
            input.2 matched.1 input.1).2) := by
  dsimp only
  have hready := package.literalCombinedFreshRightActivationReady_of_live_pair
    A strategy hwin one two stage hstage hrow hphaseOne hphaseTwo
  rw [package.literalCombinedFreshPhaseActivatedNoRecvOne_pending A strategy
    hwin one input.1 hready.1]
  rw [package.literalCombinedFreshPhaseActivatedOpenRecvTwo_pending_true A
    strategy hwin two input.2 one input.1 hready.2]
  simpa [literalCombinedFreshPhaseNoRecvOne, hphaseOne,
      literalCombinedFreshPhaseOpenRecvTwo, hphaseTwo] using
    (package.literalCombinedFreshRightPhaseSwitch_exact_pair A strategy hwin
      one two stage hstage hphaseOne hphaseTwo input)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
