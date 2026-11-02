/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveBothClose
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyInitial

/-!
# Structural selected invariant for the corrected phase-live pair

This is the proof-side `Selected` core consumed by the eventual
`ExactClosingSelectedTraceLaws`.  It contains exactly the information needed
by the local phase dispatch:

* the two leader-free freshness copies are aligned and their current policy
  state is reachable;
* in phase `false,false`, the left table is live and process two's dormant
  right sender is a root;
* in phase `true,true`, the right table is live and process one's dormant left
  sender is a root;
* in phase `true,false`, both tables are synchronized (the simultaneous/root
  phase);
* phase `false,true` is impossible.

The predicate is proof-only.  No executable transition receives it, a graph,
an orientation, or a leader bit.
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

/-- The phase-dependent table part of the selected invariant. -/
def LiteralCombinedFreshPhaseLiveTableInvariant
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  match one.2.1.1.2, two.2.1.1.2 with
  | false, false =>
      package.LiteralLeftSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
            two.2.1)
          one.2.1.2.1 ∧
        two.2.1.2.1 =
          package.literalRightSeamStagedSenderInitial A strategy hwin
            two.2.1.2.1.1
  | true, true =>
      package.LiteralRightSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshOneReceiver A strategy hwin one.1
            one.2.1)
          two.2.1.2.1 ∧
        one.2.1.2.1 =
          package.literalLeftSeamStagedSenderInitial A strategy hwin
            one.2.1.2.1.1
  | true, false =>
      package.LiteralRightSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshOneReceiver A strategy hwin one.1
            one.2.1)
          two.2.1.2.1 ∧
        package.LiteralLeftSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
            two.2.1)
          one.2.1.2.1
  | false, true => False

/-- Smallest structural selected predicate for a pending phase-live pair. -/
def LiteralCombinedFreshPhaseLiveStructuralSelected
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  DecoratedFreshnessAligned A strategy hwin one.2.1.1 two.2.1.1 ∧
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
      initial (CrossValid A strategy hwin) package.policy
        (decoratedFreshnessCurrent A strategy hwin one.2.1.1 two.2.1.1) ∧
    package.LiteralCombinedFreshPhaseLiveTableInvariant A strategy hwin one two

/-! ## Root and simultaneous preservation -/

/-- The common finite root satisfies the structural selected predicate.  The
old `PendingOnly` name belongs only to this reusable root datum; no retired
reset-on-receive controller is used here. -/
theorem literalCombinedFreshPhaseLiveStructuralSelected_initial
    (package : Package A strategy hwin (initial := initial)) :
    package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) := by
  refine ⟨package.literalCombinedFreshPendingOnlyInitial_aligned A strategy
    hwin, ?_, ?_⟩
  · simpa [literalCombinedFreshPendingOnlyInitialOne,
      literalCombinedFreshPendingOnlyInitialTwo,
      literalCombinedFreshPendingOnlyInitialOneShared,
      literalCombinedFreshPendingOnlyInitialTwoShared,
      literalCrossCombinedFreshOneSharedAt,
      literalCrossCombinedFreshTwoSharedAt,
      decoratedFreshnessBothInitial, decoratedFreshnessCurrent] using
        (package.initial_reachable A strategy hwin)
  · change
      package.LiteralRightSeamStagedControlsAligned A strategy hwin
          (package.literalRightSeamStagedReceiverInitial A strategy hwin
            (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
            .first false)
          (package.literalRightSeamStagedSenderInitial A strategy hwin
            (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)) ∧
        package.LiteralLeftSeamStagedControlsAligned A strategy hwin
          (package.literalLeftSeamStagedReceiverInitial A strategy hwin
            (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
            .first false)
          (package.literalLeftSeamStagedSenderInitial A strategy hwin
            (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin))
    exact ⟨
      package.literalRightSeamStagedControls_initial_aligned A strategy hwin
        _ .first false,
      package.literalLeftSeamStagedControls_initial_aligned A strategy hwin
        _ .first false⟩

/-- A simultaneous physical round sends both endpoints to the fresh
`true,false` phase, preserves current-policy reachability, and synchronizes
both exact-close tables. -/
theorem literalCombinedFreshPhaseLiveStructuralSelected_both
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (input : In₁ × In₂) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.closedControl
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.closedControl
    package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
      oneNext twoNext := by
  dsimp only
  rcases hselected with ⟨hfresh, hreachable, _htables⟩
  refine ⟨?_, ?_, ?_⟩
  · change DecoratedFreshnessAligned A strategy hwin
      (decoratedFreshnessRecvOne A strategy hwin package one.2.1.1 input.1
        two.2.1.1 input.2)
      (decoratedFreshnessRecvTwo A strategy hwin package two.2.1.1 input.2
        one.2.1.1 input.1)
    exact decoratedFreshnessLocalStep_aligned A strategy hwin package
      one.2.1.1 two.2.1.1 hfresh input .both
  · change ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy
      hwin initial (CrossValid A strategy hwin) package.policy
        (decoratedFreshnessCurrent A strategy hwin
          (decoratedFreshnessRecvOne A strategy hwin package one.2.1.1 input.1
            two.2.1.1 input.2)
          (decoratedFreshnessRecvTwo A strategy hwin package two.2.1.1 input.2
            one.2.1.1 input.1))
    exact decoratedFreshnessLocalStep_current_reachable A strategy hwin
      package one.2.1.1 two.2.1.1 hfresh hreachable input .both
  · change
      package.LiteralRightSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshOneReceiver A strategy hwin true
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
              input.1 two input.2).1.closedControl.2.1)
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            input.2 one input.1).1.closedControl.2.1.2.1 ∧
        package.LiteralLeftSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshTwoReceiver A strategy hwin true
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
              input.2 one input.1).1.closedControl.2.1)
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
            input.1 two input.2).1.closedControl.2.1.2.1
    have hright :=
      package.literalCombinedFreshPhaseLiveBoth_closed_right_aligned A strategy
        hwin one two input hfresh
    have hleft :=
      package.literalCombinedFreshPhaseLiveBoth_closed_left_aligned A strategy
        hwin one two input hfresh
    exact ⟨⟨hright.1, hright.2.1⟩, ⟨hleft.1, hleft.2.1⟩⟩

/-! ## Strict-round preservation -/

/-- One strict-right round preserves the selected invariant.  The old phase
decides only which already-proved local synchronization lemma applies:
same-direction in phases `ff`/`tf`, and the dormant-root switch lemma in phase
`tt`. -/
theorem literalCombinedFreshPhaseLiveStructuralSelected_strictRight
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (input : In₁ × In₂) :
    let oneNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one input.1
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.openControl
    package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
      oneNext.1 twoNext := by
  dsimp only
  rcases hselected with ⟨hfresh, hreachable, htables⟩
  refine ⟨?_, ?_, ?_⟩
  · change DecoratedFreshnessAligned A strategy hwin
      (decoratedFreshnessNoRecvOne A strategy hwin one.2.1.1 input.1)
      (decoratedFreshnessRecvTwo A strategy hwin package two.2.1.1 input.2
        one.2.1.1 input.1)
    exact decoratedFreshnessLocalStep_aligned A strategy hwin package
      one.2.1.1 two.2.1.1 hfresh input .right
  · change ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy
      hwin initial (CrossValid A strategy hwin) package.policy
        (decoratedFreshnessCurrent A strategy hwin
          (decoratedFreshnessNoRecvOne A strategy hwin one.2.1.1 input.1)
          (decoratedFreshnessRecvTwo A strategy hwin package two.2.1.1 input.2
            one.2.1.1 input.1))
    exact decoratedFreshnessLocalStep_current_reachable A strategy hwin
      package one.2.1.1 two.2.1.1 hfresh hreachable input .right
  · change
      package.LiteralLeftSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshTwoReceiver A strategy hwin false
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
              input.2 one input.1).1.openControl.2.1)
          (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
            (package.literalCombinedFreshOnePendingStep A strategy hwin) one
              input.1).1.2.1.2.1 ∧
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.openControl.2.1.2.1 =
          package.literalRightSeamStagedSenderInitial A strategy hwin
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
              input.2 one input.1).1.openControl.2.1.2.1.1
    refine ⟨?_, rfl⟩
    cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
      have haligned := htables.1
      exact package.literalCombinedFreshPhaseLiveRecvTwo_same_preserves A
        strategy hwin two one htwo haligned input
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
      have haligned := htables.2
      exact package.literalCombinedFreshPhaseLiveRecvTwo_same_preserves A
        strategy hwin two one htwo haligned input
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
      have hroot := htables.2
      exact package.literalCombinedFreshPhaseLiveRecvTwo_switch_preserves A
        strategy hwin two one htwo hroot input

/-- Mirror strict-left preservation.  Phases `tt`/`tf` use the retained right
receiver; phase `ff` uses the dormant right-sender root delivered by process
two. -/
theorem literalCombinedFreshPhaseLiveStructuralSelected_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (input : In₁ × In₂) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.openControl
    let twoNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two input.2
    package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
      oneNext twoNext.1 := by
  dsimp only
  rcases hselected with ⟨hfresh, hreachable, htables⟩
  refine ⟨?_, ?_, ?_⟩
  · change DecoratedFreshnessAligned A strategy hwin
      (decoratedFreshnessRecvOne A strategy hwin package one.2.1.1 input.1
        two.2.1.1 input.2)
      (decoratedFreshnessNoRecvTwo A strategy hwin two.2.1.1 input.2)
    exact decoratedFreshnessLocalStep_aligned A strategy hwin package
      one.2.1.1 two.2.1.1 hfresh input .left
  · change ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy
      hwin initial (CrossValid A strategy hwin) package.policy
        (decoratedFreshnessCurrent A strategy hwin
          (decoratedFreshnessRecvOne A strategy hwin package one.2.1.1 input.1
            two.2.1.1 input.2)
          (decoratedFreshnessNoRecvTwo A strategy hwin two.2.1.1 input.2))
    exact decoratedFreshnessLocalStep_current_reachable A strategy hwin
      package one.2.1.1 two.2.1.1 hfresh hreachable input .left
  · change
      package.LiteralRightSeamStagedControlsAligned A strategy hwin
          (package.literalCombinedFreshOneReceiver A strategy hwin false
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
              input.1 two input.2).1.openControl.2.1)
          (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
            (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
              input.2).1.2.1.2.1 ∧
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl.2.1.2.1 =
          package.literalLeftSeamStagedSenderInitial A strategy hwin
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
              input.1 two input.2).1.openControl.2.1.2.1.1
    refine ⟨?_, rfl⟩
    cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
      have hroot := htables.2
      exact package.literalCombinedFreshPhaseLiveRecvOne_switch_preserves A
        strategy hwin one two hone hroot input
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
      have haligned := htables.1
      exact package.literalCombinedFreshPhaseLiveRecvOne_same_preserves A
        strategy hwin one two hone haligned input
    · simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
      have haligned := htables.1
      exact package.literalCombinedFreshPhaseLiveRecvOne_same_preserves A
        strategy hwin one two hone haligned input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
