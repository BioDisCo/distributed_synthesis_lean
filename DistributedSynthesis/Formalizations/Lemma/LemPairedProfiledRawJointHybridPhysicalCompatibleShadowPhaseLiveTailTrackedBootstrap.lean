/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedInvariant

/-!
# One-live-lane bootstrap for the tagged tail invariant

At the first one-sided child, the public incidence code need not carry two
simultaneously live thread roots.  The delivered tag selects the one lane that
is genuinely live there.  A strict round in that lane both advances the live
table and constructs the opposite table from its exact successor key, so the
ordinary two-table tracked invariant holds afterwards.

These statements are proof-side.  Neither endpoint tests the strict direction
or learns which lane supplied the bootstrap.
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

/-- A single tracked right table is sufficient to enter the full invariant on
the next strict-right round. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked.strictRight
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
        hwin tag one two)
    (hphase : two.2.1.localPhase = false)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (input : In₁ × In₂) :
    let oneNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
          tag) one input.1).1
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    let twoNext := fresh.1.2.openControl
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin tag
      oneNext twoNext := by
  dsimp only
  have selected :
      ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
        one.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag two one) := by
    simpa [ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      hphase] using tracked
  have hright :=
    selected.step A strategy hwin fallbackRight one.1 (input.2, input.1)
  have hreach := selected.owner_reachable A strategy hwin
  have hrightKey :=
    selected.key A strategy hwin fallbackRight (input.2, input.1)
  dsimp only at hrightKey
  let rightReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let rightResult :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRightResult A strategy hwin tag
      fallbackRight one two input
  let rightRow :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin tag
      rightReceiver
  have hleft :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeft_tracked_of_key A strategy
      hwin tag one.2.1.baseShared.1 hreach two.2.1.baseShared rightResult.1
        rightRow false hrightKey
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchTracked,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      profiledRawJointHybridShadowPhaseLiveTailFreshRightResult,
      profiledRawJointHybridShadowPhaseLiveTailRecvTwoRight,
      profiledRawJointHybridShadowPhaseLiveTailOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      rightReceiver, rightResult, rightRow]
    using And.intro hright hleft

/-- A single tracked left table is sufficient to enter the full invariant on
the next strict-left round. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked.strictLeft
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
        hwin tag one two)
    (hphase : one.2.1.localPhase = true)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (input : In₁ × In₂) :
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    let oneNext := fresh.1.1.openControl
    let twoNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
          tag) two input.2).1
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin tag
      oneNext twoNext := by
  dsimp only
  have selected :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
        two.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag one two) := by
    simpa [ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      hphase] using tracked
  have hleft := selected.step A strategy hwin fallbackLeft two.1 input
  have hreach := selected.owner_reachable A strategy hwin
  have hleftKey := selected.key A strategy hwin fallbackLeft input
  dsimp only at hleftKey
  let leftReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let leftResult :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult A strategy hwin tag
      fallbackLeft one two input
  let leftRow :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
      leftReceiver
  have hright :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRight_tracked_of_key A strategy
      hwin tag two.2.1.baseShared.1 hreach one.2.1.baseShared leftResult.1
        leftRow false hleftKey
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked,
      ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchTracked,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult,
      profiledRawJointHybridShadowPhaseLiveTailRecvOneLeft,
      profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      leftReceiver, leftResult, leftRow]
    using And.intro hleft hright

end

end DetParityAutomaton

end DistributedSynthesis
