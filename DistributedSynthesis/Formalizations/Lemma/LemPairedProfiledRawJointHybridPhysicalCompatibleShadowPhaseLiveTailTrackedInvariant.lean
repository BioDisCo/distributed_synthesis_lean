/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTracked

/-!
# The proof-only tracked invariant of the finite tail controller

The executable controller carries only its finite pending controls.  This file
adds the semantic induction invariant which says that each phase-selected
table is a reachable literal prefix of the installed winning play.  Its
successor key is therefore derived from the selected table itself; it is not
an extra transition oracle or a leader signal.
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

/-! ## Four phase-indexed tracked tables -/

def ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
    one.2.1.baseShared (two.2.1.receiver two.1)

def ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
    two.2.1.baseShared (one.2.1.receiver one.1)

def ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchTracked
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
    one.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
        hwin tag one.2.1.basePayload one.1)

def ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchTracked
    (tag : Tag A strategy hwin) (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
    two.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
        hwin tag two.2.1.basePayload two.1)

/-- The semantic invariant follows the same four local-phase cases as the
finite table invariant. -/
def ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  match one.2.1.localPhase, two.2.1.localPhase with
  | false, false =>
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
          hwin tag one two ∧
        ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchTracked A strategy
          hwin tag two
  | true, true =>
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
          hwin tag one two ∧
        ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchTracked A strategy
          hwin tag one
  | true, false =>
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy
          hwin tag one two ∧
        ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy
          hwin tag one two
  | false, true => False

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.tableInvariant
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin tag
      one two := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchTracked] at hinvariant
    simpa [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant,
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned, hone, htwo]
      using And.intro
        (hinvariant.1.aligned A strategy hwin)
        (hinvariant.2.aligned A strategy hwin)
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo] at hinvariant
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked] at hinvariant
    simpa [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant,
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned, hone, htwo]
      using And.intro
        (hinvariant.1.aligned A strategy hwin)
        (hinvariant.2.aligned A strategy hwin)
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked,
      ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchTracked] at hinvariant
    simpa [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned, hone, htwo]
      using And.intro
        (hinvariant.1.aligned A strategy hwin)
        (hinvariant.2.aligned A strategy hwin)

/-! ## The locally selected tracked table -/

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.right_selected
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
      one.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      htwo] using hinvariant.1
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo] at hinvariant
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      htwo] using hinvariant.1
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchTracked]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      htwo] using hinvariant.2

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.left_selected
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
      two.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchTracked]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      hone] using hinvariant.2
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo] at hinvariant
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      hone] using hinvariant.2
  · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      hone, htwo, ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      hone] using hinvariant.1

/-! ## Simultaneous receive: both fresh current tables are tracked -/

theorem profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_bothTracked
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy hwin
        tag fresh.1.1.closedControl fresh.1.2.closedControl ∧
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy hwin
        tag fresh.1.1.closedControl fresh.1.2.closedControl := by
  dsimp only
  let leftReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let rightReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let leftResult :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
      tag fallbackLeft two.2.1.baseShared leftReceiver input
  let rightResult :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
      tag fallbackRight one.2.1.baseShared rightReceiver (input.2, input.1)
  let leftRow :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
      leftReceiver
  let rightRow :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
      tag rightReceiver
  have hleftSelected := hinvariant.left_selected A strategy hwin
  have hrightSelected := hinvariant.right_selected A strategy hwin
  have hleftReach := hleftSelected.owner_reachable A strategy hwin
  have hrightReach := hrightSelected.owner_reachable A strategy hwin
  have hleftKey := hleftSelected.key A strategy hwin fallbackLeft input
  have hrightKey :=
    hrightSelected.key A strategy hwin fallbackRight (input.2, input.1)
  dsimp only at hleftKey hrightKey
  have hright :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRight_tracked_of_key A
      strategy hwin tag two.2.1.baseShared.1 hleftReach
        one.2.1.baseShared leftResult.1 leftRow true hleftKey
  have hleft :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeft_tracked_of_key A strategy
      hwin tag one.2.1.baseShared.1 hrightReach two.2.1.baseShared
        rightResult.1 rightRow true hrightKey
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      leftReceiver, rightReceiver, leftResult, rightResult, leftRow, rightRow,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
    using And.intro hright hleft

theorem profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_trackedInvariant
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
      tag fresh.1.1.closedControl fresh.1.2.closedControl := by
  dsimp only
  have hboth :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_bothTracked A
      strategy hwin tag fallbackLeft fallbackRight one two input hinvariant
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair]
    using hboth

/-! ## Strict one-way rounds -/

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.strictRight
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two)
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
  let selected := hinvariant.right_selected A strategy hwin
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

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.strictLeft
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two)
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
  let selected := hinvariant.left_selected A strategy hwin
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
