/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootAcceptance

/-!
# Common-root to full-restart splice

After a synchronized mega handoff, dormant deferred payloads may differ from
the ordinary full-restart initialization.  On a no-simultaneous tail they are
never selected.  This module records the exact observational relation and
shows that the first strict orientation reversal installs the canonical fresh
restart at the authoritative parent.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

def ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne
    (left right : OneControl A strategy hwin) : Prop :=
  ∃ shared payloadLeft payloadRight,
    left = .inl (false, shared, payloadLeft) ∧
      right = .inl (false, shared, payloadRight)

def ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo
    (left right : TwoControl A strategy hwin) : Prop :=
  ∃ shared payloadLeft payloadRight,
    left = .inl (false, shared, payloadLeft) ∧
      right = .inl (false, shared, payloadRight)

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_noRecvOne
    (shared : LinkedOne A strategy hwin)
    (payloadLeft payloadRight : Payload A strategy hwin)
    (input : In₁) :
    let left :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin
          (.inl (false, shared, payloadLeft) : OneControl A strategy hwin) input
    let right :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin
          (.inl (false, shared, payloadRight) : OneControl A strategy hwin) input
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin left.1 right.1 ∧
      left.2 = right.2 := by
  exact ⟨⟨_, _, _, rfl, rfl⟩, rfl⟩

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_noRecvTwo
    (shared : LinkedTwo A strategy hwin)
    (payloadLeft payloadRight : Payload A strategy hwin)
    (input : In₂) :
    let left :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin
          (.inl (false, shared, payloadLeft) : TwoControl A strategy hwin) input
    let right :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin
          (.inl (false, shared, payloadRight) : TwoControl A strategy hwin) input
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin left.1 right.1 ∧
      left.2 = right.2 := by
  exact ⟨⟨_, _, _, rfl, rfl⟩, rfl⟩

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_openRecvTwo
    (leftTag rightTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : LinkedOne A strategy hwin)
    (two : LinkedTwo A strategy hwin)
    (payloadLeftOne payloadRightOne payloadLeftTwo payloadRightTwo :
      Payload A strategy hwin)
    (input : In₁ × In₂) :
    let leftNext :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin leftTag)
          (.inl (false, two, payloadLeftTwo) : TwoControl A strategy hwin)
          input.2
          (.inl (false, one, payloadLeftOne) : OneControl A strategy hwin)
          input.1
    let rightNext :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin rightTag)
          (.inl (false, two, payloadRightTwo) : TwoControl A strategy hwin)
          input.2
          (.inl (false, one, payloadRightOne) : OneControl A strategy hwin)
          input.1
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin leftNext.1 rightNext.1 ∧
      leftNext.2 = rightNext.2 := by
  let leftFallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin leftTag
  let rightFallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin rightTag
  let leftReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
      A strategy hwin leftFallback
        (.inl (false, two, payloadLeftTwo) : TwoControl A strategy hwin)
        input.2
        (.inl (false, one, payloadLeftOne) : OneControl A strategy hwin)
        input.1
  let rightReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
      A strategy hwin rightFallback
        (.inl (false, two, payloadRightTwo) : TwoControl A strategy hwin)
        input.2
        (.inl (false, one, payloadRightOne) : OneControl A strategy hwin)
        input.1
  have hreceived : leftReceived = rightReceived := by
    change
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
          A strategy hwin two input.2 one input.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
          A strategy hwin two input.2 one input.1
    rfl
  let leftFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin leftFallback
        (.inl (false, two, payloadLeftTwo) : TwoControl A strategy hwin)
        input.2
        (.inl (false, one, payloadLeftOne) : OneControl A strategy hwin)
        input.1
  let rightFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin rightFallback
        (.inl (false, two, payloadRightTwo) : TwoControl A strategy hwin)
        input.2
        (.inl (false, one, payloadRightOne) : OneControl A strategy hwin)
        input.1
  have hfreshFst : leftFresh.1 = rightFresh.1 := by
    change leftReceived = rightReceived
    exact hreceived
  constructor
  · refine ⟨leftFresh.1, leftFresh.2, rightFresh.2, rfl, ?_⟩
    change
      Sum.inl (false, rightFresh.1, rightFresh.2) =
        Sum.inl (false, leftFresh.1, rightFresh.2)
    rw [hfreshFst]
  · change leftReceived.1 = rightReceived.1
    exact congrArg Prod.fst hreceived

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_openRecvOne
    (leftTag rightTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : LinkedOne A strategy hwin)
    (two : LinkedTwo A strategy hwin)
    (payloadLeftOne payloadRightOne payloadLeftTwo payloadRightTwo :
      Payload A strategy hwin)
    (input : In₁ × In₂) :
    let leftNext :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin leftTag)
          (.inl (false, one, payloadLeftOne) : OneControl A strategy hwin)
          input.1
          (.inl (false, two, payloadLeftTwo) : TwoControl A strategy hwin)
          input.2
    let rightNext :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin rightTag)
          (.inl (false, one, payloadRightOne) : OneControl A strategy hwin)
          input.1
          (.inl (false, two, payloadRightTwo) : TwoControl A strategy hwin)
          input.2
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin leftNext.1 rightNext.1 ∧
      leftNext.2 = rightNext.2 := by
  let leftFallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin leftTag
  let rightFallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin rightTag
  let leftReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
      A strategy hwin leftFallback
        (.inl (false, one, payloadLeftOne) : OneControl A strategy hwin)
        input.1
        (.inl (false, two, payloadLeftTwo) : TwoControl A strategy hwin)
        input.2
  let rightReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
      A strategy hwin rightFallback
        (.inl (false, one, payloadRightOne) : OneControl A strategy hwin)
        input.1
        (.inl (false, two, payloadRightTwo) : TwoControl A strategy hwin)
        input.2
  have hreceived : leftReceived = rightReceived := by
    change
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
          A strategy hwin one input.1 two input.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
          A strategy hwin one input.1 two input.2
    rfl
  let leftFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin leftFallback
        (.inl (false, one, payloadLeftOne) : OneControl A strategy hwin)
        input.1
        (.inl (false, two, payloadLeftTwo) : TwoControl A strategy hwin)
        input.2
  let rightFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin rightFallback
        (.inl (false, one, payloadRightOne) : OneControl A strategy hwin)
        input.1
        (.inl (false, two, payloadRightTwo) : TwoControl A strategy hwin)
        input.2
  have hfreshFst : leftFresh.1 = rightFresh.1 := by
    change leftReceived = rightReceived
    exact hreceived
  constructor
  · refine ⟨leftFresh.1, leftFresh.2, rightFresh.2, rfl, ?_⟩
    change
      Sum.inl (false, rightFresh.1, rightFresh.2) =
        Sum.inl (false, leftFresh.1, rightFresh.2)
    rw [hfreshFst]
  · change leftReceived.1 = rightReceived.1
    exact congrArg Prod.fst hreceived

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_strictRight
    (leftTag rightTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftOne rightOne : OneControl A strategy hwin)
    (leftTwo rightTwo : TwoControl A strategy hwin)
    (input : In₁ × In₂)
    (hone : ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin leftOne rightOne)
    (htwo : ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin leftTwo rightTwo) :
    let leftFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin leftTag
    let rightFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin rightTag
    let leftNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin leftOne input.1
    let rightNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin rightOne input.1
    let leftNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin leftFallback leftTwo input.2 leftOne input.1
    let rightNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin rightFallback rightTwo input.2 rightOne input.1
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin leftNextOne.1 rightNextOne.1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin leftNextTwo.1 rightNextTwo.1 ∧
      (leftNextOne.2, leftNextTwo.2) =
        (rightNextOne.2, rightNextTwo.2) := by
  rcases hone with ⟨one, payloadLeftOne, payloadRightOne, rfl, rfl⟩
  rcases htwo with ⟨two, payloadLeftTwo, payloadRightTwo, rfl, rfl⟩
  have hone := profiledRawJointHybridMegaLinkedCommonRootOpenRel_noRecvOne A strategy hwin one payloadLeftOne
    payloadRightOne input.1
  have htwo := profiledRawJointHybridMegaLinkedCommonRootOpenRel_openRecvTwo A strategy hwin leftTag rightTag one two
    payloadLeftOne payloadRightOne payloadLeftTwo payloadRightTwo input
  dsimp only
  exact ⟨hone.1, htwo.1, Prod.ext hone.2 htwo.2⟩

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_strictLeft
    (leftTag rightTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftOne rightOne : OneControl A strategy hwin)
    (leftTwo rightTwo : TwoControl A strategy hwin)
    (input : In₁ × In₂)
    (hone : ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin leftOne rightOne)
    (htwo : ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin leftTwo rightTwo) :
    let leftFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin leftTag
    let rightFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin rightTag
    let leftNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin leftFallback leftOne input.1 leftTwo input.2
    let rightNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin rightFallback rightOne input.1 rightTwo input.2
    let leftNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin leftTwo input.2
    let rightNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin rightTwo input.2
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin leftNextOne.1 rightNextOne.1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin leftNextTwo.1 rightNextTwo.1 ∧
      (leftNextOne.2, leftNextTwo.2) =
        (rightNextOne.2, rightNextTwo.2) := by
  rcases hone with ⟨one, payloadLeftOne, payloadRightOne, rfl, rfl⟩
  rcases htwo with ⟨two, payloadLeftTwo, payloadRightTwo, rfl, rfl⟩
  have hone := profiledRawJointHybridMegaLinkedCommonRootOpenRel_openRecvOne A strategy hwin leftTag rightTag one two
    payloadLeftOne payloadRightOne payloadLeftTwo payloadRightTwo input
  have htwo := profiledRawJointHybridMegaLinkedCommonRootOpenRel_noRecvTwo A strategy hwin two payloadLeftTwo
    payloadRightTwo input.2
  dsimp only
  exact ⟨hone.1, htwo.1, Prod.ext hone.2 htwo.2⟩

theorem commonRootRightSwitch_retainedNoRecvOne
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (input : In₁) (hone : one.2.1 = true) :
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two
    let restartTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin :=
      (parent, (false, false))
    let standard :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin restartTag).1
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
        A strategy hwin one input =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
        A strategy hwin standard input := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay,
    hone]
  rfl

theorem commonRootRightSwitch_retainedRecvTwo
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (input : In₁ × In₂) (hone : one.2.1 = true)
    (htwo : two.2.1 = false) :
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two
    let restartTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin :=
      (parent, (false, false))
    let standard :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin restartTag
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin two input.2 one input.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin standard.2 input.2 standard.1 input.1 := by
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
      A strategy hwin one two
  let restartTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin :=
    (parent, (false, false))
  let standard :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin restartTag
  change
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin two input.2 one input.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin standard.2 input.2 standard.1 input.1
  have hparent : parent = one.child A strategy hwin := by
    simp [parent,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
      hone]
  have hstandardTwo : standard.2.2.1 = false := by
    rfl
  have hstandardChild : standard.1.child A strategy hwin = parent := by
    rfl
  have hbase :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin one two =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
          A strategy hwin standard.1 standard.2 := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
      htwo, hstandardTwo, hstandardChild, hparent]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay]
  rw [hbase]

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_rightSwitch
    (leftTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (payloadOne payloadTwo : Payload A strategy hwin)
    (input : In₁ × In₂) (hone : one.2.1 = true)
    (htwo : two.2.1 = false) :
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two
    let restartTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin :=
      (parent, (false, false))
    let leftFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin leftTag
    let rightFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin restartTag
    let leftOne : OneControl A strategy hwin :=
      .inl (false, one, payloadOne)
    let leftTwo : TwoControl A strategy hwin :=
      .inl (false, two, payloadTwo)
    let rightOne : OneControl A strategy hwin :=
      .inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
          A strategy hwin restartTag)
    let rightTwo : TwoControl A strategy hwin :=
      .inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
          A strategy hwin restartTag)
    let leftNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin leftOne input.1
    let rightNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin rightOne input.1
    let leftNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin leftFallback leftTwo input.2 leftOne input.1
    let rightNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin rightFallback rightTwo input.2 rightOne input.1
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin leftNextOne.1 rightNextOne.1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin leftNextTwo.1 rightNextTwo.1 ∧
      (leftNextOne.2, leftNextTwo.2) =
        (rightNextOne.2, rightNextTwo.2) := by
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
      A strategy hwin one two
  let restartTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin :=
    (parent, (false, false))
  let standard :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin restartTag
  let standardPayload :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin parent
  let leftNo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
      A strategy hwin one input.1
  let rightNo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
      A strategy hwin standard.1 input.1
  have hno : leftNo = rightNo :=
    commonRootRightSwitch_retainedNoRecvOne A strategy hwin one two input.1 hone
  let leftFallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin leftTag
  let leftReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
      A strategy hwin leftFallback
        (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
        (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
  let rightReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
      A strategy hwin standard
        (.inl (false, standard.2, standardPayload) : TwoControl A strategy hwin)
        input.2
        (.inl (false, standard.1, standardPayload) : OneControl A strategy hwin)
        input.1
  have hreceived : leftReceived = rightReceived := by
    change
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
          A strategy hwin two input.2 one input.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
          A strategy hwin standard.2 input.2 standard.1 input.1
    exact commonRootRightSwitch_retainedRecvTwo A strategy hwin one two input hone htwo
  let leftFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin leftFallback
        (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
        (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
  let rightFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin standard
        (.inl (false, standard.2, standardPayload) : TwoControl A strategy hwin)
        input.2
        (.inl (false, standard.1, standardPayload) : OneControl A strategy hwin)
        input.1
  have hfreshFst : leftFresh.1 = rightFresh.1 := by
    change leftReceived = rightReceived
    exact hreceived
  let leftNextOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin
        (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
  let rightNextOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin
        (.inl (false, standard.1, standardPayload) : OneControl A strategy hwin)
        input.1
  let leftNextTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
      A strategy hwin leftFallback
        (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
        (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
  let rightNextTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
      A strategy hwin standard
        (.inl (false, standard.2, standardPayload) : TwoControl A strategy hwin)
        input.2
        (.inl (false, standard.1, standardPayload) : OneControl A strategy hwin)
        input.1
  have houtputs :
      (leftNextOne.2, leftNextTwo.2) =
        (rightNextOne.2, rightNextTwo.2) := by
    change (leftNo.1, leftReceived.1) = (rightNo.1, rightReceived.1)
    exact congrArg₂ (fun first second ↦ (first, second))
      (congrArg Prod.fst hno) (congrArg Prod.fst hreceived)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨leftNo, payloadOne, standardPayload, rfl, ?_⟩
    change Sum.inl (false, rightNo, standardPayload) =
      Sum.inl (false, leftNo, standardPayload)
    rw [hno]
  · refine ⟨leftFresh.1, leftFresh.2, rightFresh.2, rfl, ?_⟩
    change Sum.inl (false, rightFresh.1, rightFresh.2) =
      Sum.inl (false, leftFresh.1, rightFresh.2)
    rw [hfreshFst]
  · exact houtputs

theorem commonRootLeftSwitch_retainedNoRecvTwo
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (input : In₂) (htwo : two.2.1 = true)
    (hone : one.2.1 = false) :
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two
    let restartTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin :=
      (parent, (false, false))
    let standard :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin restartTag).2
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
        A strategy hwin two input =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
        A strategy hwin standard input := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay,
    hone, htwo]
  rfl

theorem commonRootLeftSwitch_retainedRecvOne
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (input : In₁ × In₂) (hone : one.2.1 = false)
    (htwo : two.2.1 = true) :
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two
    let restartTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin :=
      (parent, (false, false))
    let standard :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin restartTag
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin one input.1 two input.2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin standard.1 input.1 standard.2 input.2 := by
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
      A strategy hwin one two
  let restartTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin :=
    (parent, (false, false))
  let standard :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin restartTag
  change
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin one input.1 two input.2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin standard.1 input.1 standard.2 input.2
  have hparent : parent = two.child A strategy hwin := by
    simp [parent,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
      hone]
  have hstandardOne : standard.1.2.1 = false := by
    rfl
  have hstandardChild : standard.2.child A strategy hwin = parent := by
    rfl
  have hbase :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin one two =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
          A strategy hwin standard.1 standard.2 := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
      hone, hstandardOne, hstandardChild, hparent]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay]
  rw [hbase]

theorem profiledRawJointHybridMegaLinkedCommonRootOpenRel_leftSwitch
    (leftTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (payloadOne payloadTwo : Payload A strategy hwin)
    (input : In₁ × In₂) (hone : one.2.1 = false)
    (htwo : two.2.1 = true) :
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two
    let restartTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin :=
      (parent, (false, false))
    let leftFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin leftTag
    let rightFallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin restartTag
    let leftOne : OneControl A strategy hwin :=
      .inl (false, one, payloadOne)
    let leftTwo : TwoControl A strategy hwin :=
      .inl (false, two, payloadTwo)
    let rightOne : OneControl A strategy hwin :=
      .inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
          A strategy hwin restartTag)
    let rightTwo : TwoControl A strategy hwin :=
      .inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
          A strategy hwin restartTag)
    let leftNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin leftFallback leftOne input.1 leftTwo input.2
    let rightNextOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin rightFallback rightOne input.1 rightTwo input.2
    let leftNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin leftTwo input.2
    let rightNextTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin rightTwo input.2
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin leftNextOne.1 rightNextOne.1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin leftNextTwo.1 rightNextTwo.1 ∧
      (leftNextOne.2, leftNextTwo.2) =
        (rightNextOne.2, rightNextTwo.2) := by
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
      A strategy hwin one two
  let restartTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin :=
    (parent, (false, false))
  let standard :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin restartTag
  let standardPayload :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin parent
  let leftNo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
      A strategy hwin two input.2
  let rightNo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
      A strategy hwin standard.2 input.2
  have hno : leftNo = rightNo :=
    commonRootLeftSwitch_retainedNoRecvTwo A strategy hwin one two input.2 htwo hone
  let leftFallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin leftTag
  let leftReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
      A strategy hwin leftFallback
        (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
        (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
  let rightReceived :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
      A strategy hwin standard
        (.inl (false, standard.1, standardPayload) : OneControl A strategy hwin)
        input.1
        (.inl (false, standard.2, standardPayload) : TwoControl A strategy hwin)
        input.2
  have hreceived : leftReceived = rightReceived := by
    change
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
          A strategy hwin one input.1 two input.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
          A strategy hwin standard.1 input.1 standard.2 input.2
    exact commonRootLeftSwitch_retainedRecvOne A strategy hwin one two input hone htwo
  let leftFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin leftFallback
        (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
        (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
  let rightFresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin standard
        (.inl (false, standard.1, standardPayload) : OneControl A strategy hwin)
        input.1
        (.inl (false, standard.2, standardPayload) : TwoControl A strategy hwin)
        input.2
  have hfreshFst : leftFresh.1 = rightFresh.1 := by
    change leftReceived = rightReceived
    exact hreceived
  let leftNextOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
      A strategy hwin leftFallback
        (.inl (false, one, payloadOne) : OneControl A strategy hwin) input.1
        (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
  let rightNextOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
      A strategy hwin standard
        (.inl (false, standard.1, standardPayload) : OneControl A strategy hwin)
        input.1
        (.inl (false, standard.2, standardPayload) : TwoControl A strategy hwin)
        input.2
  let leftNextTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin
        (.inl (false, two, payloadTwo) : TwoControl A strategy hwin) input.2
  let rightNextTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin
        (.inl (false, standard.2, standardPayload) : TwoControl A strategy hwin)
        input.2
  have houtputs :
      (leftNextOne.2, leftNextTwo.2) =
        (rightNextOne.2, rightNextTwo.2) := by
    change (leftReceived.1, leftNo.1) = (rightReceived.1, rightNo.1)
    exact congrArg₂ (fun first second ↦ (first, second))
      (congrArg Prod.fst hreceived) (congrArg Prod.fst hno)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨leftFresh.1, leftFresh.2, rightFresh.2, rfl, ?_⟩
    change Sum.inl (false, rightFresh.1, rightFresh.2) =
      Sum.inl (false, leftFresh.1, rightFresh.2)
    rw [hfreshFst]
  · refine ⟨leftNo, payloadTwo, standardPayload, rfl, ?_⟩
    change Sum.inl (false, rightNo, standardPayload) =
      Sum.inl (false, leftNo, standardPayload)
    rw [hno]
  · exact houtputs

/-! ## Open-member persistence on a strict tail -/

/-- Without a simultaneous round, both common-root semantic controls stay on
their ordinary (`false`) deferred member. -/
theorem profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_open_of_noBoth
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both) (n : Nat) :
    let pair :=
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
        tag env n
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        pair.1 pair.1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        pair.2 pair.2 := by
  induction n with
  | zero =>
      exact ⟨⟨_, _, _, rfl, rfl⟩, ⟨_, _, _, rfl, rfl⟩⟩
  | succ n ih =>
      let pair :=
        profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env n
      cases hgraph : (env n).graph with
      | right =>
          have hstep :=
            profiledRawJointHybridMegaLinkedCommonRootOpenRel_strictRight A
              strategy hwin tag tag pair.1 pair.1 pair.2 pair.2
                ((env n).inputOne, (env n).inputTwo) ih.1 ih.2
          simpa only [
            profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using And.intro hstep.1 hstep.2.1
      | left =>
          have hstep :=
            profiledRawJointHybridMegaLinkedCommonRootOpenRel_strictLeft A
              strategy hwin tag tag pair.1 pair.1 pair.2 pair.2
                ((env n).inputOne, (env n).inputTwo) ih.1 ih.2
          simpa only [
            profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using And.intro hstep.1 hstep.2.1
      | both =>
          exact False.elim (hnoBoth n hgraph)

/-! ## Canonical full-restart semantic outputs -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin tag env n
  match (env n).graph with
  | .right =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin pair.1 (env n).inputOne).2
  | .left | .both =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback pair.1 (env n).inputOne pair.2
          (env n).inputTwo).2

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₂ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin tag env n
  match (env n).graph with
  | .right | .both =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback pair.2 (env n).inputTwo pair.1
          (env n).inputOne).2
  | .left =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin pair.2 (env n).inputTwo).2

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_outputPair
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
      A strategy hwin tag env n).outputPair =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
          A strategy hwin tag env n,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
          A strategy hwin tag env n) := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord]
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
