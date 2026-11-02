/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedDeferredTailAdapter

/-!
# Trace readback for the synchronized mega-linked tail root

A simultaneous front handoff installs one unresolved acknowledged fork at
both endpoints.  Equal fork identifiers select the synchronized closed
interpretation, whose linked controls start at the old `.both` checker row.
The open and closed controls are not equal: their receiver anchors and local
receive bits deliberately differ.  They nevertheless have the same effective
blind sender, which is the only coordinate read by a no-receive transition.

This file packages that weaker endpoint-local bisimulation, applies the generic
arbitrary-relay exact-closing trace adapter, and identifies the concrete
rerooted `FullRestart` word with its semantic common-root reference word.
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

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev TailPayload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev TailInnerOne :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (TailPayload A strategy hwin) PUnit.{1}

private abbrev TailInnerTwo :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (TailPayload A strategy hwin) PUnit.{1}

/-! ## The effective blind-sender relation -/

private noncomputable def profiledRawJointHybridMegaLinkedEffectiveRightSender
    (state : LinkedOne A strategy hwin) :=
  let base :=
    if state.2.1 then
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin (state.child A strategy hwin) false false
    else state.2.2.1
  base.1.1

private noncomputable def profiledRawJointHybridMegaLinkedEffectiveLeftSender
    (state : LinkedTwo A strategy hwin) :=
  let base :=
    if state.2.1 then
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin (state.child A strategy hwin) false false
    else state.2.2.1
  base.2.1

private def ProfiledRawJointHybridMegaLinkedCommonRootBlindOne
    (left right : TailInnerOne A strategy hwin) : Prop :=
  match left, right with
  | .inl left, .inl right =>
      profiledRawJointHybridMegaLinkedEffectiveRightSender A strategy hwin
          left.2.1 =
        profiledRawJointHybridMegaLinkedEffectiveRightSender A strategy hwin
          right.2.1
  | .inr left, .inr right => left = right
  | _, _ => False

private def ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo
    (left right : TailInnerTwo A strategy hwin) : Prop :=
  match left, right with
  | .inl left, .inl right =>
      profiledRawJointHybridMegaLinkedEffectiveLeftSender A strategy hwin
          left.2.1 =
        profiledRawJointHybridMegaLinkedEffectiveLeftSender A strategy hwin
          right.2.1
  | .inr left, .inr right => left = right
  | _, _ => False

private theorem profiledRawJointHybridMegaLinkedCommonRootBlindOne_noRecv
    (left right : TailInnerOne A strategy hwin) (input : In₁)
    (hblind : ProfiledRawJointHybridMegaLinkedCommonRootBlindOne A strategy hwin
      left right) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin left input).2 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
          A strategy hwin right input).2 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootBlindOne A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
          A strategy hwin left input).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
          A strategy hwin right input).1 := by
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          rcases left with ⟨leftMember, leftShared, leftPayload⟩
          rcases right with ⟨rightMember, rightShared, rightPayload⟩
          have hnext := congrArg
            (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A · input)
            hblind
          constructor
          · simpa only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne,
              FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
              FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne]
              using congrArg Prod.fst hnext
          · simpa only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne,
              FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
              FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne,
              ProfiledRawJointHybridMegaLinkedCommonRootBlindOne,
              profiledRawJointHybridMegaLinkedEffectiveRightSender,
              if_false] using congrArg Prod.snd hnext
      | inr right => exact False.elim hblind
  | inr left =>
      cases right with
      | inl right => exact False.elim hblind
      | inr right =>
          subst right
          exact ⟨rfl, rfl⟩

private theorem profiledRawJointHybridMegaLinkedCommonRootBlindTwo_noRecv
    (left right : TailInnerTwo A strategy hwin) (input : In₂)
    (hblind : ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo A strategy hwin
      left right) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin left input).2 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
          A strategy hwin right input).2 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
          A strategy hwin left input).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
          A strategy hwin right input).1 := by
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          rcases left with ⟨leftMember, leftShared, leftPayload⟩
          rcases right with ⟨rightMember, rightShared, rightPayload⟩
          have hnext := congrArg
            (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A · input)
            hblind
          constructor
          · simpa only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo,
              FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
              FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo]
              using congrArg Prod.fst hnext
          · simpa only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo,
              FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
              FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
              ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo,
              profiledRawJointHybridMegaLinkedEffectiveLeftSender,
              if_false] using congrArg Prod.snd hnext
      | inr right => exact False.elim hblind
  | inr left =>
      cases right with
      | inl right => exact False.elim hblind
      | inr right =>
          subst right
          exact ⟨rfl, rfl⟩

private theorem profiledRawJointHybridMegaLinkedDeferredBlind_to_commonRootBlindOne
    (left right : TailInnerOne A strategy hwin)
    (hblind :
      FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind left right) :
    ProfiledRawJointHybridMegaLinkedCommonRootBlindOne A strategy hwin left
      right := by
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          rcases hblind with ⟨hshared, _hpayload⟩
          change
            profiledRawJointHybridMegaLinkedEffectiveRightSender A strategy hwin
                left.2.1 =
              profiledRawJointHybridMegaLinkedEffectiveRightSender A strategy
                hwin right.2.1
          rw [hshared]
      | inr right => exact False.elim hblind
  | inr left =>
      cases right with
      | inl right => exact False.elim hblind
      | inr right => exact hblind

private theorem profiledRawJointHybridMegaLinkedDeferredBlind_to_commonRootBlindTwo
    (left right : TailInnerTwo A strategy hwin)
    (hblind :
      FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind left right) :
    ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo A strategy hwin left
      right := by
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          rcases hblind with ⟨hshared, _hpayload⟩
          change
            profiledRawJointHybridMegaLinkedEffectiveLeftSender A strategy hwin
                left.2.1 =
              profiledRawJointHybridMegaLinkedEffectiveLeftSender A strategy
                hwin right.2.1
          rw [hshared]
      | inr right => exact False.elim hblind
  | inr left =>
      cases right with
      | inl right => exact False.elim hblind
      | inr right => exact hblind

/-! ## Common-root semantic model -/

private theorem profiledRawJointHybridMegaLinkedCommonRoot_selected_relation
    (tag : RetainedTag A strategy hwin) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let common :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin tag.1
    let payload :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
        A strategy hwin tag.1
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback
        (.inl (false, common.1, payload) : TailInnerOne A strategy hwin)
        (.inl (false, common.2, payload) : TailInnerTwo A strategy hwin) := by
  dsimp only
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  intro _hflags
  rfl

private theorem profiledRawJointHybridMegaLinkedTailCommonRootForkPair_blindOne
    (tag : RetainedTag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointHybridMegaLinkedCommonRootBlindOne A strategy hwin)
      (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
        tag).1 := by
  rfl

private theorem profiledRawJointHybridMegaLinkedTailCommonRootForkPair_blindTwo
    (tag : RetainedTag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo A strategy hwin)
      (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
        tag).2 := by
  rfl

private noncomputable def profiledRawJointHybridMegaLinkedCommonRootBlindForkLaws
    (tag : RetainedTag A strategy hwin) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let common :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin tag.1
    let payload :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
        A strategy hwin tag.1
    let initialOne : TailInnerOne A strategy hwin :=
      .inl (false, common.1, payload)
    let initialTwo : TailInnerTwo A strategy hwin :=
      .inl (false, common.2, payload)
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkLaws
      initialOne initialTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin fallback)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
        A strategy hwin fallback)
      (ProfiledRawJointHybridMegaLinkedCommonRootBlindOne A strategy hwin)
      (ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo A strategy hwin) := by
  dsimp only
  let standard :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartAuthorityBlindForkLaws
      A strategy hwin tag
  refine {
    relation := {
      initial := profiledRawJointHybridMegaLinkedCommonRoot_selected_relation
        A strategy hwin tag
      strictRight := standard.relation.strictRight
      strictLeft := standard.relation.strictLeft
      both := standard.relation.both }
    noRecv := {
      one := profiledRawJointHybridMegaLinkedCommonRootBlindOne_noRecv A
        strategy hwin
      two := profiledRawJointHybridMegaLinkedCommonRootBlindTwo_noRecv A
        strategy hwin }
    receive := {
      one := ?_
      two := ?_ } }
  · intro one inputOne two inputTwo hrel
    exact
      profiledRawJointHybridMegaLinkedDeferredBlind_to_commonRootBlindOne A
        strategy hwin _ _
          (standard.receive.one one inputOne two inputTwo hrel)
  · intro one inputOne two inputTwo hrel
    exact
      profiledRawJointHybridMegaLinkedDeferredBlind_to_commonRootBlindTwo A
        strategy hwin _ _
          (standard.receive.two one inputOne two inputTwo hrel)

/-- The exact-closing semantic trace whose initial selected pair is the
synchronized common-root interpretation of the front fork. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    TailInnerOne A strategy hwin × TailInnerTwo A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let common :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
      A strategy hwin tag.1
  let payload :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin tag.1
  let initialOne : TailInnerOne A strategy hwin :=
    .inl (false, common.1, payload)
  let initialTwo : TailInnerTwo A strategy hwin :=
    .inl (false, common.2, payload)
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace initialOne
    initialTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin fallback) env n

/-- The common-root semantic run remains in the same pending/authority
relation used by the ordinary `FullRestart` cut construction. -/
theorem profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_invariant
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env n).1
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env n).2 := by
  dsimp only
  let laws :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRelationLaws
      A strategy hwin tag
  induction n with
  | zero =>
      exact profiledRawJointHybridMegaLinkedCommonRoot_selected_relation A
        strategy hwin tag
  | succ n ih =>
      rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
      split <;> rename_i hgraph
      · exact laws.strictRight _ _ _ _ ih
      · exact laws.strictLeft _ _ _ _ ih
      · exact laws.both _ _ _ _ ih

/-- The common-root run has the same exact graph-driven receive bits as the
ordinary restart run after every transition. -/
theorem
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_succ_selected_lastRecv
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let next :=
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
        tag env (n + 1)
    let selectedOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 next.1
    let selectedTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 next.2
    match (env n).graph with
    | .right => selectedOne.2.1 = false ∧ selectedTwo.2.1 = true
    | .left => selectedOne.2.1 = true ∧ selectedTwo.2.1 = false
    | .both => selectedOne.2.1 = false ∧ selectedTwo.2.1 = false := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let current :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
      tag env n
  have hnext :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env (n + 1) =
        match (env n).graph with
        | .right =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                A strategy hwin current.1 (env n).inputOne).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                A strategy hwin fallback current.2 (env n).inputTwo current.1
                  (env n).inputOne).1)
        | .left =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                A strategy hwin fallback current.1 (env n).inputOne current.2
                  (env n).inputTwo).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                A strategy hwin current.2 (env n).inputTwo).1)
        | .both =>
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
              A strategy hwin fallback current.1 (env n).inputOne current.2
                (env n).inputTwo := by
    rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
    rfl
  have hpending :=
    (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_invariant A
      strategy hwin tag env n).1
  change FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending
    current.1 current.2 at hpending
  cases hone : current.1 with
  | inr recurrent => exact False.elim (by simpa [hone] using hpending.1)
  | inl onePending =>
    cases htwo : current.2 with
    | inr recurrent => exact False.elim (by simpa [htwo] using hpending.2)
    | inl twoPending =>
      cases hgraph : (env n).graph with
      | right =>
          rw [hnext, hgraph, hone, htwo]
          exact ⟨
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv
              A strategy hwin fallback.1 onePending (env n).inputOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwo_openRecv_lastRecv
              A strategy hwin fallback (.inl twoPending) (env n).inputTwo
                (.inl onePending) (env n).inputOne⟩
      | left =>
          rw [hnext, hgraph, hone, htwo]
          exact ⟨
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOne_openRecv_lastRecv
              A strategy hwin fallback (.inl onePending) (env n).inputOne
                (.inl twoPending) (env n).inputTwo,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwo_noRecv_lastRecv
              A strategy hwin fallback.2 twoPending (env n).inputTwo⟩
      | both =>
          rw [hnext, hgraph, hone, htwo]
          exact ⟨rfl, rfl⟩

/-- Process-one semantic output of the common-root run. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let pair :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
      tag env n
  match (env n).graph with
  | .right =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin pair.1 (env n).inputOne).2
  | .left | .both =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback pair.1 (env n).inputOne pair.2
          (env n).inputTwo).2

/-- Process-two semantic output of the common-root run. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₂ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let pair :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
      tag env n
  match (env n).graph with
  | .right | .both =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback pair.2 (env n).inputTwo pair.1
          (env n).inputOne).2
  | .left =>
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin pair.2 (env n).inputTwo).2

/-- The acknowledged controller with the production common-root fork as its
physical initial relays. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootMealyController
    (tag : RetainedTag A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let common :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
      A strategy hwin tag.1
  let payload :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin tag.1
  let initialOne : TailInnerOne A strategy hwin :=
    .inl (false, common.1, payload)
  let initialTwo : TailInnerTwo A strategy hwin :=
    .inl (false, common.2, payload)
  FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.exactClosingPairedMealyControllerFromRelays
    initialOne initialTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin fallback)
      (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
        tag).1
      (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
        tag).2

/-- The common-root acknowledged implementation has exactly its canonical
selected semantic outputs. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootMealyTraceInvariant
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridMegaLinkedCommonRootMealyController A strategy hwin
      tag).LiteralCrossMealyTraceInvariant env := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let common :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
      A strategy hwin tag.1
  let payload :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin tag.1
  let initialOne : TailInnerOne A strategy hwin :=
    .inl (false, common.1, payload)
  let initialTwo : TailInnerTwo A strategy hwin :=
    .inl (false, common.2, payload)
  let noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin
  let openRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
      A strategy hwin fallback
  let openRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
      A strategy hwin fallback
  let close :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
      A strategy hwin fallback
  let Rel :=
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback
  let Selected :=
    FiniteAcknowledgedDelayedCarrier.ExactClosingCanonicalSelected initialOne
      initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let expectedOne :=
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne initialOne
      initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let expectedTwo :=
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo initialOne
      initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let traceLaws :=
    FiniteAcknowledgedDelayedCarrier.exactClosingCanonicalSelectedTraceLaws
      initialOne initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close
        env Rel
  apply
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariantFromRelays
      (initialOne := initialOne) (initialTwo := initialTwo)
      (noRecvOne := noRecvOne) (noRecvTwo := noRecvTwo)
      (openRecvOne := openRecvOne) (openRecvTwo := openRecvTwo)
      (close := close) (Rel := Rel)
      (BlindOne :=
        ProfiledRawJointHybridMegaLinkedCommonRootBlindOne A strategy hwin)
      (BlindTwo :=
        ProfiledRawJointHybridMegaLinkedCommonRootBlindTwo A strategy hwin)
      (Selected := Selected) (env := env)
      (expectedOutputOne := expectedOne) (expectedOutputTwo := expectedTwo)
      (rootOne :=
        (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
          tag).1)
      (rootTwo :=
        (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
          tag).2)
  · exact ⟨
      profiledRawJointHybridMegaLinkedTailCommonRootForkPair_resolves_one A
        strategy hwin tag,
      profiledRawJointHybridMegaLinkedTailCommonRootForkPair_resolves_two A
        strategy hwin tag⟩
  · exact
      profiledRawJointHybridMegaLinkedTailCommonRootForkPair_blindOne A strategy
        hwin tag
  · exact
      profiledRawJointHybridMegaLinkedTailCommonRootForkPair_blindTwo A strategy
        hwin tag
  · exact
      profiledRawJointHybridMegaLinkedCommonRootBlindForkLaws A strategy hwin
        tag
  · exact traceLaws

noncomputable def profiledRawJointHybridMegaLinkedCommonRootTraceInvariant
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    ((profiledRawJointHybridMegaLinkedCommonRootMealyController A strategy hwin
      tag).mooreize).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointHybridMegaLinkedCommonRootMealyTraceInvariant A strategy hwin
    tag env).toMooreTraceInvariant _

/-- Semantic reference word read by the synchronized common-root invariant. -/
noncomputable def profiledRawJointHybridMegaLinkedCommonRootReferenceWord
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let controller :=
    (profiledRawJointHybridMegaLinkedCommonRootMealyController A strategy hwin
      tag).mooreize
  (profiledRawJointHybridMegaLinkedCommonRootTraceInvariant A strategy hwin tag
    env).referenceWord controller

@[simp] theorem
    profiledRawJointHybridMegaLinkedCommonRootReferenceWord_outputPair
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
      tag env n).outputPair =
      (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy
          hwin tag env n,
        profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
          hwin tag env n) := by
  rfl

/-! ## Concrete physical readback -/

/-- Stale Moore outputs stored by the handoff are ignored by the next
transition.  The rerooted production `FullRestart` word is therefore exactly
the verified common-root semantic reference word. -/
theorem profiledRawJointHybridMegaLinkedTailCommonRootForkPair_word_eq_reference
    (tag : RetainedTag A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag
    let fork :=
      profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin tag
    let entry := ((fork.1, oldOutputOne), (fork.2, oldOutputTwo))
    (linked.globalMachine.reroot entry).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo env =
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        tag env := by
  dsimp only
  let customMealy :=
    profiledRawJointHybridMegaLinkedCommonRootMealyController A strategy hwin tag
  let custom := customMealy.mooreize
  let invariant :=
    profiledRawJointHybridMegaLinkedCommonRootTraceInvariant A strategy hwin tag
      env
  let linked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin tag
  let fork :=
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin tag
  let entry := ((fork.1, oldOutputOne), (fork.2, oldOutputTwo))
  calc
    (linked.globalMachine.reroot entry).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo env =
      custom.globalMachine.globalMachineTraceWord custom.globalOutputOne
        custom.globalOutputTwo env := by
      apply
        FiniteGlobalRoundMachine.reroot_globalMachineTraceWord_eq_of_first_step_eq
      cases hgraph : (env 0).graph <;> rfl
    _ = invariant.referenceWord custom :=
      invariant.globalMachineTraceWord_eq_referenceWord custom

end

end DetParityAutomaton

end DistributedSynthesis
