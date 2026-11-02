/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartAnchorRowOperationalConstancy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutOutput

/-!
# Reachable equivalence with the fixed-`.first` FullRestart controller

The anchor-row receive differs from the mature FullRestart receive only on
states whose selected receiver anchor is not `.first`.  The global reachable
row invariant rules those states out.  This module first records the local
receive and acknowledged-wrapper equalities; these are the transition seam
for identifying the two reachable traces.
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

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

/-! ## Local fixed-row reduction -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_eq_fixed
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁)
    (hrow :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin partner state) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo
        A strategy hwin state own partner delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin state own partner delivered := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo]
  rw [hrow]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_eq_fixed
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂)
    (hrow :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin state partner) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne
        A strategy hwin state own partner delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin state own partner delivered := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne]
  rw [hrow]

/-! ## Acknowledged receive wrappers -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedTwo_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedTwo
        A strategy hwin fallback two own one delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
        A strategy hwin fallback two own one delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedTwo
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvTwo_eq_fixed
      A strategy hwin
  exact hrow

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedOne_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedOne
        A strategy hwin fallback one own two delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
        A strategy hwin fallback one own two delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedOne
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRecvOne_eq_fixed
      A strategy hwin
  exact hrow

/-! ## Fresh packets and acknowledged handlers -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshTwo_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshTwo
        A strategy hwin fallback two own one delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
        A strategy hwin fallback two own one delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshTwo
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedTwo_eq_fixed
      A strategy hwin fallback two own one delivered hrow]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshOne_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshOne
        A strategy hwin fallback one own two delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
        A strategy hwin fallback one own two delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshOne
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedOne_eq_fixed
      A strategy hwin fallback one own two delivered hrow]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputTwo_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputTwo
        A strategy hwin fallback two own one delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo
        A strategy hwin fallback two own one delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputTwo
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedTwo_eq_fixed
      A strategy hwin fallback two own one delivered hrow]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputOne_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputOne
        A strategy hwin fallback one own two delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne
        A strategy hwin fallback one own two delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputOne
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReceivedOne_eq_fixed
      A strategy hwin fallback one own two delivered hrow]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne
        A strategy hwin fallback one own two delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback one own two delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshOne_eq_fixed
      A strategy hwin fallback one own two delivered hrow,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputOne_eq_fixed
      A strategy hwin fallback one own two delivered hrow]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁)
    (hrow :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo
        A strategy hwin fallback two own one delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback two own one delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshTwo_eq_fixed
      A strategy hwin fallback two own one delivered hrow,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOutputTwo_eq_fixed
      A strategy hwin fallback two own one delivered hrow]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowClose_eq_fixed
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂)
    (hleft :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin selectedOne selectedTwo) = .first)
    (hright :
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin selectedOne selectedTwo) = .first) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowClose
        A strategy hwin fallback one own two delivered =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin fallback one own two delivered := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowClose
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshOne_eq_fixed
      A strategy hwin fallback one own two delivered hleft,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowFreshTwo_eq_fixed
      A strategy hwin fallback two delivered one own hright]

/-! ## Reachable semantic-trace equivalence -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt_eq_fixed
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
        A strategy hwin initialTag env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrows :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt
          A strategy hwin initialTag env n
      have hright :
          let fallback :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
              A strategy hwin initialTag
          let pair :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt
              A strategy hwin initialTag env n
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
              A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
                    A strategy hwin fallback.1 pair.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
                    A strategy hwin fallback.2 pair.2)) = .first := by
        simpa only [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedOneAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedTwoAt]
          using hrows.1
      have hleft :
          let fallback :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
              A strategy hwin initialTag
          let pair :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt
              A strategy hwin initialTag env n
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
              A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
                    A strategy hwin fallback.1 pair.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
                    A strategy hwin fallback.2 pair.2)) = .first := by
        simpa only [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedOneAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedTwoAt]
          using hrows.2
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag
      let anchorStep := fun prior : OneControl A strategy hwin ×
          TwoControl A strategy hwin ↦
        match (env n).graph with
        | .right =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                A strategy hwin prior.1 (env n).inputOne).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo
                A strategy hwin fallback prior.2 (env n).inputTwo prior.1
                  (env n).inputOne).1)
        | .left =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne
                A strategy hwin fallback prior.1 (env n).inputOne prior.2
                  (env n).inputTwo).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                A strategy hwin prior.2 (env n).inputTwo).1)
        | .both =>
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowClose
              A strategy hwin fallback prior.1 (env n).inputOne prior.2
                (env n).inputTwo
      let fixedStep := fun prior : OneControl A strategy hwin ×
          TwoControl A strategy hwin ↦
        match (env n).graph with
        | .right =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                A strategy hwin prior.1 (env n).inputOne).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                A strategy hwin fallback prior.2 (env n).inputTwo prior.1
                  (env n).inputOne).1)
        | .left =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                A strategy hwin fallback prior.1 (env n).inputOne prior.2
                  (env n).inputTwo).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                A strategy hwin prior.2 (env n).inputTwo).1)
        | .both =>
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
              A strategy hwin fallback prior.1 (env n).inputOne prior.2
                (env n).inputTwo
      change
        anchorStep
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt
              A strategy hwin initialTag env n) =
          fixedStep
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
              A strategy hwin initialTag env n)
      rw [ih]
      rw [ih] at hleft hright
      cases hgraph : (env n).graph with
      | right =>
          simp only [anchorStep, fixedStep, hgraph]
          rw [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo_eq_fixed
              A strategy hwin _ _ _ _ _ hright]
      | left =>
          simp only [anchorStep, fixedStep, hgraph]
          rw [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne_eq_fixed
              A strategy hwin _ _ _ _ _ hleft]
      | both =>
          simp only [anchorStep, fixedStep, hgraph]
          rw [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowClose_eq_fixed
              A strategy hwin _ _ _ _ _ hleft hright]

/-! ## Reference-output equivalence -/

/-- The output pair named by the anchor-row controller's reference word. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ × Out₂ :=
  let controller :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowController
      A strategy hwin initialTag
  let word :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowTraceInvariant
      A strategy hwin initialTag env).referenceWord controller
  ((word n).outputOne, (word n).outputTwo)

/-- The anchor-row semantic output pair before round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticOutputPairAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ × Out₂ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt
      A strategy hwin initialTag env n
  match (env n).graph with
  | .right =>
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
          A strategy hwin pair.1 (env n).inputOne).2,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo
          A strategy hwin fallback pair.2 (env n).inputTwo pair.1
            (env n).inputOne).2)
  | .left =>
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne
          A strategy hwin fallback pair.1 (env n).inputOne pair.2
            (env n).inputTwo).2,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
          A strategy hwin pair.2 (env n).inputTwo).2)
  | .both =>
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne
          A strategy hwin fallback pair.1 (env n).inputOne pair.2
            (env n).inputTwo).2,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo
          A strategy hwin fallback pair.2 (env n).inputTwo pair.1
            (env n).inputOne).2)

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt_eq_semantic
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticOutputPairAt
        A strategy hwin initialTag env n := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowTraceInvariant,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowMealyTraceInvariant,
    FinitePairedMealyController.LiteralCrossMealyTraceInvariant.toMooreTraceInvariant,
    FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord,
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticOutputPairAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt]
  cases hgraph : (env n).graph <;> rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticOutputPairAt_eq_fixed
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticOutputPairAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt
        A strategy hwin initialTag env n := by
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt_eq_fixed
      A strategy hwin initialTag env n
  have hrows :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt
      A strategy hwin initialTag env n
  have hright :
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt
          A strategy hwin initialTag env n
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
                A strategy hwin fallback.1 pair.1)
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
                A strategy hwin fallback.2 pair.2)) = .first := by
    simpa only [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowRightBaseAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedTwoAt]
      using hrows.1
  have hleft :
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticPairAt
          A strategy hwin initialTag env n
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
                A strategy hwin fallback.1 pair.1)
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
                A strategy hwin fallback.2 pair.2)) = .first := by
    simpa only [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowsFirstAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowLeftBaseAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSelectedTwoAt]
      using hrows.2
  rw [hpair] at hleft hright
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticOutputPairAt
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt
  rw [hpair]
  cases hgraph : (env n).graph with
  | right =>
      simp only [hgraph]
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo_eq_fixed
          A strategy hwin _ _ _ _ _ hright]
  | left =>
      simp only [hgraph]
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne_eq_fixed
          A strategy hwin _ _ _ _ _ hleft]
  | both =>
      simp only [hgraph]
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvOne_eq_fixed
          A strategy hwin _ _ _ _ _ hleft,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowOpenRecvTwo_eq_fixed
          A strategy hwin _ _ _ _ _ hright]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt_eq_fixed
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env n := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt_eq_semantic,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowSemanticOutputPairAt_eq_fixed
      A strategy hwin initialTag env n

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceWord_eq_fixed
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let anchorController :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowController
        A strategy hwin initialTag
    let fixedController :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin initialTag
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowTraceInvariant
        A strategy hwin initialTag env).referenceWord anchorController =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceInvariant
        A strategy hwin initialTag env).referenceWord fixedController := by
  dsimp only
  funext n
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · rfl
  · simpa only [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt,
      RoundRecord.outputPair]
      using
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceOutputAt_eq_fixed
          A strategy hwin initialTag env n

/-- The actual Moore word of the anchor-row controller. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let controller :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowController
      A strategy hwin initialTag
  controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
    controller.globalOutputTwo env

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord_eq_fullRestartWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord
        A strategy hwin initialTag env =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env := by
  unfold
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowTraceWord_eq_referenceWord,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowReferenceWord_eq_fixed
      A strategy hwin initialTag env

/-! ## Accepted repaired words -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord_acceptsFrom_of_exactFirstChild
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env)
    (physicalState : A.State)
    (hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState 0)
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hfirstChild : initialTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) (.strict actual))
    (hfirstGraph : (env 0).graph =
      profiledRawJointStrictGraphOfSide actual.side.other) :
    A.AcceptsFrom physicalState
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord
        A strategy hwin initialTag env) := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord_eq_fullRestartWord]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_acceptsFrom_of_exactFirstChild
      A strategy hwin initialTag env cuts hnoBoth hfirst physicalState hinitial
        control actual hfirstChild hfirstGraph

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord_acceptsFrom_of_exactSecondChild
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env)
    (physicalState : A.State)
    (hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState 0)
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first second : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hsecondSide : second.side = first.side.other)
    (hfirstRoot : ∃ targetRoot : ProfiledRawJointThreadRoot A,
      profiledRawJointHybridCurrentSlots A first.side.other
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
                strategy hwin control) (.strict first)).2.1.1 () =
        some targetRoot)
    (hsecondChild : initialTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
                strategy hwin control) (.strict first))
          (.strict second))
    (hfirstGraph : (env 0).graph =
      profiledRawJointStrictGraphOfSide second.side.other) :
    A.AcceptsFrom physicalState
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord
        A strategy hwin initialTag env) := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAnchorRowWord_eq_fullRestartWord]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_acceptsFrom_of_exactSecondChild
      A strategy hwin initialTag env cuts hnoBoth hfirst physicalState hinitial
        control first second hsecondSide hfirstRoot hsecondChild hfirstGraph

end

end DetParityAutomaton

end DistributedSynthesis
