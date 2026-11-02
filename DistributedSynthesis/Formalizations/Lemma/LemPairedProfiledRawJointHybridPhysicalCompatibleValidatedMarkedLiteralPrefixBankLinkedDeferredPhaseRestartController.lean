/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredEpochBaseTrace

/-!
# Phase-restarted linked deferred controller

The original linked receiver always imported the selected old complete relay.
That is correct inside one homogeneous block, but at an orientation reversal
the opposite table is still rooted at the old block base.  This module keeps
the stable controller untouched and tests the minimal local repair:

* if the receiving endpoint received in the preceding round, continue its
  selected relay;
* otherwise rebuild at the delivered partner's stored provisional child and
  consume the current input from that fresh root.

The branch is determined solely by the receiver's local `lastRecv` bit.  The
new root is obtained solely from the delivered finite partner control.  No
transition receives a graph, direction, leader bit, history, or semantic
witness.
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

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev OnePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (LinkedOne A strategy hwin) (Payload A strategy hwin)

private abbrev TwoPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (LinkedTwo A strategy hwin) (Payload A strategy hwin)

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev OldRightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev OldLeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

/-! ## Local retained receives -/

/-- Process one receives on the left-oriented lane, continuing it in the
same phase and restarting it at the delivered child on a switch. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin :=
  let row : PairedEntryRow := .first
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
      A strategy hwin state partner
  let receiver :=
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A base.2.2 own
      delivered
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay
      A strategy hwin state partner (own, delivered)
  let child :=
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
      (receiver.1.target row).1
  (pairedLeftInformedForRow row receiver.1.physical,
    (true, (relay, child)))

/-- Process-two/right mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin :=
  let row : PairedEntryRow := .first
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
      A strategy hwin partner state
  let receiver :=
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A base.1.2 own
      delivered
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay
      A strategy hwin partner state (delivered, own)
  let child :=
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
      (receiver.1.target row).1
  (pairedRightInformedForRow row receiver.1.physical,
    (true, (relay, child)))

/-! ## Deferred wrappers -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one) own
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two) delivered

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two) own
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one) delivered

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin × Payload A strategy hwin :=
  let received :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
      A strategy hwin fallback one own two delivered
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
      A strategy hwin selectedOne selectedTwo
  let closedChild :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin parent (.simultaneous (own, delivered))
  (received,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChildren
      A strategy hwin (received.child A strategy hwin) closedChild)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin × Payload A strategy hwin :=
  let received :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
      A strategy hwin fallback two own one delivered
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
      A strategy hwin selectedOne selectedTwo
  let closedChild :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin parent (.simultaneous (delivered, own))
  (received,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChildren
      A strategy hwin (received.child A strategy hwin) closedChild)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) : Out₁ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
    A strategy hwin fallback one own two delivered).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) : Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
    A strategy hwin fallback two own one delivered).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin fallback)

/-! ## Exact same-phase and switch payloads -/

/-- Continuing a right block computes the exact next payload of the existing
epoch-base occurrence at the frozen `.first` row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo_same_child_eq
    (epochBase : BankControl A strategy hwin)
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁)
    (hsame : state.2.1 = true)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin epochBase state.2.2.1.1.1 state.2.2.1.1.2) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin epochBase
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) .first semanticPast
                  semanticInput)) := by
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hpair.payload_exists A strategy hwin (own, delivered) .first
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false => simp at hsame
  | true =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child,
        ↓reduceIte] using hpayload

/-- Continuing-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne_same_child_eq
    (epochBase : BankControl A strategy hwin)
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂)
    (hsame : state.2.1 = true)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin epochBase state.2.2.1.2.1 state.2.2.1.2.2) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin epochBase
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) .first semanticPast
                  semanticInput)) := by
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hpair.payload_exists A strategy hwin (own, delivered) .first
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false => simp at hsame
  | true =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child,
        ↓reduceIte] using hpayload

/-- At a left-to-right switch, the fresh right table returns an exact child
of the delivered provisional parent. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo_switch_child_eq
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁)
    (hswitch : state.2.1 = false)
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin (partner.child A strategy hwin))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (partner.child A strategy hwin).2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : ((partner.child A strategy hwin).literal A strategy hwin).1 =
      some oldMove) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (partner.child A strategy hwin)
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) .first semanticPast
                  semanticInput)) := by
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_rightPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hroot.payload_exists A strategy hwin (own, delivered) .first
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child,
        Bool.false_eq_true, ↓reduceIte] using hpayload
  | true => simp at hswitch

/-- Right-to-left switch mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne_switch_child_eq
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂)
    (hswitch : state.2.1 = false)
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin (partner.child A strategy hwin))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (partner.child A strategy hwin).2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : ((partner.child A strategy hwin).literal A strategy hwin).2 =
      some oldMove) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (partner.child A strategy hwin)
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) .first semanticPast
                  semanticInput)) := by
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_leftPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hroot.payload_exists A strategy hwin (own, delivered) .first
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child,
        Bool.false_eq_true, ↓reduceIte] using hpayload
  | true => simp at hswitch

/-! ## Closed candidates -/

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne_open_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin fallback one own two delivered).2.tag A strategy hwin
        false).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
        A strategy hwin fallback one own two delivered).child A strategy
          hwin :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo_open_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin fallback two own one delivered).2.tag A strategy hwin
        false).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
        A strategy hwin fallback two own one delivered).child A strategy
          hwin :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne_closed_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin fallback one own two delivered).2.tag A strategy hwin
        true).1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two))
        (.simultaneous (own, delivered)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo_closed_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
      A strategy hwin fallback two own one delivered).2.tag A strategy hwin
        true).1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two))
        (.simultaneous (delivered, own)) :=
  rfl

/-- The phase restart changes only the open receive base.  The two closed
candidate children still agree under the established authority invariant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFresh_closed_children_eq
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hparents :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
        A strategy hwin fallback one two) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin fallback one inputOne two inputTwo).2.tag A strategy
        hwin true).1) =
      (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
        A strategy hwin fallback two inputTwo one inputOne).2.tag A strategy
          hwin true).1) := by
  unfold
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
    at hparents
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne_closed_child,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo_closed_child,
    hparents]

/-! ## Three-case invariant and executable controller -/

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOne_openRecv_lastRecv
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback one inputOne two inputTwo).1).2.1 = true :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwo_openRecv_lastRecv
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (one : OneControl A strategy hwin) (inputOne : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback two inputTwo one inputOne).1).2.1 = true :=
  rfl

/-- The dangerous-pair relation is unaffected by the phase restart.  Strict
rounds leave unequal receive flags; BOTH uses the still-equal simultaneous
closed payloads. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRelationLaws
    (initialTag : RetainedTag A strategy hwin) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelationLaws
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
          A strategy hwin initialTag) : OneControl A strategy hwin)
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
          A strategy hwin initialTag) : TwoControl A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin fallback)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
        A strategy hwin fallback) := by
  dsimp only
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  refine {
    initial := ?_
    strictRight := ?_
    strictLeft := ?_
    both := ?_ }
  · refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro _hflags
    rfl
  · intro one inputOne two inputTwo hrel
    rcases hrel with ⟨hpending, _hauthority⟩
    cases one with
    | inr recurrent => exact False.elim hpending.1
    | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        intro hflags
        have : False := by
          simpa only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_noRecv_lastRecv,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwo_openRecv_lastRecv,
            Bool.false_eq_true] using hflags
        exact this.elim
  · intro one inputOne two inputTwo hrel
    rcases hrel with ⟨hpending, _hauthority⟩
    cases one with
    | inr recurrent => exact False.elim hpending.1
    | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        intro hflags
        have : False := by
          simpa only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOne_openRecv_lastRecv,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_noRecv_lastRecv,
            Bool.true_eq_false] using hflags
        exact this.elim
  · intro one inputOne two inputTwo hrel
    rcases hrel with ⟨hpending, hauthority⟩
    cases one with
    | inr recurrent => exact False.elim hpending.1
    | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        intro _hflags
        exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFresh_closed_children_eq
            A strategy hwin fallback (.inl onePending) inputOne
              (.inl twoPending) inputTwo
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
                A strategy hwin fallback (.inl onePending) (.inl twoPending)
                  hauthority)

/-- The finite acknowledged controller with only its receive base selector
replaced.  Its control types, initialization, and blind transitions are the
same as in the stable linked-deferred controller. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartMealyController
    (initialTag : RetainedTag A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartController
    (initialTag : RetainedTag A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartMealyController
    A strategy hwin initialTag).mooreize

/-- Canonical proof-side semantic controls of the repaired controller. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
      A strategy hwin fallback) env n

/-- All three graph cases preserve pendingness and exact child authority for
the repaired semantic trace. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
          A strategy hwin initialTag env n).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
          A strategy hwin initialTag env n).2 := by
  dsimp only
  let laws :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRelationLaws
      A strategy hwin initialTag
  induction n with
  | zero => exact laws.initial
  | succ n ih =>
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
      split <;> rename_i hgraph
      · exact laws.strictRight _ _ _ _ ih
      · exact laws.strictLeft _ _ _ _ ih
      · exact laws.both _ _ _ _ ih

/-- Exact receive-phase bits after each repaired semantic step.  These are
the local facts which distinguish the first round of a block (`false`) from
later rounds of the same block (`true`). -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_succ_selected_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
        A strategy hwin initialTag env (n + 1)
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
      A strategy hwin initialTag
  let current :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hnext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
          A strategy hwin initialTag env (n + 1) =
        match (env n).graph with
        | .right =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
                A strategy hwin current.1 (env n).inputOne).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                A strategy hwin fallback current.2 (env n).inputTwo current.1
                  (env n).inputOne).1)
        | .left =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                A strategy hwin fallback current.1 (env n).inputOne current.2
                  (env n).inputTwo).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
                A strategy hwin current.2 (env n).inputTwo).1)
        | .both =>
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
              A strategy hwin fallback current.1 (env n).inputOne current.2
                (env n).inputTwo := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
    rfl
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_noRecv_lastRecv
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_noRecv_lastRecv
              A strategy hwin fallback.2 twoPending (env n).inputTwo⟩
      | both =>
          rw [hnext, hgraph, hone, htwo]
          exact ⟨rfl, rfl⟩

/-- Both selected phase bits are initially false. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_zero_selected_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
        A strategy hwin initialTag env 0
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 initial.1).2.1 = false ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 initial.2).2.1 = false := by
  exact ⟨rfl, rfl⟩

/-! ## Acknowledged trace and reference word -/

/-- Canonical fresh re-encapsulation plus the repaired authority relation. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAuthorityForkLaws
    (initialTag : RetainedTag A strategy hwin) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    FiniteAcknowledgedDelayedCarrier.DeferredExactClosingForkLaws
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
          A strategy hwin initialTag) : OneControl A strategy hwin)
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
          A strategy hwin initialTag) : TwoControl A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
        (Out₁ := Out₁))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
        (Out₂ := Out₂))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin fallback)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
        A strategy hwin fallback) := by
  dsimp only
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  exact {
    relation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRelationLaws
        A strategy hwin initialTag
    pendingOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne_laws
        A strategy hwin
    pendingTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo_laws
        A strategy hwin
    receive := {
      one := by
        intro one inputOne two inputTwo _hrel
        exact ⟨
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
            A strategy hwin fallback one inputOne two inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
            A strategy hwin fallback one inputOne two inputTwo).2,
          rfl, rfl⟩
      two := by
        intro one inputOne two inputTwo _hrel
        exact ⟨
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
            A strategy hwin fallback two inputTwo one inputOne).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
            A strategy hwin fallback two inputTwo one inputOne).2,
          rfl, rfl⟩ } }

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAuthorityBlindForkLaws
    (initialTag : RetainedTag A strategy hwin) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAuthorityForkLaws
    A strategy hwin initialTag).toExactClosingBlindForkLaws

/-- The acknowledged implementation has exactly the canonical repaired
semantic outputs. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartMealyTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartMealyController
      A strategy hwin initialTag).LiteralCrossMealyTraceInvariant env := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let initialOne : OneControl A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag)
  let initialTwo : TwoControl A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag)
  let noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
      A strategy hwin
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
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
  let Rel : OneControl A strategy hwin → TwoControl A strategy hwin → Prop :=
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
  exact
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant
      (initialOne := initialOne) (initialTwo := initialTwo)
      (noRecvOne := noRecvOne) (noRecvTwo := noRecvTwo)
      (openRecvOne := openRecvOne) (openRecvTwo := openRecvTwo)
      (close := close) (Rel := Rel)
      (BlindOne := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (BlindTwo := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (Selected := Selected) (env := env)
      (expectedOutputOne := expectedOne) (expectedOutputTwo := expectedTwo)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartAuthorityBlindForkLaws
        A strategy hwin initialTag)
      traceLaws

/-- Moore-facing repaired trace invariant. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartController
      A strategy hwin initialTag).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartMealyTraceInvariant
    A strategy hwin initialTag env).toMooreTraceInvariant _

/-- Physical repaired trace word equals its canonical semantic reference. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartTraceWord_eq_referenceWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartController
        A strategy hwin initialTag
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartTraceInvariant
        A strategy hwin initialTag env).referenceWord controller := by
  dsimp only
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartTraceInvariant
      A strategy hwin initialTag env).globalMachineTraceWord_eq_referenceWord _

end


end DetParityAutomaton

end DistributedSynthesis
