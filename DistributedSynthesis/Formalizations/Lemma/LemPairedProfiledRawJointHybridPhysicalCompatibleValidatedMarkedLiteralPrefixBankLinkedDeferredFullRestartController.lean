/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFixedTailBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalPhaseBits

/-!
# Sender-and-receiver phase restart for the linked deferred bank

The receiver-only phase restart leaves one seam: on an orientation switch,
the newly blind sender continues the old opposite-phase relay while the
receiver starts the new lane at the delivered provisional child.  Literal
relay equality across those two roots is not available and is not expected.

This module removes that seam locally.  A blind endpoint restarts exactly
when its own `lastRecv` bit is true.  Thus on a left-to-right switch process
one restarts the right sender at its own stored child, while process two
restarts the right receiver at that same child obtained from the delivered
process-one control.  The construction is symmetric.  It does not reveal the
current strict leader: each endpoint sees only whether it receives now and
its own one-bit receive status from the preceding round.
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

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

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

/-! ## Local blind restart -/

/-- Process one is blind on a right-oriented round.  If it received on the
preceding round, that fact locally identifies an orientation switch, so it
rebuilds the right sender at its own stored provisional child.  Otherwise it
continues the retained relay. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
    (state : LinkedOne A strategy hwin) (input : In₁) :
    LinkedOne A strategy hwin :=
  let base : LinkedRelay A strategy hwin :=
    if state.2.1 then
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin (state.child A strategy hwin) false false
    else state.2.2.1
  let next :=
    profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A base.1.1 input
  (next.1,
    (false,
      (((next.2, base.1.2), base.2), state.child A strategy hwin)))

/-- Process-two/left mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
    (state : LinkedTwo A strategy hwin) (input : In₂) :
    LinkedTwo A strategy hwin :=
  let base : LinkedRelay A strategy hwin :=
    if state.2.1 then
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin (state.child A strategy hwin) false false
    else state.2.2.1
  let next :=
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A base.2.1 input
  (next.1,
    (false,
      ((base.1, (next.2, base.2.2)), state.child A strategy hwin)))

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne_child
    (state : LinkedOne A strategy hwin) (input : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
        A strategy hwin state input).child A strategy hwin =
      state.child A strategy hwin := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo_child
    (state : LinkedTwo A strategy hwin) (input : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
        A strategy hwin state input).child A strategy hwin =
      state.child A strategy hwin := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne_lastRecv
    (state : LinkedOne A strategy hwin) (input : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
        A strategy hwin state input).2.1 = false := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo_lastRecv
    (state : LinkedTwo A strategy hwin) (input : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
        A strategy hwin state input).2.1 = false := by
  rfl

/-! ## The switch pair closes definitionally -/

/-- At a left-to-right switch the newly blind process-one sender and the
receiving process-two relay advance the same freshly rebuilt right sender. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightSwitch_sender_eq
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hone : one.2.1 = true) (htwo : two.2.1 = false)
    (input : In₁ × In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
        A strategy hwin one input.1).2.2.1.1.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay
        A strategy hwin one two input).1.1 := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance,
    hone, htwo]

/-! ## Deferred wrappers -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
    (_member : Bool) (shared : LinkedOne A strategy hwin) (input : In₁) :
    LinkedOne A strategy hwin × Out₁ :=
  let next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne
      A strategy hwin shared input
  (next, next.1)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
    (_member : Bool) (shared : LinkedTwo A strategy hwin) (input : In₂) :
    LinkedTwo A strategy hwin × Out₂ :=
  let next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
      A strategy hwin shared input
  (next, next.1)

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
        A strategy hwin) where
  outputEq := by intros; rfl
  stateEq := by intros; rfl

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
        A strategy hwin) where
  outputEq := by intros; rfl
  stateEq := by intros; rfl

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne :
    OneControl A strategy hwin → In₁ → OneControl A strategy hwin × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
      (Out₁ := Out₁))

/-! ## Pending-state fallback irrelevance

The retained tag is used as totalization data only when a semantic control
has escaped to the recurrent summand.  Reachable full-restart controls stay
pending, so all receive and close rows are independent of that fallback tag.
These local equations are the cross-tag splice used after a mixed front
closes at a dynamically reached child. -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_fallback_irrel_pending
    (left right : LinkedOne A strategy hwin)
    (pending : OnePending A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin left (.inl pending) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin right (.inl pending) := by
  rcases pending with ⟨member, shared, payload⟩
  cases member <;> rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_fallback_irrel_pending
    (left right : LinkedTwo A strategy hwin)
    (pending : TwoPending A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin left (.inl pending) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin right (.inl pending) := by
  rcases pending with ⟨member, shared, payload⟩
  cases member <;> rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne_tag_irrel_pending
    (left right : RetainedTag A strategy hwin)
    (one : OnePending A strategy hwin) (inputOne : In₁)
    (two : TwoPending A strategy hwin) (inputTwo : In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin left)
          (.inl one) inputOne (.inl two) inputTwo =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin right)
          (.inl one) inputOne (.inl two) inputTwo := by
  have hone :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_fallback_irrel_pending
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin left).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin right).1 one
  have htwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_fallback_irrel_pending
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin left).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin right).2 two
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne]
  rw [hone, htwo]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo_tag_irrel_pending
    (left right : RetainedTag A strategy hwin)
    (two : TwoPending A strategy hwin) (inputTwo : In₂)
    (one : OnePending A strategy hwin) (inputOne : In₁) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin left)
          (.inl two) inputTwo (.inl one) inputOne =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin right)
          (.inl two) inputTwo (.inl one) inputOne := by
  have hone :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_fallback_irrel_pending
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin left).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin right).1 one
  have htwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_fallback_irrel_pending
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin left).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin right).2 two
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo]
  rw [hone, htwo]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose_tag_irrel_pending
    (left right : RetainedTag A strategy hwin)
    (one : OnePending A strategy hwin) (inputOne : In₁)
    (two : TwoPending A strategy hwin) (inputTwo : In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin left)
          (.inl one) inputOne (.inl two) inputTwo =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin right)
          (.inl one) inputOne (.inl two) inputTwo := by
  have hone :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_fallback_irrel_pending
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin left).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin right).1 one
  have htwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_fallback_irrel_pending
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin left).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin right).2 two
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo]
  rw [hone, htwo]

/-- Process-one acknowledged receive/refork is independent of the fallback
tag whenever every stored interpretation of both relays is pending. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_recvReforkOne_tag_irrel_pending
    (left right : RetainedTag A strategy hwin)
    (one : DistributedSynthesis.FiniteAcknowledgedDelayedCarrier
      (Fin 5) (OneControl A strategy hwin))
    (two : DistributedSynthesis.FiniteAcknowledgedDelayedCarrier
      (Fin 5) (TwoControl A strategy hwin))
    (inputOne : In₁) (inputTwo : In₂)
    (hone : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one)
    (htwo : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two) :
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy
        (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin left))
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin left)))
        one inputOne two inputTwo =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy
        (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin right))
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin right)))
        one inputOne two inputTwo := by
  have honeSelected :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_resolvedControl
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one two hone
  have htwoSelected :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_resolvedControl
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two one htwo
  cases hselectedOne :
      FiniteAcknowledgedDelayedCarrier.resolvedControl one two with
  | inr recurrent =>
      simp [FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending,
        hselectedOne] at honeSelected
  | inl onePending =>
      cases hselectedTwo :
          FiniteAcknowledgedDelayedCarrier.resolvedControl two one with
      | inr recurrent =>
          simp [FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending,
            hselectedTwo] at htwoSelected
      | inl twoPending =>
          simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy,
            hselectedOne, hselectedTwo,
            FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne]
          rw [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne_tag_irrel_pending
              A strategy hwin left right onePending inputOne twoPending
                inputTwo,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose_tag_irrel_pending
              A strategy hwin left right onePending inputOne twoPending
                inputTwo]

/-- Process-two mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_recvReforkTwo_tag_irrel_pending
    (left right : RetainedTag A strategy hwin)
    (two : DistributedSynthesis.FiniteAcknowledgedDelayedCarrier
      (Fin 5) (TwoControl A strategy hwin))
    (one : DistributedSynthesis.FiniteAcknowledgedDelayedCarrier
      (Fin 5) (OneControl A strategy hwin))
    (inputTwo : In₂) (inputOne : In₁)
    (htwo : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two)
    (hone : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one) :
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy
        (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin left))
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin left)))
        two inputTwo one inputOne =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy
        (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin right))
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin right)))
        two inputTwo one inputOne := by
  have htwoSelected :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_resolvedControl
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two one htwo
  have honeSelected :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_resolvedControl
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one two hone
  cases hselectedTwo :
      FiniteAcknowledgedDelayedCarrier.resolvedControl two one with
  | inr recurrent =>
      simp [FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending,
        hselectedTwo] at htwoSelected
  | inl twoPending =>
      cases hselectedOne :
          FiniteAcknowledgedDelayedCarrier.resolvedControl one two with
      | inr recurrent =>
          simp [FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending,
            hselectedOne] at honeSelected
      | inl onePending =>
          simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy,
            hselectedTwo, hselectedOne,
            FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo]
          rw [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo_tag_irrel_pending
              A strategy hwin left right twoPending inputTwo onePending
                inputOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose_tag_irrel_pending
              A strategy hwin left right onePending inputOne twoPending
                inputTwo]

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo :
    TwoControl A strategy hwin → In₂ → TwoControl A strategy hwin × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
      (Out₂ := Out₂))

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv
    (fallback : LinkedOne A strategy hwin)
    (pending : OnePending A strategy hwin) (input : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin (.inl pending) input).1).2.1 = false := by
  rcases pending with ⟨member, shared, payload⟩
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwo_noRecv_lastRecv
    (fallback : LinkedTwo A strategy hwin)
    (pending : TwoPending A strategy hwin) (input : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin (.inl pending) input).1).2.1 = false := by
  rcases pending with ⟨member, shared, payload⟩
  cases member <;> rfl

/-- Right-to-left switch mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftSwitch_sender_eq
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hone : one.2.1 = false) (htwo : two.2.1 = true)
    (input : In₁ × In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo
        A strategy hwin two input.2).2.2.1.2.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay
        A strategy hwin one two input).2.1 := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance,
    hone, htwo]

/-! ## Executable acknowledged controller -/

/-- Canonical retained tag at the marked common root selected by one finite
common-control bank index.  This is the exact root-facing entry used by the
finite front; the anchors are fresh because no local receive has preceded
the entry. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag
    (control : ProfiledRawJointHybridCommonControl A strategy hwin) :
    RetainedTag A strategy hwin :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control,
    (false, false))

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag_state
    (control : ProfiledRawJointHybridCommonControl A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag
      A strategy hwin control).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag_anchors
    (control : ProfiledRawJointHybridCommonControl A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag
      A strategy hwin control).2 = (false, false) :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag_initialPair
    (control : ProfiledRawJointHybridCommonControl A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRootTag
            A strategy hwin control) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
            hwin control) false false :=
  rfl

/-- The existing pending/authority invariant remains sufficient.  Blind
restart changes neither the stored child nor the normalized receive bit. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRelationLaws
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv,
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwo_noRecv_lastRecv,
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

/-- The finite controller whose two local transition kinds use the same
one-bit restart convention. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
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

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
    (initialTag : RetainedTag A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
    A strategy hwin initialTag).mooreize

/-- Proof-side semantic controls of the sender-and-receiver repair. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
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

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_invariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin initialTag env n).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin initialTag env n).2 := by
  dsimp only
  let laws :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRelationLaws
      A strategy hwin initialTag
  induction n with
  | zero => exact laws.initial
  | succ n ih =>
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
      split <;> rename_i hgraph
      · exact laws.strictRight _ _ _ _ ih
      · exact laws.strictLeft _ _ _ _ ih
      · exact laws.both _ _ _ _ ih

/-- The repaired sender transition preserves the exact graph-driven receive
bits.  In particular its local restart test sees `true` exactly on the first
blind round after an opposite receive. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_succ_selected_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hnext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin initialTag env (n + 1) =
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
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
    rfl
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_invariant
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

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_zero_selected_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
        A strategy hwin initialTag env 0
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 initial.1).2.1 = false ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 initial.2).2.1 = false := by
  exact ⟨rfl, rfl⟩

/-! ## Acknowledged implementation and physical readback -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartAuthorityForkLaws
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
        (Out₁ := Out₁))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
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
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRelationLaws
        A strategy hwin initialTag
    pendingOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne_laws
        A strategy hwin
    pendingTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo_laws
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartAuthorityBlindForkLaws
    (initialTag : RetainedTag A strategy hwin) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartAuthorityForkLaws
    A strategy hwin initialTag).toExactClosingBlindForkLaws

/-- The finite acknowledged implementation has exactly the canonical
sender-and-receiver-restarted semantic outputs. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartAuthorityBlindForkLaws
        A strategy hwin initialTag)
      traceLaws

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin initialTag).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyTraceInvariant
    A strategy hwin initialTag env).toMooreTraceInvariant _

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin initialTag
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceInvariant
        A strategy hwin initialTag env).referenceWord controller := by
  dsimp only
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceInvariant
      A strategy hwin initialTag env).globalMachineTraceWord_eq_referenceWord _

/-! ## Controller-free operational-cut adapter -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedOne A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
    A strategy hwin fallback.1
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
        A strategy hwin initialTag env n).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedTwo A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
    A strategy hwin fallback.2
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
        A strategy hwin initialTag env n).2

/-- Exact receive-bit recurrence exposed to the generic maximal-block
arithmetic.  This is a proof-side package, not controller input. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    OperationalReceivePhaseBits (fun n ↦ (env n).graph) where
  one n :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
      A strategy hwin initialTag env n).2.1
  two n :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
      A strategy hwin initialTag env n).2.1
  initial := by
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
      using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_zero_selected_lastRecv
          A strategy hwin initialTag env)
  step n := by
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
      using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_succ_selected_lastRecv
          A strategy hwin initialTag env n)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_right_closing_row_eq_bankOperationalRowAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt
          cuts k := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits
      A strategy hwin initialTag env).right_closing_row_eq_bankOperationalRowAt
        cuts k hgraph

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_left_closing_row_eq_bankOperationalRowAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.bankOperationalRowAt
          cuts k := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartOperationalReceivePhaseBits
      A strategy hwin initialTag env).left_closing_row_eq_bankOperationalRowAt
        cuts k hgraph

end


end DetParityAutomaton

end DistributedSynthesis
