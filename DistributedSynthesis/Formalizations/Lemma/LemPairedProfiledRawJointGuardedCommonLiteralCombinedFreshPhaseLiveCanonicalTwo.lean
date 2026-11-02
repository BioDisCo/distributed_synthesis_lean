/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveCanonicalOne
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveReceiveTwo

/-!
# Canonical exact-close adapter for both retained live tables

This file supplies the process-two canonical adapter and pairs it with the
process-one adapter.  On reachable pending controls, the ordinary handlers
select the open continuation of the two phase-live receive forks, while the
simultaneous close selects both closed continuations computed from the same
local receives.  Recurrent arguments are totalized by fixed fallbacks.

The resulting endpoint maps and their exact-closing laws are finite and
executable.  They take only local controls and locally available inputs; no
graph, orientation, hierarchy side, leader bit, history, or view is passed to
an endpoint.
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

private abbrev OnePayload (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy hwin
    package

private abbrev TwoPayload (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy hwin
    package

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package) (OnePayload A strategy hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package) (TwoPayload A strategy hwin package)

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin package) (OnePayload A strategy hwin package)
    Unit

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin package) (TwoPayload A strategy hwin package)
    Unit

/-! ## Total process-two adapter -/

/-- Shared value and payload common to the open and closed meanings of the
phase-live process-two receive. -/
noncomputable def literalCombinedFreshPhaseLiveFreshTwo
    (package : Package A strategy hwin (initial := initial))
    (fallback : TwoPending A strategy hwin package)
    (two : TwoControl A strategy hwin package) (own : In₂)
    (one : OneControl A strategy hwin package) (delivered : In₁) :
    TwoShared A strategy hwin package × TwoPayload A strategy hwin package :=
  match two, one with
  | .inl twoPending, .inl onePending =>
      let fork := package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin
        twoPending own onePending delivered
      (fork.1.openControl.2.1, fork.1.openControl.2.2)
  | _, _ => (fallback.2.1, fallback.2.2)

/-- Old-occurrence physical output of the phase-live process-two receive. -/
noncomputable def literalCombinedFreshPhaseLiveOutputTwo
    (package : Package A strategy hwin (initial := initial))
    (two : TwoControl A strategy hwin package) (own : In₂)
    (one : OneControl A strategy hwin package) (delivered : In₁) : Out₂ :=
  match two, one with
  | .inl twoPending, .inl onePending =>
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin twoPending
        own onePending delivered).2
  | _, _ => default

@[simp] theorem literalCombinedFreshPhaseLiveFreshTwo_pending
    (package : Package A strategy hwin (initial := initial))
    (fallback two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package) (own : In₂)
    (delivered : In₁) :
    package.literalCombinedFreshPhaseLiveFreshTwo A strategy hwin fallback
        (.inl two) own (.inl one) delivered =
      ((package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
        one delivered).1.openControl.2.1,
       (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
        one delivered).1.openControl.2.2) :=
  rfl

@[simp] theorem literalCombinedFreshPhaseLiveOutputTwo_pending
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package) (own : In₂)
    (delivered : In₁) :
    package.literalCombinedFreshPhaseLiveOutputTwo A strategy hwin
        (.inl two) own (.inl one) delivered =
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
        one delivered).2 :=
  rfl

/-- The canonical ordinary process-two receive is definitionally the open
phase-live continuation. -/
@[simp] theorem canonicalDeferredOpenRecvTwo_phaseLive_pending
    (package : Package A strategy hwin (initial := initial))
    (fallback two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package) (own : In₂)
    (delivered : In₁) :
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
        (package.literalCombinedFreshPhaseLiveFreshTwo A strategy hwin
          fallback)
        (package.literalCombinedFreshPhaseLiveOutputTwo A strategy hwin)
        (.inl two) own (.inl one) delivered =
      (.inl
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            own one delivered).1.openControl,
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
          one delivered).2) := by
  rfl

/-- The second component of a simultaneous close is definitionally the
closed phase-live process-two continuation. -/
@[simp] theorem canonicalDeferredClose_phaseLive_two_pending
    (package : Package A strategy hwin (initial := initial))
    (fallbackOne : OnePending A strategy hwin package)
    (fallbackTwo two : TwoPending A strategy hwin package)
    (freshOne : OneControl A strategy hwin package → In₁ →
      TwoControl A strategy hwin package → In₂ →
        OneShared A strategy hwin package × OnePayload A strategy hwin package)
    (one : OnePending A strategy hwin package) (own : In₁)
    (delivered : In₂) :
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose freshOne
        (package.literalCombinedFreshPhaseLiveFreshTwo A strategy hwin
          fallbackTwo)
        (.inl one) own (.inl two) delivered).2 =
      .inl
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          delivered one own).1.closedControl := by
  rfl

/-- Both projections of the canonical simultaneous close are precisely the
two closed phase-live continuations from the same old pending pair. -/
@[simp] theorem canonicalDeferredClose_phaseLive_pair_pending
    (package : Package A strategy hwin (initial := initial))
    (fallbackOne one : OnePending A strategy hwin package)
    (fallbackTwo two : TwoPending A strategy hwin package)
    (input : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
        (package.literalCombinedFreshPhaseLiveFreshOne A strategy hwin
          fallbackOne)
        (package.literalCombinedFreshPhaseLiveFreshTwo A strategy hwin
          fallbackTwo)
        (.inl one) input.1 (.inl two) input.2 =
      (.inl
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
            input.1 two input.2).1.closedControl,
        .inl
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            input.2 one input.1).1.closedControl) := by
  rfl

/-! ## Full finite endpoint bundle -/

def literalCombinedFreshPhaseLiveRecurrentStepOne
    (_ : Unit) (_ : In₁) : Unit × Out₁ :=
  ((), default)

def literalCombinedFreshPhaseLiveRecurrentStepTwo
    (_ : Unit) (_ : In₂) : Unit × Out₂ :=
  ((), default)

noncomputable def literalCombinedFreshPhaseLiveNoRecvOne
    (package : Package A strategy hwin (initial := initial)) :
    OneControl A strategy hwin package → In₁ →
      OneControl A strategy hwin package × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (package.literalCombinedFreshOnePendingStep A strategy hwin)
    (literalCombinedFreshPhaseLiveRecurrentStepOne (Out₁ := Out₁))

noncomputable def literalCombinedFreshPhaseLiveNoRecvTwo
    (package : Package A strategy hwin (initial := initial)) :
    TwoControl A strategy hwin package → In₂ →
      TwoControl A strategy hwin package × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (package.literalCombinedFreshTwoPendingStep A strategy hwin)
    (literalCombinedFreshPhaseLiveRecurrentStepTwo (Out₂ := Out₂))

noncomputable def literalCombinedFreshPhaseLiveOpenRecvOne
    (package : Package A strategy hwin (initial := initial))
    (fallback : OnePending A strategy hwin package) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (package.literalCombinedFreshPhaseLiveFreshOne A strategy hwin fallback)
    (package.literalCombinedFreshPhaseLiveOutputOne A strategy hwin)

noncomputable def literalCombinedFreshPhaseLiveOpenRecvTwo
    (package : Package A strategy hwin (initial := initial))
    (fallback : TwoPending A strategy hwin package) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (package.literalCombinedFreshPhaseLiveFreshTwo A strategy hwin fallback)
    (package.literalCombinedFreshPhaseLiveOutputTwo A strategy hwin)

noncomputable def literalCombinedFreshPhaseLiveClose
    (package : Package A strategy hwin (initial := initial))
    (fallbackOne : OnePending A strategy hwin package)
    (fallbackTwo : TwoPending A strategy hwin package) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (package.literalCombinedFreshPhaseLiveFreshOne A strategy hwin
      fallbackOne)
    (package.literalCombinedFreshPhaseLiveFreshTwo A strategy hwin
      fallbackTwo)

/-- All exact-closing fork laws for the corrected executable endpoints follow
from the two member-independent blind steps and the canonical open/closed
re-encapsulation. -/
noncomputable def literalCombinedFreshPhaseLiveForkLaws
    (package : Package A strategy hwin (initial := initial))
    (initialOne : OnePending A strategy hwin package)
    (initialTwo : TwoPending A strategy hwin package) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredExactClosingForkLaws
    (.inl initialOne : OneControl A strategy hwin package)
    (.inl initialTwo : TwoControl A strategy hwin package)
    (package.literalCombinedFreshOnePendingStep A strategy hwin)
    (package.literalCombinedFreshOnePendingStepLaws A strategy hwin)
    (literalCombinedFreshPhaseLiveRecurrentStepOne (Out₁ := Out₁))
    (package.literalCombinedFreshTwoPendingStep A strategy hwin)
    (package.literalCombinedFreshTwoPendingStepLaws A strategy hwin)
    (literalCombinedFreshPhaseLiveRecurrentStepTwo (Out₂ := Out₂))
    (package.literalCombinedFreshPhaseLiveFreshOne A strategy hwin initialOne)
    (package.literalCombinedFreshPhaseLiveFreshTwo A strategy hwin initialTwo)
    (package.literalCombinedFreshPhaseLiveOutputOne A strategy hwin)
    (package.literalCombinedFreshPhaseLiveOutputTwo A strategy hwin)

/-- The finite acknowledged paired controller assembled from the corrected
phase-live endpoints. -/
noncomputable def literalCombinedFreshPhaseLiveController
    (package : Package A strategy hwin (initial := initial))
    (initialOne : OnePending A strategy hwin package)
    (initialTwo : TwoPending A strategy hwin package) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl initialOne : OneControl A strategy hwin package)
    (.inl initialTwo : TwoControl A strategy hwin package)
    (package.literalCombinedFreshPhaseLiveNoRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseLiveOpenRecvOne A strategy hwin
      initialOne)
    (package.literalCombinedFreshPhaseLiveOpenRecvTwo A strategy hwin
      initialTwo)
    (package.literalCombinedFreshPhaseLiveClose A strategy hwin initialOne
      initialTwo)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
