/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalFreshHandlers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveReceiveOne

/-!
# Canonical exact-close adapter for the retained process-one table

The corrected process-one receive already returns the two meanings required
by the acknowledgement relay: the open meaning retains and advances the live
right receiver, while the closed meaning selects the fresh simultaneous
receiver.  Their shared state and payload are definitionally identical; only
the unresolved member differs.

This file exposes that receive through the generic canonical exact-closing
interface.  The executable maps remain endpoint-local: they receive only
finite local controls and the inputs delivered at the endpoint.
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

/-- The shared value and payload common to the open and closed meanings of
the corrected process-one receive.  Recurrent arguments are unreachable and
are totalized by `fallback`. -/
noncomputable def literalCombinedFreshPhaseLiveFreshOne
    (package : Package A strategy hwin (initial := initial))
    (fallback : OnePending A strategy hwin package)
    (one : OneControl A strategy hwin package) (own : In₁)
    (two : TwoControl A strategy hwin package) (delivered : In₂) :
    OneShared A strategy hwin package × OnePayload A strategy hwin package :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      let fork := package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
        onePending own twoPending delivered
      (fork.1.openControl.2.1, fork.1.openControl.2.2)
  | _, _ => (fallback.2.1, fallback.2.2)

/-- The old-occurrence physical output of the corrected receive. -/
noncomputable def literalCombinedFreshPhaseLiveOutputOne
    (package : Package A strategy hwin (initial := initial))
    (one : OneControl A strategy hwin package) (own : In₁)
    (two : TwoControl A strategy hwin package) (delivered : In₂) : Out₁ :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin onePending
        own twoPending delivered).2
  | _, _ => default

@[simp] theorem literalCombinedFreshPhaseLiveFreshOne_pending
    (package : Package A strategy hwin (initial := initial))
    (fallback one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) (own : In₁)
    (delivered : In₂) :
    package.literalCombinedFreshPhaseLiveFreshOne A strategy hwin fallback
        (.inl one) own (.inl two) delivered =
      ((package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
        two delivered).1.openControl.2.1,
       (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
        two delivered).1.openControl.2.2) :=
  rfl

@[simp] theorem literalCombinedFreshPhaseLiveOutputOne_pending
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) (own : In₁)
    (delivered : In₂) :
    package.literalCombinedFreshPhaseLiveOutputOne A strategy hwin
        (.inl one) own (.inl two) delivered =
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
        two delivered).2 :=
  rfl

/-- The generic open handler is exactly the open meaning computed by the
retained-table receive. -/
@[simp] theorem canonicalDeferredOpenRecvOne_phaseLive_pending
    (package : Package A strategy hwin (initial := initial))
    (fallback one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) (own : In₁)
    (delivered : In₂) :
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
        (package.literalCombinedFreshPhaseLiveFreshOne A strategy hwin
          fallback)
        (package.literalCombinedFreshPhaseLiveOutputOne A strategy hwin)
        (.inl one) own (.inl two) delivered =
      (.inl
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
            own two delivered).1.openControl,
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
          two delivered).2) := by
  rfl

/-- The first component of a simultaneous close is exactly the closed
meaning computed at the same receive. -/
@[simp] theorem canonicalDeferredClose_phaseLive_one_pending
    (package : Package A strategy hwin (initial := initial))
    (fallbackOne one : OnePending A strategy hwin package)
    (freshTwo : TwoControl A strategy hwin package → In₂ →
      OneControl A strategy hwin package → In₁ →
        TwoShared A strategy hwin package × TwoPayload A strategy hwin package)
    (two : TwoPending A strategy hwin package) (own : In₁)
    (delivered : In₂) :
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
        (package.literalCombinedFreshPhaseLiveFreshOne A strategy hwin
          fallbackOne)
        freshTwo (.inl one) own (.inl two) delivered).1 =
      .inl
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
          two delivered).1.closedControl := by
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
