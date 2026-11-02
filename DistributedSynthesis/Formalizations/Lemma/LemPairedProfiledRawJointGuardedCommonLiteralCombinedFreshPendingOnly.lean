/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveOneHandler
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveTwoHandler

/-!
# The literal combined controller stays in shared tables

The concrete combined-fresh receive maps already construct a new exact
heterogeneous table on every receive.  This file presents those constructors
through the generic canonical pending-only interface.  The ordinary branch
stores the `false` member and a simultaneous close stores the `true` member
of the very same new table.  A blind no-receive advances that table.

Consequently the canonical execution never enters an independently selected
ordinary recurrent controller.  The `PUnit` recurrent summand below only
totalizes the finite type; it is unreachable by the proved invariant.

Every executable function takes only finite local controls and the inputs
available at that endpoint.  No graph, orientation, hierarchy side, leader
bit, strict-leader bit, history, or semantic view is an argument.
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

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev OneShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePayload (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy hwin
    package

private abbrev TwoPayload (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy hwin
    package

private abbrev OnePending (package : Package A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package) (OnePayload A strategy hwin package)

private abbrev TwoPending (package : Package A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package) (TwoPayload A strategy hwin package)

private abbrev OneControl (package : Package A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin package) (OnePayload A strategy hwin package)
    Unit

private abbrev TwoControl (package : Package A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin package) (TwoPayload A strategy hwin package)
    Unit

/-! ## Total concrete fresh-table functions -/

/-- Process one's fresh-data function.  On the reachable pending/pending
branch it installs the opposite exact table at the locally reconstructed
fresh key.  The fallback is used only to totalize unreachable recurrent
arguments. -/
noncomputable def literalCombinedFreshPendingOnlyFreshOne
    (package : Package A strategy hwin initial)
    (fallback : OnePending A strategy hwin package)
    (one : OneControl A strategy hwin package) (own : In₁)
    (two : TwoControl A strategy hwin package) (delivered : In₂) :
    OneShared A strategy hwin package × OnePayload A strategy hwin package :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      let fresh := package.literalCombinedFreshOneReceiveFreshness A strategy
        hwin onePending.2.1 own twoPending.2.1 delivered
      let key := package.literalCombinedFreshOneReceiveKey A strategy hwin
        onePending.2.1 own twoPending.2.1 delivered
      (package.literalCrossCombinedFreshOneSharedAt A strategy hwin fresh key,
        none)
  | _, _ => (fallback.2.1, fallback.2.2)

/-- Process-two mirror. -/
noncomputable def literalCombinedFreshPendingOnlyFreshTwo
    (package : Package A strategy hwin initial)
    (fallback : TwoPending A strategy hwin package)
    (two : TwoControl A strategy hwin package) (own : In₂)
    (one : OneControl A strategy hwin package) (delivered : In₁) :
    TwoShared A strategy hwin package × TwoPayload A strategy hwin package :=
  match two, one with
  | .inl twoPending, .inl onePending =>
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin
          twoPending.2.1 own onePending.2.1 delivered,
        none)
  | _, _ => (fallback.2.1, fallback.2.2)

/-- The old-occurrence process-one output used at a receive. -/
noncomputable def literalCombinedFreshPendingOnlyOutputOne
    (package : Package A strategy hwin initial)
    (one : OneControl A strategy hwin package) (own : In₁)
    (two : TwoControl A strategy hwin package) (delivered : In₂) : Out₁ :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      (package.literalCombinedFreshOnePendingRecvFork A strategy hwin Unit
        onePending twoPending own delivered).2
  | _, _ => default

/-- The old-occurrence process-two output used at a receive. -/
noncomputable def literalCombinedFreshPendingOnlyOutputTwo
    (package : Package A strategy hwin initial)
    (two : TwoControl A strategy hwin package) (own : In₂)
    (one : OneControl A strategy hwin package) (delivered : In₁) : Out₂ :=
  match two, one with
  | .inl twoPending, .inl onePending =>
      package.literalCombinedFreshTwoPendingReceiveOutput A strategy hwin
        twoPending.1 twoPending.2.1 own delivered
  | _, _ => default

/-- Unreachable ordinary process-one transition. -/
def literalCombinedFreshPendingOnlyRecurrentStepOne
    (_ : Unit) (_ : In₁) : Unit × Out₁ :=
  ((), default)

/-- Unreachable ordinary process-two transition. -/
def literalCombinedFreshPendingOnlyRecurrentStepTwo
    (_ : Unit) (_ : In₂) : Unit × Out₂ :=
  ((), default)

/-! ## The concrete exact-closing controller -/

noncomputable def literalCombinedFreshPendingOnlyNoRecvOne
    (package : Package A strategy hwin initial) :
    OneControl A strategy hwin package → In₁ →
      OneControl A strategy hwin package × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (package.literalCombinedFreshOnePendingStep A strategy hwin)
    (literalCombinedFreshPendingOnlyRecurrentStepOne (Out₁ := Out₁))

noncomputable def literalCombinedFreshPendingOnlyNoRecvTwo
    (package : Package A strategy hwin initial) :
    TwoControl A strategy hwin package → In₂ →
      TwoControl A strategy hwin package × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (package.literalCombinedFreshTwoPendingStep A strategy hwin)
    (literalCombinedFreshPendingOnlyRecurrentStepTwo (Out₂ := Out₂))

noncomputable def literalCombinedFreshPendingOnlyOpenRecvOne
    (package : Package A strategy hwin initial)
    (fallback : OnePending A strategy hwin package) :
    OneControl A strategy hwin package → In₁ →
      TwoControl A strategy hwin package → In₂ →
        OneControl A strategy hwin package × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (package.literalCombinedFreshPendingOnlyFreshOne A strategy hwin fallback)
    (package.literalCombinedFreshPendingOnlyOutputOne A strategy hwin)

noncomputable def literalCombinedFreshPendingOnlyOpenRecvTwo
    (package : Package A strategy hwin initial)
    (fallback : TwoPending A strategy hwin package) :
    TwoControl A strategy hwin package → In₂ →
      OneControl A strategy hwin package → In₁ →
        TwoControl A strategy hwin package × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (package.literalCombinedFreshPendingOnlyFreshTwo A strategy hwin fallback)
    (package.literalCombinedFreshPendingOnlyOutputTwo A strategy hwin)

noncomputable def literalCombinedFreshPendingOnlyClose
    (package : Package A strategy hwin initial)
    (fallbackOne : OnePending A strategy hwin package)
    (fallbackTwo : TwoPending A strategy hwin package) :
    OneControl A strategy hwin package → In₁ →
      TwoControl A strategy hwin package → In₂ →
        OneControl A strategy hwin package ×
          TwoControl A strategy hwin package :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (package.literalCombinedFreshPendingOnlyFreshOne A strategy hwin
      fallbackOne)
    (package.literalCombinedFreshPendingOnlyFreshTwo A strategy hwin
      fallbackTwo)

/-- The actual finite acknowledged paired controller.  Its endpoint maps are
the concrete shared-table maps above; the generic relay supplies only finite
occurrence acknowledgements. -/
noncomputable def literalCombinedFreshPendingOnlyController
    (package : Package A strategy hwin initial)
    (initialOne : OnePending A strategy hwin package)
    (initialTwo : TwoPending A strategy hwin package) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl initialOne : OneControl A strategy hwin package)
    (.inl initialTwo : TwoControl A strategy hwin package)
    (package.literalCombinedFreshPendingOnlyNoRecvOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyNoRecvTwo A strategy hwin)
    (package.literalCombinedFreshPendingOnlyOpenRecvOne A strategy hwin
      initialOne)
    (package.literalCombinedFreshPendingOnlyOpenRecvTwo A strategy hwin
      initialTwo)
    (package.literalCombinedFreshPendingOnlyClose A strategy hwin initialOne
      initialTwo)

@[simp] theorem literalCombinedFreshPendingOnlyFreshOne_pending
    (package : Package A strategy hwin initial)
    (fallback onePending : OnePending A strategy hwin package)
    (twoPending : TwoPending A strategy hwin package)
    (own : In₁) (delivered : In₂) :
    package.literalCombinedFreshPendingOnlyFreshOne A strategy hwin fallback
        (.inl onePending) own (.inl twoPending) delivered =
      (package.literalCrossCombinedFreshOneSharedAt A strategy hwin
          (package.literalCombinedFreshOneReceiveFreshness A strategy hwin
            onePending.2.1 own twoPending.2.1 delivered)
          (package.literalCombinedFreshOneReceiveKey A strategy hwin
            onePending.2.1 own twoPending.2.1 delivered),
        none) :=
  rfl

@[simp] theorem literalCombinedFreshPendingOnlyFreshTwo_pending
    (package : Package A strategy hwin initial)
    (fallback twoPending : TwoPending A strategy hwin package)
    (onePending : OnePending A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    package.literalCombinedFreshPendingOnlyFreshTwo A strategy hwin fallback
        (.inl twoPending) own (.inl onePending) delivered =
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin
          twoPending.2.1 own onePending.2.1 delivered,
        none) :=
  rfl

/-! ## Pending-only exact-closing package -/

/-- The concrete combined-fresh maps instantiate the generic pending-only
fork laws.  In particular ordinary recurrent controls are absent from every
related execution. -/
noncomputable def literalCombinedFreshPendingOnlyForkLaws
    (package : Package A strategy hwin initial)
    (initialOne : OnePending A strategy hwin package)
    (initialTwo : TwoPending A strategy hwin package) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredPendingExactClosingForkLaws
    (package.literalCombinedFreshOnePendingStep A strategy hwin)
    (literalCombinedFreshPendingOnlyRecurrentStepOne
      (Out₁ := Out₁))
    (package.literalCombinedFreshTwoPendingStep A strategy hwin)
    (literalCombinedFreshPendingOnlyRecurrentStepTwo
      (Out₂ := Out₂))
    (package.literalCombinedFreshPendingOnlyFreshOne A strategy hwin
      initialOne)
    (package.literalCombinedFreshPendingOnlyFreshTwo A strategy hwin
      initialTwo)
    (package.literalCombinedFreshPendingOnlyOutputOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyOutputTwo A strategy hwin)
    initialOne initialTwo
    (package.literalCombinedFreshOnePendingStepLaws A strategy hwin)
    (package.literalCombinedFreshTwoPendingStepLaws A strategy hwin)

/-- Canonical concrete control trace for the table-only construction. -/
noncomputable def literalCombinedFreshPendingOnlyTrace
    (package : Package A strategy hwin initial)
    (initialOne : OnePending A strategy hwin package)
    (initialTwo : TwoPending A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) : Nat →
      OneControl A strategy hwin package ×
        TwoControl A strategy hwin package :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl initialOne) (.inl initialTwo)
    (FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin)
      (literalCombinedFreshPendingOnlyRecurrentStepOne (Out₁ := Out₁)))
    (FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin)
      (literalCombinedFreshPendingOnlyRecurrentStepTwo (Out₂ := Out₂)))
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
      (package.literalCombinedFreshPendingOnlyFreshOne A strategy hwin
        initialOne)
      (package.literalCombinedFreshPendingOnlyOutputOne A strategy hwin))
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
      (package.literalCombinedFreshPendingOnlyFreshTwo A strategy hwin
        initialTwo)
      (package.literalCombinedFreshPendingOnlyOutputTwo A strategy hwin))
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
      (package.literalCombinedFreshPendingOnlyFreshOne A strategy hwin
        initialOne)
      (package.literalCombinedFreshPendingOnlyFreshTwo A strategy hwin
        initialTwo)) env

/-- Every control reached by the concrete canonical trace is still the
pending half of the sum.  Hence every later receive takes the two reduction
lemmas above and installs another shared table. -/
theorem literalCombinedFreshPendingOnlyTrace_pending
    (package : Package A strategy hwin initial)
    (initialOne : OnePending A strategy hwin package)
    (initialTwo : TwoPending A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending
      (package.literalCombinedFreshPendingOnlyTrace A strategy hwin initialOne
        initialTwo env n).1
      (package.literalCombinedFreshPendingOnlyTrace A strategy hwin initialOne
        initialTwo env n).2 := by
  exact
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace_pending
      (package.literalCombinedFreshOnePendingStep A strategy hwin)
      (literalCombinedFreshPendingOnlyRecurrentStepOne (Out₁ := Out₁))
      (package.literalCombinedFreshTwoPendingStep A strategy hwin)
      (literalCombinedFreshPendingOnlyRecurrentStepTwo (Out₂ := Out₂))
      (package.literalCombinedFreshPendingOnlyFreshOne A strategy hwin
        initialOne)
      (package.literalCombinedFreshPendingOnlyFreshTwo A strategy hwin
        initialTwo)
      (package.literalCombinedFreshPendingOnlyOutputOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyOutputTwo A strategy hwin)
      initialOne initialTwo env n

/-- The acknowledged finite controller follows the canonical table-only
trace, including both current physical outputs.  Relay IDs and stale/fresh
acknowledgements are discharged by the generic exact-closing proof; concrete
model work can now reason solely about the canonical shared-table trace. -/
noncomputable def literalCombinedFreshPendingOnlyMealyTraceInvariant
    (package : Package A strategy hwin initial)
    (initialOne : OnePending A strategy hwin package)
    (initialTwo : TwoPending A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) :
    (package.literalCombinedFreshPendingOnlyController A strategy hwin
      initialOne initialTwo).LiteralCrossMealyTraceInvariant env := by
  let initialOne' : OneControl A strategy hwin package := .inl initialOne
  let initialTwo' : TwoControl A strategy hwin package := .inl initialTwo
  let noRecvOne :=
    package.literalCombinedFreshPendingOnlyNoRecvOne A strategy hwin
  let noRecvTwo :=
    package.literalCombinedFreshPendingOnlyNoRecvTwo A strategy hwin
  let openRecvOne :=
    package.literalCombinedFreshPendingOnlyOpenRecvOne A strategy hwin
      initialOne
  let openRecvTwo :=
    package.literalCombinedFreshPendingOnlyOpenRecvTwo A strategy hwin
      initialTwo
  let close := package.literalCombinedFreshPendingOnlyClose A strategy hwin
    initialOne initialTwo
  let Rel : OneControl A strategy hwin package →
      TwoControl A strategy hwin package → Prop :=
    FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending
  let BlindOne : OneControl A strategy hwin package →
      OneControl A strategy hwin package → Prop :=
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind
  let BlindTwo : TwoControl A strategy hwin package →
      TwoControl A strategy hwin package → Prop :=
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind
  let Selected :=
    FiniteAcknowledgedDelayedCarrier.ExactClosingCanonicalSelected initialOne'
      initialTwo' noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let expectedOne :=
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne initialOne'
      initialTwo' noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let expectedTwo :=
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo initialOne'
      initialTwo' noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let blindLaws :=
    (package.literalCombinedFreshPendingOnlyForkLaws A strategy hwin initialOne
      initialTwo).toExactClosingBlindForkLaws
  let traceLaws :=
    FiniteAcknowledgedDelayedCarrier.exactClosingCanonicalSelectedTraceLaws
      initialOne' initialTwo' noRecvOne noRecvTwo openRecvOne openRecvTwo close
      env Rel
  exact
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant
      (initialOne := initialOne') (initialTwo := initialTwo')
      (noRecvOne := noRecvOne) (noRecvTwo := noRecvTwo)
      (openRecvOne := openRecvOne) (openRecvTwo := openRecvTwo)
      (close := close) (Rel := Rel) (BlindOne := BlindOne)
      (BlindTwo := BlindTwo) (Selected := Selected) (env := env)
      (expectedOutputOne := expectedOne) (expectedOutputTwo := expectedTwo)
      blindLaws traceLaws

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
