/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailFreshPair

/-!
# The finite acknowledged controller in one delivered-tag tail fibre

This assembles the tag-relative phase-live carrier and fresh constructor into
the generic acknowledged exact-close relay.  Ordinary receives choose the open
continuation, simultaneous receives choose the exact paired closed controls,
and both endpoint outputs are the phase-selected projections of one live table.

The recurrent `PUnit` branches only totalize the finite maps; the generic
pending-only theorem makes them unreachable from pending initial controls.
No local transition takes a graph, orientation, leader bit, history, or view.
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

private abbrev OneShared (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin tag

private abbrev TwoShared (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin tag

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

private abbrev OneControl (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin tag) PUnit PUnit

private abbrev TwoControl (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin tag) PUnit PUnit

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Total endpoint maps -/

def profiledRawJointHybridShadowPhaseLiveTailRecurrentStepOne
    (_ : PUnit) (_ : In₁) : PUnit × Out₁ :=
  (PUnit.unit, default)

def profiledRawJointHybridShadowPhaseLiveTailRecurrentStepTwo
    (_ : PUnit) (_ : In₂) : PUnit × Out₂ :=
  (PUnit.unit, default)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailNoRecvOne
    (tag : Tag A strategy hwin) :
    OneControl A strategy hwin tag → In₁ →
      OneControl A strategy hwin tag × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
      tag)
    profiledRawJointHybridShadowPhaseLiveTailRecurrentStepOne

noncomputable def profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo
    (tag : Tag A strategy hwin) :
    TwoControl A strategy hwin tag → In₂ →
      TwoControl A strategy hwin tag × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
      tag)
    profiledRawJointHybridShadowPhaseLiveTailRecurrentStepTwo

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailNoRecvOne_pending
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (input : In₁) :
    profiledRawJointHybridShadowPhaseLiveTailNoRecvOne A strategy hwin tag
        (.inl one) input =
      let next :=
        profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
          tag one.1 one.2.1 input
      (.inl (one.1, next.1, one.2.2), next.2) := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo_pending
    (tag : Tag A strategy hwin) (two : TwoPending A strategy hwin tag)
    (input : In₂) :
    profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo A strategy hwin tag
        (.inl two) input =
      let next :=
        profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
          tag two.1 two.2.1 input
      (.inl (two.1, next.1, two.2.2), next.2) := by
  rfl

noncomputable def profiledRawJointHybridShadowPhaseLiveTailFreshOne
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OneControl A strategy hwin tag) (inputOne : In₁)
    (two : TwoControl A strategy hwin tag) (inputTwo : In₂) :
    OneShared A strategy hwin tag × PUnit :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      let fresh :=
        profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s} A strategy hwin tag
          fallbackLeft fallbackRight onePending twoPending (inputOne, inputTwo)
      (fresh.1.1.openControl.2.1, PUnit.unit)
  | _, _ => (initialOne.2.1, PUnit.unit)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailFreshTwo
    (tag : Tag A strategy hwin) (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (two : TwoControl A strategy hwin tag) (inputTwo : In₂)
    (one : OneControl A strategy hwin tag) (inputOne : In₁) :
    TwoShared A strategy hwin tag × PUnit :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      let fresh :=
        profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s} A strategy hwin tag
          fallbackLeft fallbackRight onePending twoPending (inputOne, inputTwo)
      (fresh.1.2.openControl.2.1, PUnit.unit)
  | _, _ => (initialTwo.2.1, PUnit.unit)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailOutputOne
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OneControl A strategy hwin tag) (inputOne : In₁)
    (two : TwoControl A strategy hwin tag) (inputTwo : In₂) : Out₁ :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      (profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag
        fallbackLeft fallbackRight onePending twoPending
          (inputOne, inputTwo)).2.1
  | _, _ => default

noncomputable def profiledRawJointHybridShadowPhaseLiveTailOutputTwo
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (two : TwoControl A strategy hwin tag) (inputTwo : In₂)
    (one : OneControl A strategy hwin tag) (inputOne : In₁) : Out₂ :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      (profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag
        fallbackLeft fallbackRight onePending twoPending
          (inputOne, inputTwo)).2.2
  | _, _ => default

/-! The pending/pending equations expose the exact fresh candidates used by
the generic relay.  These are the natural induction interface: a strict round
uses an open control, while a simultaneous receive uses both closed controls. -/

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailFreshOne_pending
    (tag : Tag A strategy hwin) (initialOne one : OnePending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailFreshOne A strategy hwin tag
        initialOne fallbackLeft fallbackRight (.inl one) input.1 (.inl two)
          input.2 =
      let fresh :=
        profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s} A strategy hwin tag
          fallbackLeft fallbackRight one two input
      (fresh.1.1.openControl.2.1, PUnit.unit) := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailFreshTwo_pending
    (tag : Tag A strategy hwin) (initialTwo two : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailFreshTwo A strategy hwin tag
        initialTwo fallbackLeft fallbackRight (.inl two) input.2 (.inl one)
          input.1 =
      let fresh :=
        profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s} A strategy hwin tag
          fallbackLeft fallbackRight one two input
      (fresh.1.2.openControl.2.1, PUnit.unit) := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailOutputOne_pending
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailOutputOne A strategy hwin tag
        fallbackLeft fallbackRight (.inl one) input.1 (.inl two) input.2 =
      (profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag
        fallbackLeft fallbackRight one two input).2.1 := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailOutputTwo_pending
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailOutputTwo A strategy hwin tag
        fallbackLeft fallbackRight (.inl two) input.2 (.inl one) input.1 =
      (profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag
        fallbackLeft fallbackRight one two input).2.2 := by
  rfl

/-! ## Exact-closing assembly -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (profiledRawJointHybridShadowPhaseLiveTailFreshOne A strategy hwin tag
      initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailOutputOne A strategy hwin tag
      fallbackLeft fallbackRight)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo
    (tag : Tag A strategy hwin) (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (profiledRawJointHybridShadowPhaseLiveTailFreshTwo A strategy hwin tag
      initialTwo fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailOutputTwo A strategy hwin tag
      fallbackLeft fallbackRight)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailClose
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (profiledRawJointHybridShadowPhaseLiveTailFreshOne A strategy hwin tag
      initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailFreshTwo A strategy hwin tag
      initialTwo fallbackLeft fallbackRight)

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne_pending
    (tag : Tag A strategy hwin) (initialOne one : OnePending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy hwin tag
        initialOne fallbackLeft fallbackRight (.inl one) input.1 (.inl two)
          input.2 =
      let fresh :=
        profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s} A strategy hwin tag
          fallbackLeft fallbackRight one two input
      (.inl fresh.1.1.openControl, fresh.2.1) := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo_pending
    (tag : Tag A strategy hwin) (initialTwo two : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy hwin tag
        initialTwo fallbackLeft fallbackRight (.inl two) input.2 (.inl one)
          input.1 =
      let fresh :=
        profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s} A strategy hwin tag
          fallbackLeft fallbackRight one two input
      (.inl fresh.1.2.openControl, fresh.2.2) := by
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailClose_pending
    (tag : Tag A strategy hwin)
    (initialOne one : OnePending A strategy hwin tag)
    (initialTwo two : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailClose A strategy hwin tag
        initialOne initialTwo fallbackLeft fallbackRight (.inl one) input.1
          (.inl two) input.2 =
      let fresh :=
        profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s, max u v x y s,
          max u v x y s, max u v x y s} A strategy hwin tag
          fallbackLeft fallbackRight one two input
      (.inl fresh.1.1.closedControl, .inl fresh.1.2.closedControl) := by
  rfl

noncomputable def profiledRawJointHybridShadowPhaseLiveTailForkLaws
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredExactClosingForkLaws
    (.inl initialOne : OneControl A strategy hwin tag)
    (.inl initialTwo : TwoControl A strategy hwin tag)
    (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
      tag)
    (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep_laws A strategy
      hwin tag)
    profiledRawJointHybridShadowPhaseLiveTailRecurrentStepOne
    (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
      tag)
    (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep_laws A strategy
      hwin tag)
    profiledRawJointHybridShadowPhaseLiveTailRecurrentStepTwo
    (profiledRawJointHybridShadowPhaseLiveTailFreshOne A strategy hwin tag
      initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailFreshTwo A strategy hwin tag
      initialTwo fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailOutputOne A strategy hwin tag
      fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailOutputTwo A strategy hwin tag
      fallbackLeft fallbackRight)

/-- The concrete finite paired Mealy controller in one tag fibre. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailController
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl initialOne : OneControl A strategy hwin tag)
    (.inl initialTwo : TwoControl A strategy hwin tag)
    (profiledRawJointHybridShadowPhaseLiveTailNoRecvOne A strategy hwin tag)
    (profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo A strategy hwin tag)
    (profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy hwin tag
      initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy hwin tag
      initialTwo fallbackLeft fallbackRight)
    (profiledRawJointHybridShadowPhaseLiveTailClose A strategy hwin tag
      initialOne initialTwo fallbackLeft fallbackRight)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailPhysicalController
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) :=
  (profiledRawJointHybridShadowPhaseLiveTailController A strategy hwin tag
    initialOne initialTwo fallbackLeft fallbackRight).mooreize

end

end DetParityAutomaton

end DistributedSynthesis
