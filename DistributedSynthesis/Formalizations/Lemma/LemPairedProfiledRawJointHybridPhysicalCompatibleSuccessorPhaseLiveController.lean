/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveFreshPair

/-!
# The finite compatible-successor phase-live controller

This is the executable controller obtained by inserting the paired phase-live
fresh computation into the generic acknowledged exact-closing carrier.  The
ordinary receive selects the open continuation, a simultaneous receive selects
the closed continuation, and blind evolution uses the two member-coherent
phase-live pending steps.

The `PUnit` recurrent summands totalize the finite maps.  The generic
pending-only theorem makes them unreachable from pending initial controls.
No local transition receives a graph, orientation, hierarchy side, leader,
strict-leader bit, history, or view.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev OneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy hwin
    policy

private abbrev TwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy hwin
    policy

private abbrev OnePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending A strategy hwin
    policy

private abbrev TwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending A strategy hwin
    policy

private abbrev OneControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin policy) PUnit PUnit

private abbrev TwoControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin policy) PUnit PUnit

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

/-! ## Total canonical endpoint maps -/

def profiledRawJointHybridPhysicalCompatiblePhaseLiveRecurrentStepOne
    (_ : PUnit) (_ : In₁) : PUnit × Out₁ :=
  (PUnit.unit, default)

def profiledRawJointHybridPhysicalCompatiblePhaseLiveRecurrentStepTwo
    (_ : PUnit) (_ : In₂) : PUnit × Out₂ :=
  (PUnit.unit, default)

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    OneControl A strategy hwin policy → In₁ →
      OneControl A strategy hwin policy × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A strategy
      hwin policy)
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecurrentStepOne

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    TwoControl A strategy hwin policy → In₂ →
      TwoControl A strategy hwin policy × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A strategy
      hwin policy)
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecurrentStepTwo

/-- Totalized process-one fresh data.  The pending/pending branch is the
paired computation; all other branches return the supplied pending fallback. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂) :
    OneShared A strategy hwin policy × PUnit :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      let fresh :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x,
          y, s, max u v x y s, max u v x y s, max u v x y s,
          max u v x y s} A strategy
          hwin policy fallbackLeft fallbackRight onePending twoPending
            (inputOne, inputTwo)
      (fresh.1.1.openControl.2.1, PUnit.unit)
  | _, _ => (initialOne.2.1, PUnit.unit)

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂)
    (one : OneControl A strategy hwin policy) (inputOne : In₁) :
    TwoShared A strategy hwin policy × PUnit :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      let fresh :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x,
          y, s, max u v x y s, max u v x y s, max u v x y s,
          max u v x y s} A strategy
          hwin policy fallbackLeft fallbackRight onePending twoPending
            (inputOne, inputTwo)
      (fresh.1.2.openControl.2.1, PUnit.unit)
  | _, _ => (initialTwo.2.1, PUnit.unit)

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOutputOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂) : Out₁ :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x,
        y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy
        hwin policy fallbackLeft fallbackRight onePending twoPending
          (inputOne, inputTwo)).2.1
  | _, _ => default

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOutputTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂)
    (one : OneControl A strategy hwin policy) (inputOne : In₁) : Out₂ :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x,
        y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy
        hwin policy fallbackLeft fallbackRight onePending twoPending
          (inputOne, inputTwo)).2.2
  | _, _ => default

/-! ## Exact-closing assembly -/

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshOne A strategy hwin
      policy initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOutputOne A strategy hwin
      policy fallbackLeft fallbackRight)

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshTwo A strategy hwin
      policy initialTwo fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOutputTwo A strategy hwin
      policy fallbackLeft fallbackRight)

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveClose
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshOne A strategy hwin
      policy initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshTwo A strategy hwin
      policy initialTwo fallbackLeft fallbackRight)

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveForkLaws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredExactClosingForkLaws
    (.inl initialOne : OneControl A strategy hwin policy)
    (.inl initialTwo : TwoControl A strategy hwin policy)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A strategy
      hwin policy)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep_laws A
      strategy hwin policy)
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecurrentStepOne
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A strategy
      hwin policy)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep_laws A
      strategy hwin policy)
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecurrentStepTwo
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshOne A strategy hwin
      policy initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshTwo A strategy hwin
      policy initialTwo fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOutputOne A strategy hwin
      policy fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOutputTwo A strategy hwin
      policy fallbackLeft fallbackRight)

/-- The actual finite acknowledged Mealy controller. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveController
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl initialOne : OneControl A strategy hwin policy)
    (.inl initialTwo : TwoControl A strategy hwin policy)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A strategy hwin
      policy)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A strategy hwin
      policy)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A strategy
      hwin policy initialOne fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A strategy
      hwin policy initialTwo fallbackLeft fallbackRight)
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveClose A strategy hwin
      policy initialOne initialTwo fallbackLeft fallbackRight)

/-- Moore presentation used by the physical-word endpoints. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalController
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :=
  (profiledRawJointHybridPhysicalCompatiblePhaseLiveController A strategy hwin
    policy initialOne initialTwo fallbackLeft fallbackRight).mooreize

end

end DetParityAutomaton

end DistributedSynthesis
