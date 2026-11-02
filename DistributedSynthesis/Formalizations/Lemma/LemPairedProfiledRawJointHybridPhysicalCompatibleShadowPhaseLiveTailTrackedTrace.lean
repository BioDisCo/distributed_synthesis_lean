/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalSelectedTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailController

/-!
# The actual finite tail-controller trace is pending and tracked

This is the operational induction for one delivered-tag recurrent tail.  It
uses the exact controller maps, so its three branches coincide with the three
physical graph letters.  The proof-only tracked invariant supplies successor
keys; the executable local states remain exactly those of `TailController`.
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
    (OneShared A strategy hwin tag) PUnit PUnit.{1}

private abbrev TwoControl (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin tag) PUnit PUnit.{1}

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Canonical semantic trace of the concrete controller maps -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTailSemanticTrace
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (env : EnvironmentSequence In₁ In₂) :
    Nat → OneControl A strategy hwin tag × TwoControl A strategy hwin tag :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
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
    env

noncomputable def profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₁ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne
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
    env

noncomputable def profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo
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
    env

/-- At time `n`, the exact semantic trace is represented by pending controls
whose phase-selected table is semantically tracked. -/
def ProfiledRawJointHybridShadowPhaseLiveTailCanonicalTracked
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (env : EnvironmentSequence In₁ In₂)
    (one : OneControl A strategy hwin tag)
    (two : TwoControl A strategy hwin tag) (n : Nat) : Prop :=
  ∃ onePending : OnePending A strategy hwin tag,
    ∃ twoPending : TwoPending A strategy hwin tag,
      one = .inl onePending ∧ two = .inl twoPending ∧
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy
            hwin tag onePending twoPending ∧
          (one, two) =
            profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy
              hwin tag initialOne initialTwo fallbackLeft fallbackRight env n

/-! ## The three exact controller transitions preserve tracking -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailTrackedSelectedTraceLaws
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws
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
      (fun _ _ ↦ True)
      (ProfiledRawJointHybridShadowPhaseLiveTailCanonicalTracked A strategy hwin
        tag initialOne initialTwo fallbackLeft fallbackRight env)
      env
      (profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne A strategy
        hwin tag initialOne initialTwo fallbackLeft fallbackRight env)
      (profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo A strategy
        hwin tag initialOne initialTwo fallbackLeft fallbackRight env) := by
  let noRecvOne :=
    profiledRawJointHybridShadowPhaseLiveTailNoRecvOne A strategy hwin tag
  let noRecvTwo :=
    profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo A strategy hwin tag
  let openRecvOne :=
    profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy hwin tag
      initialOne fallbackLeft fallbackRight
  let openRecvTwo :=
    profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy hwin tag
      initialTwo fallbackLeft fallbackRight
  let close :=
    profiledRawJointHybridShadowPhaseLiveTailClose A strategy hwin tag
      initialOne initialTwo fallbackLeft fallbackRight
  let canonicalLaws :=
    FiniteAcknowledgedDelayedCarrier.exactClosingCanonicalSelectedTraceLaws
      (.inl initialOne : OneControl A strategy hwin tag)
      (.inl initialTwo : TwoControl A strategy hwin tag)
      noRecvOne noRecvTwo openRecvOne openRecvTwo close env (fun _ _ ↦ True)
  refine { initial := ?_, strictRight := ?_, strictLeft := ?_, both := ?_ }
  · exact ⟨initialOne, initialTwo, rfl, rfl, hinitial, rfl⟩
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let oneNext : OnePending A strategy hwin tag :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
          tag) onePending (env n).inputOne).1
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag
        fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let twoNext : TwoPending A strategy hwin tag := fresh.1.2.openControl
    have hnext :
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy
          hwin tag oneNext twoNext :=
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.strictRight.{u,
        v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin hinvariant
          fallbackLeft fallbackRight ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictRight n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, rfl, rfl, hnext, hnextCanonical.1⟩,
      hnextCanonical.2⟩
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag
        fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let oneNext : OnePending A strategy hwin tag := fresh.1.1.openControl
    let twoNext : TwoPending A strategy hwin tag :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
          tag) twoPending (env n).inputTwo).1
    have hnext :
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy
          hwin tag oneNext twoNext :=
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.strictLeft.{u,
        v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin hinvariant
          fallbackLeft fallbackRight ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictLeft n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, rfl, rfl, hnext, hnextCanonical.1⟩,
      hnextCanonical.2⟩
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag
        fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let oneNext : OnePending A strategy hwin tag := fresh.1.1.closedControl
    let twoNext : TwoPending A strategy hwin tag := fresh.1.2.closedControl
    have hnext :
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy
          hwin tag oneNext twoNext :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_trackedInvariant.{u,
        v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag fallbackLeft
          fallbackRight onePending twoPending
            ((env n).inputOne, (env n).inputTwo) hinvariant
    have hnextCanonical := canonicalLaws.both n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, rfl, rfl, hnext, hnextCanonical.1⟩,
      hnextCanonical.2⟩

/-- Pointwise operational trace invariant. -/
theorem profiledRawJointHybridShadowPhaseLiveTailSemanticTrace_tracked
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    ProfiledRawJointHybridShadowPhaseLiveTailCanonicalTracked A strategy hwin
      tag initialOne initialTwo fallbackLeft fallbackRight env
      (profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy hwin tag
        initialOne initialTwo fallbackLeft fallbackRight env n).1
      (profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy hwin tag
        initialOne initialTwo fallbackLeft fallbackRight env n).2 n := by
  intro n
  induction n with
  | zero =>
      exact
        (profiledRawJointHybridShadowPhaseLiveTailTrackedSelectedTraceLaws A
          strategy hwin tag initialOne initialTwo fallbackLeft fallbackRight
            hinitial env).initial
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only
            [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridShadowPhaseLiveTailTrackedSelectedTraceLaws
                A strategy hwin tag initialOne initialTwo fallbackLeft
                  fallbackRight hinitial env).strictRight n _ _ trivial ih
                    hgraph |>.1
      | left =>
          simpa only
            [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridShadowPhaseLiveTailTrackedSelectedTraceLaws
                A strategy hwin tag initialOne initialTwo fallbackLeft
                  fallbackRight hinitial env).strictLeft n _ _ trivial ih
                    hgraph |>.1
      | both =>
          simpa only
            [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridShadowPhaseLiveTailTrackedSelectedTraceLaws
                A strategy hwin tag initialOne initialTwo fallbackLeft
                  fallbackRight hinitial env).both n _ _ trivial ih hgraph |>.1

/-! ## The actual finite controller follows the tracked semantic trace -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailMealyTraceInvariant
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailController A strategy hwin tag
      initialOne initialTwo fallbackLeft fallbackRight
      ).LiteralCrossMealyTraceInvariant env := by
  exact
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant
      (initialOne := (.inl initialOne : OneControl A strategy hwin tag))
      (initialTwo := (.inl initialTwo : TwoControl A strategy hwin tag))
      (noRecvOne :=
        profiledRawJointHybridShadowPhaseLiveTailNoRecvOne A strategy hwin tag)
      (noRecvTwo :=
        profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo A strategy hwin tag)
      (openRecvOne :=
        profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy hwin tag
          initialOne fallbackLeft fallbackRight)
      (openRecvTwo :=
        profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy hwin tag
          initialTwo fallbackLeft fallbackRight)
      (close :=
        profiledRawJointHybridShadowPhaseLiveTailClose A strategy hwin tag
          initialOne initialTwo fallbackLeft fallbackRight)
      (Rel := fun _ _ ↦ True)
      (BlindOne := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (BlindTwo := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (Selected :=
        ProfiledRawJointHybridShadowPhaseLiveTailCanonicalTracked A strategy hwin
          tag initialOne initialTwo fallbackLeft fallbackRight env)
      (env := env)
      (expectedOutputOne :=
        profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env)
      (expectedOutputTwo :=
        profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env)
      (profiledRawJointHybridShadowPhaseLiveTailForkLaws A strategy hwin tag
        initialOne initialTwo fallbackLeft fallbackRight
        ).toExactClosingBlindForkLaws
      (profiledRawJointHybridShadowPhaseLiveTailTrackedSelectedTraceLaws A
        strategy hwin tag initialOne initialTwo fallbackLeft fallbackRight
          hinitial env)

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailTraceInvariant
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailPhysicalController A strategy hwin
      tag initialOne initialTwo fallbackLeft fallbackRight
      ).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointHybridShadowPhaseLiveTailMealyTraceInvariant A strategy hwin
    tag initialOne initialTwo fallbackLeft fallbackRight hinitial env
    ).toMooreTraceInvariant _

theorem profiledRawJointHybridShadowPhaseLiveTailTraceWord_eq_referenceWord
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      profiledRawJointHybridShadowPhaseLiveTailPhysicalController A strategy
        hwin tag initialOne initialTwo fallbackLeft fallbackRight
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointHybridShadowPhaseLiveTailTraceInvariant A strategy hwin
        tag initialOne initialTwo fallbackLeft fallbackRight hinitial env
        ).referenceWord controller := by
  dsimp only
  exact
    (profiledRawJointHybridShadowPhaseLiveTailTraceInvariant A strategy hwin tag
      initialOne initialTwo fallbackLeft fallbackRight hinitial env
      ).globalMachineTraceWord_eq_referenceWord _

end

end DetParityAutomaton

end DistributedSynthesis
