/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlaySchedule

/-!
# The phase-live trace supplies the scheduled live-overlay laws

This file connects the local relational invariant of the finite phase-live
controller to the controller-independent scheduling interface.  The two
initial pending controls and their invariant are explicit inputs: they are
installed by the delayed front handoff, not guessed by a blind endpoint.

The proof-side semantic trace follows the same six local endpoint maps as the
finite acknowledged controller.  At every time its selected controls remain
pending and satisfy the phase-live table invariant.  The generic blind-fork
simulation then identifies the actual Moore trace word with the semantic
output word.  Finally the three graph cases give
`ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws`.

No executable transition receives a graph, orientation, hierarchy side,
leader bit, strict-leader bit, history, or view.
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
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev TwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev OneControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin policy) PUnit.{max u v x y s + 1}
      PUnit.{max u v x y s + 1}

private abbrev TwoControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin policy) PUnit.{max u v x y s + 1}
      PUnit.{max u v x y s + 1}

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

/-! ## Canonical semantic trace -/

/-- The pair of selected semantic controls before physical round `n`. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) : Nat →
      OneControl A strategy hwin policy × TwoControl A strategy hwin policy :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
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
    env

/-- Process-one output of the canonical semantic trace. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ :=
  let prior :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env n
  match (env n).graph with
  | .right =>
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A strategy
        hwin policy prior.1 (env n).inputOne).2
  | .left | .both =>
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A strategy
        hwin policy initialOne fallbackLeft fallbackRight prior.1
          (env n).inputOne prior.2 (env n).inputTwo).2

/-- Process-two output of the canonical semantic trace. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₂ :=
  let prior :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env n
  match (env n).graph with
  | .right | .both =>
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A strategy
        hwin policy initialTwo fallbackLeft fallbackRight prior.2
          (env n).inputTwo prior.1 (env n).inputOne).2
  | .left =>
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A strategy
        hwin policy prior.2 (env n).inputTwo).2

/-! ## Pending selection and invariant preservation -/

/-- A selected semantic pair is pending, phase-live, and is the canonical
pair at time `n`. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalSelected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (one : OneControl A strategy hwin policy)
    (two : TwoControl A strategy hwin policy) (n : Nat) : Prop :=
  ∃ onePending : OnePending A strategy hwin policy,
    ∃ twoPending : TwoPending A strategy hwin policy,
      one = .inl onePending ∧ two = .inl twoPending ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
          strategy hwin policy onePending twoPending ∧
        (one, two) =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n

/-- The three local phase-live preservation theorems lift to the canonical
exact-closing selected-trace interface. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws
      (.inl initialOne : OneControl A strategy hwin policy)
      (.inl initialTwo : TwoControl A strategy hwin policy)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A strategy
        hwin policy)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A strategy
        hwin policy)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A strategy
        hwin policy initialOne fallbackLeft fallbackRight)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A strategy
        hwin policy initialTwo fallbackLeft fallbackRight)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveClose A strategy hwin
        policy initialOne initialTwo fallbackLeft fallbackRight)
      (fun _ _ ↦ True)
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalSelected A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env)
      env
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env) := by
  let noRecvOne :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A strategy hwin
      policy
  let noRecvTwo :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A strategy hwin
      policy
  let openRecvOne :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A strategy
      hwin policy initialOne fallbackLeft fallbackRight
  let openRecvTwo :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A strategy
      hwin policy initialTwo fallbackLeft fallbackRight
  let close :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveClose A strategy hwin
      policy initialOne initialTwo fallbackLeft fallbackRight
  let canonicalLaws :=
    FiniteAcknowledgedDelayedCarrier.exactClosingCanonicalSelectedTraceLaws
      (.inl initialOne : OneControl A strategy hwin policy)
      (.inl initialTwo : TwoControl A strategy hwin policy)
      noRecvOne noRecvTwo openRecvOne openRecvTwo close env (fun _ _ ↦ True)
  refine {
    initial := ?_
    strictRight := ?_
    strictLeft := ?_
    both := ?_ }
  · exact ⟨initialOne, initialTwo, rfl, rfl, hinitial, rfl⟩
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let oneNext : OnePending A strategy hwin policy :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A
          strategy hwin policy) onePending (env n).inputOne).1
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight
          onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let twoNext : TwoPending A strategy hwin policy := fresh.1.2.openControl
    have hnextInvariant := hinvariant.strictRight A strategy hwin fallbackLeft
      fallbackRight ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictRight n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    have hone : (.inl onePending : OneControl A strategy hwin policy) =
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).1 := by
      simpa only [Prod.fst] using congrArg Prod.fst hcanonical
    have htwo : (.inl twoPending : TwoControl A strategy hwin policy) =
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).2 := by
      simpa only [Prod.snd] using congrArg Prod.snd hcanonical
    have houtputs :
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A strategy
            hwin policy (.inl onePending) (env n).inputOne).2 =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n ∧
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A
            strategy hwin policy initialTwo fallbackLeft fallbackRight
              (.inl twoPending) (env n).inputTwo (.inl onePending)
                (env n).inputOne).2 =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n := by
      constructor
      · simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne,
            hgraph] using congrArg
          (fun control ↦
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A
              strategy hwin policy control (env n).inputOne).2) hone
      · simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo,
            hgraph] using congrArg
          (fun controls : OneControl A strategy hwin policy ×
              TwoControl A strategy hwin policy ↦
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A
              strategy hwin policy initialTwo fallbackLeft fallbackRight
                controls.2 (env n).inputTwo controls.1
                  (env n).inputOne).2) hcanonical
    refine ⟨⟨oneNext, twoNext, ?_, ?_, hnextInvariant, hnextCanonical.1⟩,
      houtputs⟩
    · rfl
    · rfl
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight
          onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let oneNext : OnePending A strategy hwin policy := fresh.1.1.openControl
    let twoNext : TwoPending A strategy hwin policy :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A
          strategy hwin policy) twoPending (env n).inputTwo).1
    have hnextInvariant := hinvariant.strictLeft A strategy hwin fallbackLeft
      fallbackRight ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictLeft n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    have hone : (.inl onePending : OneControl A strategy hwin policy) =
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).1 := by
      simpa only [Prod.fst] using congrArg Prod.fst hcanonical
    have htwo : (.inl twoPending : TwoControl A strategy hwin policy) =
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).2 := by
      simpa only [Prod.snd] using congrArg Prod.snd hcanonical
    have houtputs :
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A
            strategy hwin policy initialOne fallbackLeft fallbackRight
              (.inl onePending) (env n).inputOne (.inl twoPending)
                (env n).inputTwo).2 =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n ∧
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A strategy
            hwin policy (.inl twoPending) (env n).inputTwo).2 =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n := by
      constructor
      · simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne,
            hgraph] using congrArg
          (fun controls : OneControl A strategy hwin policy ×
              TwoControl A strategy hwin policy ↦
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A
              strategy hwin policy initialOne fallbackLeft fallbackRight
                controls.1 (env n).inputOne controls.2
                  (env n).inputTwo).2) hcanonical
      · simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo,
            hgraph] using congrArg
          (fun control ↦
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A
              strategy hwin policy control (env n).inputTwo).2) htwo
    refine ⟨⟨oneNext, twoNext, ?_, ?_, hnextInvariant, hnextCanonical.1⟩,
      houtputs⟩
    · rfl
    · rfl
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight
          onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let oneNext : OnePending A strategy hwin policy := fresh.1.1.closedControl
    let twoNext : TwoPending A strategy hwin policy := fresh.1.2.closedControl
    have hnextInvariant := hinvariant.both A strategy hwin fallbackLeft
      fallbackRight ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.both n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    have hcanonicalOne : (.inl onePending : OneControl A strategy hwin policy) =
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).1 := by
      simpa only [Prod.fst] using congrArg Prod.fst hcanonical
    have hcanonicalTwo : (.inl twoPending : TwoControl A strategy hwin policy) =
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).2 := by
      simpa only [Prod.snd] using congrArg Prod.snd hcanonical
    have houtputs :
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A
            strategy hwin policy initialOne fallbackLeft fallbackRight
              (.inl onePending) (env n).inputOne (.inl twoPending)
                (env n).inputTwo).2 =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n ∧
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A
            strategy hwin policy initialTwo fallbackLeft fallbackRight
              (.inl twoPending) (env n).inputTwo (.inl onePending)
                (env n).inputOne).2 =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n := by
      constructor
      · simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne,
            hgraph] using congrArg
          (fun controls : OneControl A strategy hwin policy ×
              TwoControl A strategy hwin policy ↦
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A
              strategy hwin policy initialOne fallbackLeft fallbackRight
                controls.1 (env n).inputOne controls.2
                  (env n).inputTwo).2) hcanonical
      · simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo,
            hgraph] using congrArg
          (fun controls : OneControl A strategy hwin policy ×
              TwoControl A strategy hwin policy ↦
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A
              strategy hwin policy initialTwo fallbackLeft fallbackRight
                controls.2 (env n).inputTwo controls.1
                  (env n).inputOne).2) hcanonical
    refine ⟨⟨oneNext, twoNext, ?_, ?_, hnextInvariant, hnextCanonical.1⟩,
      houtputs⟩
    · rfl
    · rfl

/-! ## Pointwise semantic invariant -/

/-- Every state of the canonical semantic trace is a pending pair satisfying
the phase-live table invariant. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace_selected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalSelected A
      strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight env
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env n).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env n).2 n := by
  intro n
  induction n with
  | zero =>
      exact
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            hinitial env).initial
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only
            [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws
                A strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight hinitial env).strictRight n _ _ trivial ih
                    hgraph |>.1
      | left =>
          simpa only
            [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws
                A strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight hinitial env).strictLeft n _ _ trivial ih
                    hgraph |>.1
      | both =>
          simpa only
            [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws
                A strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight hinitial env).both n _ _ trivial ih hgraph |>.1

/-! ## The actual finite controller follows the semantic trace -/

/-- Mealy-level invariant for the finite phase-live controller. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveMealyTraceInvariant
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveController A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight
      ).LiteralCrossMealyTraceInvariant env := by
  exact
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant
      (initialOne := (.inl initialOne : OneControl A strategy hwin policy))
      (initialTwo := (.inl initialTwo : TwoControl A strategy hwin policy))
      (noRecvOne :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A strategy
          hwin policy)
      (noRecvTwo :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A strategy
          hwin policy)
      (openRecvOne :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A strategy
          hwin policy initialOne fallbackLeft fallbackRight)
      (openRecvTwo :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A strategy
          hwin policy initialTwo fallbackLeft fallbackRight)
      (close :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveClose A strategy hwin
          policy initialOne initialTwo fallbackLeft fallbackRight)
      (Rel := fun _ _ ↦ True)
      (BlindOne := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (BlindTwo := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (Selected :=
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalSelected A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
      (env := env)
      (expectedOutputOne :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
      (expectedOutputTwo :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveForkLaws A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight
        ).toExactClosingBlindForkLaws
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          hinitial env)

/-- Moore-facing invariant for the actual finite physical controller. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveTraceInvariant
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalController A
      strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
      ).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointHybridPhysicalCompatiblePhaseLiveMealyTraceInvariant A
    strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
      hinitial env).toMooreTraceInvariant _

/-- The actual controller word is exactly the semantic reference word. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveTraceWord_eq_referenceWord
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      profiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalController A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveTraceInvariant A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          hinitial env).referenceWord controller := by
  dsimp only
  exact
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveTraceInvariant A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
      ).globalMachineTraceWord_eq_referenceWord _

/-! ## The semantic trace implements the live-overlay interface -/

/-- The physical input pair at round `n`. -/
def profiledRawJointHybridPhysicalCompatiblePhaseLiveInputAt
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : In₁ × In₂ :=
  ((env n).inputOne, (env n).inputTwo)

/-- The output pair prescribed by the two local maps in a strict-right
round.  The definition does not inspect the graph: it merely applies the
no-receive map of process one and the receive map of process two. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ × Out₂ :=
  let prior :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env n
  ((profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A strategy hwin
      policy prior.1 (env n).inputOne).2,
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A strategy
      hwin policy initialTwo fallbackLeft fallbackRight prior.2
        (env n).inputTwo prior.1 (env n).inputOne).2)

/-- Strict-left mirror of
`profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOutput`. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ × Out₂ :=
  let prior :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env n
  ((profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A strategy
      hwin policy initialOne fallbackLeft fallbackRight prior.1
        (env n).inputOne prior.2 (env n).inputTwo).2,
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A strategy hwin
      policy prior.2 (env n).inputTwo).2)

/-- The output pair prescribed when both endpoints receive. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveBothOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Out₁ × Out₂ :=
  let prior :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env n
  ((profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A strategy
      hwin policy initialOne fallbackLeft fallbackRight prior.1
        (env n).inputOne prior.2 (env n).inputTwo).2,
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A strategy
      hwin policy initialTwo fallbackLeft fallbackRight prior.2
        (env n).inputTwo prior.1 (env n).inputOne).2)

/-- The proof-side live predicate at time `n`: the canonical semantic controls
are pending and satisfy the phase-live table invariant.  It contains no
orientation or leader flag. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let prior :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env n
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalSelected A
    strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight env
      prior.1 prior.2 n

/-- The phase-live predicate holds at every physical time. -/
theorem profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveAt A strategy hwin policy
      initialOne initialTwo fallbackLeft fallbackRight env n :=
  profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace_selected A
    strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
      hinitial env n

/-- The semantic reference word satisfies the controller-independent
live-overlay laws.  We use the same proof-side phase-live predicate for both
orientations: orientation is selected by the physical graph, never stored as
knowledge at either endpoint. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveReferenceLiveOverlayLaws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveTraceInvariant A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          hinitial env).referenceWord
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveInputAt env)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOutput A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOutput A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveBothOutput A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env)
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveAt A strategy hwin
        policy initialOne initialTwo fallbackLeft fallbackRight env)
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveAt A strategy hwin
        policy initialOne initialTwo fallbackLeft fallbackRight env) := by
  refine {
    physical_inputs := ?_
    right_same := ?_
    right_switch := ?_
    left_same := ?_
    left_switch := ?_
    both_from_right := ?_
    both_from_left := ?_
    right_output := ?_
    left_output := ?_
    both_output := ?_ }
  · intro n
    rfl
  · intro n _hlive _hgraph
    exact profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
        (n + 1)
  · intro n _hlive _hgraph
    exact profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
        (n + 1)
  · intro n _hlive _hgraph
    exact profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
        (n + 1)
  · intro n _hlive _hgraph
    exact profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
        (n + 1)
  · intro n _hlive _hgraph
    exact ⟨
      profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy hwin
        policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
          (n + 1),
      profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy hwin
        policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
          (n + 1)⟩
  · intro n _hlive _hgraph
    exact ⟨
      profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy hwin
        policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
          (n + 1),
      profiledRawJointHybridPhysicalCompatiblePhaseLiveAt_all A strategy hwin
        policy initialOne initialTwo fallbackLeft fallbackRight hinitial env
          (n + 1)⟩
  · intro n _hlive hgraph
    have hgraph' : (env n).graph = .right := by
      simpa only
        [FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
        using hgraph
    change
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n) = _
    simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOutput, hgraph']
  · intro n _hlive hgraph
    have hgraph' : (env n).graph = .left := by
      simpa only
        [FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
        using hgraph
    change
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n) = _
    simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOutput, hgraph']
  · intro n _hlive hgraph
    have hgraph' : (env n).graph = .both := by
      simpa only
        [FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
        using hgraph
    change
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n) = _
    simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveBothOutput, hgraph']

end

end DetParityAutomaton

end DistributedSynthesis
