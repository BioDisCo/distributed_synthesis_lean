/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalSelectedTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveInvariant

/-!
# Trace induction for the compatible successor phase-live controller

Starting at any pending pair satisfying the relational table invariant, the
canonical exact-closing semantic trace remains pending and satisfies that
invariant forever.  The three induction branches are exactly the unconditional
strict-right, strict-left, and simultaneous theorems from the preceding file.

The initial invariant is deliberately an argument.  The front/recurrent seam
supplies it only after the genuinely delayed acknowledgement installs the
staged phase payload; no direct first-strict activation or leader oracle is
assumed here.
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

set_option pp.universes true in
#check ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending
set_option pp.universes true in
#check ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared
set_option pp.universes true in
#check profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne
set_option pp.universes true in
#check profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne
set_option pp.universes true in
#check profiledRawJointHybridPhysicalCompatiblePhaseLiveClose

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

/-! ## Canonical semantic trace -/

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) :
    Nat → OneControl A strategy hwin policy ×
      TwoControl A strategy hwin policy :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl initialOne) (.inl initialTwo)
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

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₁ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne
    (.inl initialOne) (.inl initialTwo)
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

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo
    (.inl initialOne) (.inl initialTwo)
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

/-- Pending semantic controls at the canonical time, carrying the live table
invariant. -/
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

/-! ## Exact-closing selected trace laws -/

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
  refine { initial := ?_, strictRight := ?_, strictLeft := ?_, both := ?_ }
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
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let twoNext : TwoPending A strategy hwin policy := fresh.1.2.openControl
    have hnext := hinvariant.strictRight A strategy hwin fallbackLeft
      fallbackRight ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictRight n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, rfl, rfl, hnext, hnextCanonical.1⟩,
      hnextCanonical.2⟩
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let oneNext : OnePending A strategy hwin policy := fresh.1.1.openControl
    let twoNext : TwoPending A strategy hwin policy :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A
          strategy hwin policy) twoPending (env n).inputTwo).1
    have hnext := hinvariant.strictLeft A strategy hwin fallbackLeft
      fallbackRight ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictLeft n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, rfl, rfl, hnext, hnextCanonical.1⟩,
      hnextCanonical.2⟩
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hinvariant, hcanonical⟩
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    let oneNext : OnePending A strategy hwin policy := fresh.1.1.closedControl
    let twoNext : TwoPending A strategy hwin policy := fresh.1.2.closedControl
    have hnext := hinvariant.both A strategy hwin fallbackLeft fallbackRight
      ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.both n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, rfl, rfl, hnext, hnextCanonical.1⟩,
      hnextCanonical.2⟩

/-- Pointwise access: every canonical semantic state is pending and satisfies
the relational table invariant. -/
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

end

end DetParityAutomaton

end DistributedSynthesis
