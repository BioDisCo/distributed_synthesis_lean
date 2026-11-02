/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedRowCoupledInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedTrace

/-!
# Canonical Tail trace with the row-aware invariant

Given the single model-specific `RowConstructorClosure` socket, the existing
canonical semantic trace carries `TrackedInvariant ∧ RowSwitchCoupled` at
every time.  This is an induction-only adapter; it deliberately makes no
claim about the old Tail controller's hard-coded `.both` output functions.
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

/-- The canonical semantic control pair at time `n`, strengthened with the
row-aware cross invariant. -/
def ProfiledRawJointHybridShadowPhaseLiveTailCanonicalTrackedRowCoupled
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
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy
            hwin tag fallbackLeft fallbackRight onePending twoPending ∧
          (one, two) =
            profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy
              hwin tag initialOne initialTwo fallbackLeft fallbackRight env n

/-- The strengthened selected-trace laws.  All semantic work is concentrated
in `closure`; the remaining proof is the generic three-letter induction. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupledSelectedTraceLaws
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight initialOne initialTwo)
    (closure :
      ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure A strategy
        hwin tag fallbackLeft fallbackRight)
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
      (ProfiledRawJointHybridShadowPhaseLiveTailCanonicalTrackedRowCoupled A
        strategy hwin tag initialOne initialTwo fallbackLeft fallbackRight env)
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
      ⟨onePending, twoPending, rfl, rfl, hcurrent, hcanonical⟩
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    have hnext :
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy
          hwin tag fallbackLeft fallbackRight next.1 next.2 :=
      hcurrent.strictRight_of_closure A strategy hwin closure
        ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictRight n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨next.1, next.2, rfl, rfl, hnext, ?_⟩, hnextCanonical.2⟩
    simpa [next,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext] using
        hnextCanonical.1
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hcurrent, hcanonical⟩
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    have hnext :
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy
          hwin tag fallbackLeft fallbackRight next.1 next.2 :=
      hcurrent.strictLeft_of_closure A strategy hwin closure
        ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictLeft n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨next.1, next.2, rfl, rfl, hnext, ?_⟩, hnextCanonical.2⟩
    simpa [next,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext] using
        hnextCanonical.1
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hcurrent, hcanonical⟩
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin tag
        fallbackLeft fallbackRight onePending twoPending
          ((env n).inputOne, (env n).inputTwo)
    have hnext :
        ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy
          hwin tag fallbackLeft fallbackRight next.1 next.2 :=
      hcurrent.both_of_closure A strategy hwin closure
        ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.both n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨next.1, next.2, rfl, rfl, hnext, ?_⟩, hnextCanonical.2⟩
    simpa [next,
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext] using
        hnextCanonical.1

/-- Pointwise strengthened invariant on the concrete semantic trace. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailSemanticTrace_trackedRowCoupled
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight initialOne initialTwo)
    (closure :
      ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure A strategy
        hwin tag fallbackLeft fallbackRight)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    ProfiledRawJointHybridShadowPhaseLiveTailCanonicalTrackedRowCoupled A
      strategy hwin tag initialOne initialTwo fallbackLeft fallbackRight env
      (profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy hwin tag
        initialOne initialTwo fallbackLeft fallbackRight env n).1
      (profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy hwin tag
        initialOne initialTwo fallbackLeft fallbackRight env n).2 n := by
  intro n
  induction n with
  | zero =>
      exact
        (profiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupledSelectedTraceLaws
          A strategy hwin tag initialOne initialTwo fallbackLeft fallbackRight
            hinitial closure env).initial
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only
            [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupledSelectedTraceLaws
                A strategy hwin tag initialOne initialTwo fallbackLeft
                  fallbackRight hinitial closure env).strictRight n _ _ trivial
                    ih hgraph |>.1
      | left =>
          simpa only
            [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupledSelectedTraceLaws
                A strategy hwin tag initialOne initialTwo fallbackLeft
                  fallbackRight hinitial closure env).strictLeft n _ _ trivial
                    ih hgraph |>.1
      | both =>
          simpa only
            [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            using
              (profiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupledSelectedTraceLaws
                A strategy hwin tag initialOne initialTwo fallbackLeft
                  fallbackRight hinitial closure env).both n _ _ trivial ih
                    hgraph |>.1

end

end DetParityAutomaton

end DistributedSynthesis
