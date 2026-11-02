/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyInitial

/-!
# The pending-only semantic trace carries the accepted freshness path

The accepted installed-child code word is indexed by the leader-free
freshness trace.  The physical reference word is indexed by the canonical
exact-closing semantic trace.  This file proves that these are not parallel
proof artefacts: at every time, the two pending controls in the semantic trace
contain exactly the two freshness states in the accepted path.

The statement keeps the pending controls existential.  Their table controls,
member bits, and retained stages may evolve, but their freshness projection is
fixed by the local receive/no-receive maps.  No executable function gains a
graph, hierarchy side, leader bit, history, view, or global selector.
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

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package) Unit

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package) Unit

/-- One physical environment, projected to the two streams used by the
freshness path. -/
def literalCombinedFreshPendingOnlyTraceInputs
    (env : EnvironmentSequence In₁ In₂) : Nat → In₁ × In₂ :=
  fun n ↦ ((env n).inputOne, (env n).inputTwo)

def literalCombinedFreshPendingOnlyTraceGraphs
    (env : EnvironmentSequence In₁ In₂) : Nat → Graph :=
  fun n ↦ (env n).graph

/-- At one time, the canonical semantic controls are pending and their
freshness projections are exactly the accepted leader-free path state. -/
structure LiteralCombinedFreshPendingOnlyTraceFreshnessAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) where
  one : OnePending A strategy hwin package
  two : TwoPending A strategy hwin package
  controls_eq :
    package.literalCombinedFreshPendingOnlyTrace A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
        env n =
      ((.inl one : OneControl A strategy hwin package),
        (.inl two : TwoControl A strategy hwin package))
  freshness_eq :
    (one.2.1.1, two.2.1.1) =
      package.literalCombinedFreshPendingFreshnessTrace A strategy hwin
        (literalCombinedFreshPendingOnlyTraceInputs env)
        (literalCombinedFreshPendingOnlyTraceGraphs env) n

/-- The exact-closing semantic trace and accepted freshness path agree at
every time.  This is a direct induction over the three physical graph cases;
the graph remains proof-side and only selects the already local endpoint
maps. -/
noncomputable def literalCombinedFreshPendingOnlyTrace_freshnessAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n,
    LiteralCombinedFreshPendingOnlyTraceFreshnessAt A strategy hwin package
      env n := by
  intro n
  induction n with
  | zero =>
      exact {
        one := package.literalCombinedFreshPendingOnlyInitialOne A strategy
          hwin
        two := package.literalCombinedFreshPendingOnlyInitialTwo A strategy
          hwin
        controls_eq := rfl
        freshness_eq := rfl }
  | succ n ih =>
      rcases ih with ⟨one, two, hcontrols, hfreshness⟩
      cases hgraph : (env n).graph with
      | right =>
          let oneNext : OnePending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshOnePendingStep A strategy hwin)
              one (env n).inputOne).1
          let twoShared :=
            package.literalCombinedFreshTwoReceiveShared A strategy hwin
              two.2.1 (env n).inputTwo one.2.1 (env n).inputOne
          let twoNext : TwoPending A strategy hwin package :=
            (false, twoShared, none)
          refine ⟨oneNext, twoNext, ?_, ?_⟩
          · unfold literalCombinedFreshPendingOnlyTrace at hcontrols ⊢
            rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hcontrols, hgraph]
            rfl
          · rw [literalCombinedFreshPendingFreshnessTrace_succ,
              ← hfreshness]
            simp [literalCombinedFreshPendingOnlyTraceInputs,
              literalCombinedFreshPendingOnlyTraceGraphs,
              decoratedFreshnessLocalStep, hgraph]
            constructor <;> rfl
      | left =>
          let oneShared :=
            package.literalCrossCombinedFreshOneSharedAt A strategy hwin
              (package.literalCombinedFreshOneReceiveFreshness A strategy
                hwin one.2.1 (env n).inputOne two.2.1 (env n).inputTwo)
              (package.literalCombinedFreshOneReceiveKey A strategy hwin
                one.2.1 (env n).inputOne two.2.1 (env n).inputTwo)
          let oneNext : OnePending A strategy hwin package :=
            (false, oneShared, none)
          let twoNext : TwoPending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshTwoPendingStep A strategy hwin)
              two (env n).inputTwo).1
          refine ⟨oneNext, twoNext, ?_, ?_⟩
          · unfold literalCombinedFreshPendingOnlyTrace at hcontrols ⊢
            rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hcontrols, hgraph]
            rfl
          · rw [literalCombinedFreshPendingFreshnessTrace_succ,
              ← hfreshness]
            simp [literalCombinedFreshPendingOnlyTraceInputs,
              literalCombinedFreshPendingOnlyTraceGraphs,
              decoratedFreshnessLocalStep, hgraph]
            constructor <;> rfl
      | both =>
          let oneShared :=
            package.literalCrossCombinedFreshOneSharedAt A strategy hwin
              (package.literalCombinedFreshOneReceiveFreshness A strategy
                hwin one.2.1 (env n).inputOne two.2.1 (env n).inputTwo)
              (package.literalCombinedFreshOneReceiveKey A strategy hwin
                one.2.1 (env n).inputOne two.2.1 (env n).inputTwo)
          let twoShared :=
            package.literalCombinedFreshTwoReceiveShared A strategy hwin
              two.2.1 (env n).inputTwo one.2.1 (env n).inputOne
          let oneNext : OnePending A strategy hwin package :=
            (true, oneShared, none)
          let twoNext : TwoPending A strategy hwin package :=
            (true, twoShared, none)
          refine ⟨oneNext, twoNext, ?_, ?_⟩
          · unfold literalCombinedFreshPendingOnlyTrace at hcontrols ⊢
            rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hcontrols, hgraph]
            rfl
          · rw [literalCombinedFreshPendingFreshnessTrace_succ,
              ← hfreshness]
            simp [literalCombinedFreshPendingOnlyTraceInputs,
              literalCombinedFreshPendingOnlyTraceGraphs,
              decoratedFreshnessLocalStep, hgraph]
            constructor <;> rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
