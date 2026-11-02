/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveTraceInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyPolicyAcceptance

/-!
# The phase-live trace carries the accepted freshness lineage

The branch-aware table carrier changes retained table and stage controls, but
does not change the leader-free freshness product.  This file identifies the
freshness projection of its actual semantic trace with the already proved
accepted decorated-policy path.

This is the entry point for the priority-only hard-regime route.  It avoids
the invalid stronger demand that every rationalized heterogeneous-table
record equal the corresponding record of an independently chosen ordinary
policy.  Only the accepted child-code lineage is retained here.
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

/-- Physical inputs used by the common decorated-policy path. -/
def literalCombinedFreshPhaseLiveTraceInputs
    (env : EnvironmentSequence In₁ In₂) : Nat → In₁ × In₂ :=
  fun n ↦ ((env n).inputOne, (env n).inputTwo)

/-- Proof-side graph word selecting the already local freshness maps. -/
def literalCombinedFreshPhaseLiveTraceGraphs
    (env : EnvironmentSequence In₁ In₂) : Nat → Graph :=
  fun n ↦ (env n).graph

/-- At time `n`, the actual phase-live semantic controls are pending and
contain exactly the accepted leader-free freshness state. -/
structure LiteralCombinedFreshPhaseLiveTraceFreshnessAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) where
  one : OnePending A strategy hwin package
  two : TwoPending A strategy hwin package
  controls_eq :
    package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin env
        n =
      ((.inl one : OneControl A strategy hwin package),
        (.inl two : TwoControl A strategy hwin package))
  freshness_eq :
    (one.2.1.1, two.2.1.1) =
      package.literalCombinedFreshPendingFreshnessTrace A strategy hwin
        (literalCombinedFreshPhaseLiveTraceInputs env)
        (literalCombinedFreshPhaseLiveTraceGraphs env) n

/-- Retaining live table controls is invisible to the freshness product. -/
noncomputable def literalCombinedFreshPhaseLiveTrace_freshnessAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n,
    LiteralCombinedFreshPhaseLiveTraceFreshnessAt A strategy hwin package env
      n := by
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
          let twoNext : TwoPending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
              (env n).inputTwo one (env n).inputOne).1.openControl
          refine ⟨oneNext, twoNext, ?_, ?_⟩
          · unfold literalCombinedFreshPhaseLiveRootSemanticTrace at hcontrols ⊢
            rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hcontrols, hgraph]
            rfl
          · rw [literalCombinedFreshPendingFreshnessTrace_succ,
              ← hfreshness]
            simp [literalCombinedFreshPhaseLiveTraceInputs,
              literalCombinedFreshPhaseLiveTraceGraphs,
              decoratedFreshnessLocalStep, hgraph, oneNext, twoNext,
              literalCombinedFreshPhaseLiveRecvTwo]
      | left =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
              (env n).inputOne two (env n).inputTwo).1.openControl
          let twoNext : TwoPending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshTwoPendingStep A strategy hwin)
              two (env n).inputTwo).1
          refine ⟨oneNext, twoNext, ?_, ?_⟩
          · unfold literalCombinedFreshPhaseLiveRootSemanticTrace at hcontrols ⊢
            rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hcontrols, hgraph]
            rfl
          · rw [literalCombinedFreshPendingFreshnessTrace_succ,
              ← hfreshness]
            simp [literalCombinedFreshPhaseLiveTraceInputs,
              literalCombinedFreshPhaseLiveTraceGraphs,
              decoratedFreshnessLocalStep, hgraph, oneNext, twoNext,
              literalCombinedFreshPhaseLiveRecvOne,
              literalCombinedFreshOneReceiveFreshness]
      | both =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
              (env n).inputOne two (env n).inputTwo).1.closedControl
          let twoNext : TwoPending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
              (env n).inputTwo one (env n).inputOne).1.closedControl
          refine ⟨oneNext, twoNext, ?_, ?_⟩
          · unfold literalCombinedFreshPhaseLiveRootSemanticTrace at hcontrols ⊢
            rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hcontrols, hgraph]
            rfl
          · rw [literalCombinedFreshPendingFreshnessTrace_succ,
              ← hfreshness]
            simp [literalCombinedFreshPhaseLiveTraceInputs,
              literalCombinedFreshPhaseLiveTraceGraphs,
              decoratedFreshnessLocalStep, hgraph, oneNext, twoNext,
              literalCombinedFreshPhaseLiveRecvOne,
              literalCombinedFreshPhaseLiveRecvTwo,
              literalCombinedFreshOneReceiveFreshness]

/-- The accepted child-code word attached to the phase-live trace. -/
def literalCombinedFreshPhaseLiveInstalledChildCodeWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  package.literalCombinedFreshPendingInstalledChildCodeWord A strategy hwin
    (literalCombinedFreshPhaseLiveTraceInputs env)
    (literalCombinedFreshPhaseLiveTraceGraphs env)

/-- The live-table repair preserves the already established accepted hidden
lineage. -/
theorem literalCombinedFreshPhaseLiveInstalledChildCodeWord_accepts
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy)).Accepts
        (package.literalCombinedFreshPhaseLiveInstalledChildCodeWord A strategy
          hwin env) := by
  exact package.literalCombinedFreshPendingInstalledChildCodeWord_accepts A
    strategy hwin (literalCombinedFreshPhaseLiveTraceInputs env)
      (literalCombinedFreshPhaseLiveTraceGraphs env)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
