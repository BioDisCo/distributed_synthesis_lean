/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalSelectedTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveRootController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveSelectedInvariant

/-!
# Canonical trace invariant for the rooted phase-live controller

The deterministic semantic trace of the corrected phase-live endpoints stays
in the pending carrier and preserves the structural live-table invariant.
This file packages that fact as `ExactClosingSelectedTraceLaws`, lifts it
through the acknowledged relay, and exposes the Moore-facing
`LiteralCrossGraphTraceInvariant` used by readback.

The expected output word is exactly the canonical semantic output word of the
same endpoint maps.  Graph cases occur only in the proof of the selected
invariant; no executable endpoint receives a graph, orientation, leader bit,
history, or view.
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

/-! ## The canonical semantic word -/

/-- Pair of selected endpoint controls before round `n`. -/
noncomputable def literalCombinedFreshPhaseLiveRootSemanticTrace
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : Nat →
      OneControl A strategy hwin package × TwoControl A strategy hwin package :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
    (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
    (package.literalCombinedFreshPhaseLiveNoRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseLiveOpenRecvOne A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
    (package.literalCombinedFreshPhaseLiveOpenRecvTwo A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
    (package.literalCombinedFreshPhaseLiveClose A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)) env

/-- Process-one component of the canonical semantic output word. -/
noncomputable def literalCombinedFreshPhaseLiveRootSemanticOutputOne
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₁ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne
    (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
    (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
    (package.literalCombinedFreshPhaseLiveNoRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseLiveOpenRecvOne A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
    (package.literalCombinedFreshPhaseLiveOpenRecvTwo A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
    (package.literalCombinedFreshPhaseLiveClose A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)) env

/-- Process-two component of the canonical semantic output word. -/
noncomputable def literalCombinedFreshPhaseLiveRootSemanticOutputTwo
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo
    (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
    (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
    (package.literalCombinedFreshPhaseLiveNoRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseLiveOpenRecvOne A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
    (package.literalCombinedFreshPhaseLiveOpenRecvTwo A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
    (package.literalCombinedFreshPhaseLiveClose A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)) env

/-! ## Structural selection along the semantic trace -/

/-- The semantic pair is the canonical pair at time `n`, is still pending,
and satisfies the corrected live-table invariant. -/
def LiteralCombinedFreshPhaseLiveCanonicalSelected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (one : OneControl A strategy hwin package)
    (two : TwoControl A strategy hwin package) (n : Nat) : Prop :=
  ∃ onePending : OnePending A strategy hwin package,
    ∃ twoPending : TwoPending A strategy hwin package,
      one = .inl onePending ∧ two = .inl twoPending ∧
        package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy
          hwin onePending twoPending ∧
        (one, two) =
          package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
            hwin env n

/-- The structural selected predicate satisfies all exact-close trace laws.
The output equations are inherited from the canonical semantic trace, while
the new content is preservation of the live tables in all three graph cases.
-/
noncomputable def literalCombinedFreshPhaseLiveRootSelectedTraceLaws
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws
      (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
      (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
      (package.literalCombinedFreshPhaseLiveNoRecvOne A strategy hwin)
      (package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin)
      (package.literalCombinedFreshPhaseLiveOpenRecvOne A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
      (package.literalCombinedFreshPhaseLiveOpenRecvTwo A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
      (package.literalCombinedFreshPhaseLiveClose A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
      (fun _ _ ↦ True)
      (package.LiteralCombinedFreshPhaseLiveCanonicalSelected A strategy hwin
        env)
      env
      (package.literalCombinedFreshPhaseLiveRootSemanticOutputOne A strategy
        hwin env)
      (package.literalCombinedFreshPhaseLiveRootSemanticOutputTwo A strategy
        hwin env) := by
  let initialOne :=
    package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
  let initialTwo :=
    package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
  let noRecvOne :=
    package.literalCombinedFreshPhaseLiveNoRecvOne A strategy hwin
  let noRecvTwo :=
    package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin
  let openRecvOne := package.literalCombinedFreshPhaseLiveOpenRecvOne A
    strategy hwin initialOne
  let openRecvTwo := package.literalCombinedFreshPhaseLiveOpenRecvTwo A
    strategy hwin initialTwo
  let close := package.literalCombinedFreshPhaseLiveClose A strategy hwin
    initialOne initialTwo
  let canonicalLaws :=
    FiniteAcknowledgedDelayedCarrier.exactClosingCanonicalSelectedTraceLaws
      (.inl initialOne : OneControl A strategy hwin package)
      (.inl initialTwo : TwoControl A strategy hwin package)
      noRecvOne noRecvTwo openRecvOne openRecvTwo close env (fun _ _ ↦ True)
  refine {
    initial := ?_
    strictRight := ?_
    strictLeft := ?_
    both := ?_ }
  · exact ⟨initialOne, initialTwo, rfl, rfl,
      package.literalCombinedFreshPhaseLiveStructuralSelected_initial A
        strategy hwin, rfl⟩
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hstructural, hcanonical⟩
    let oneNext : OnePending A strategy hwin package :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalCombinedFreshOnePendingStep A strategy hwin)
        onePending (env n).inputOne).1
    let twoNext : TwoPending A strategy hwin package :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin twoPending
        (env n).inputTwo onePending (env n).inputOne).1.openControl
    have hnextStructural :=
      package.literalCombinedFreshPhaseLiveStructuralSelected_strictRight A
        strategy hwin onePending twoPending hstructural
          ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictRight n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, ?_, ?_, ?_, hnextCanonical.1⟩,
      hnextCanonical.2⟩
    · rfl
    · rfl
    · exact hnextStructural
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hstructural, hcanonical⟩
    let oneNext : OnePending A strategy hwin package :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin onePending
        (env n).inputOne twoPending (env n).inputTwo).1.openControl
    let twoNext : TwoPending A strategy hwin package :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalCombinedFreshTwoPendingStep A strategy hwin)
        twoPending (env n).inputTwo).1
    have hnextStructural :=
      package.literalCombinedFreshPhaseLiveStructuralSelected_strictLeft A
        strategy hwin onePending twoPending hstructural
          ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.strictLeft n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, ?_, ?_, ?_, hnextCanonical.1⟩,
      hnextCanonical.2⟩
    · rfl
    · rfl
    · exact hnextStructural
  · intro n one two _hrel hselected hgraph
    rcases hselected with
      ⟨onePending, twoPending, rfl, rfl, hstructural, hcanonical⟩
    let oneNext : OnePending A strategy hwin package :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin onePending
        (env n).inputOne twoPending (env n).inputTwo).1.closedControl
    let twoNext : TwoPending A strategy hwin package :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin twoPending
        (env n).inputTwo onePending (env n).inputOne).1.closedControl
    have hnextStructural :=
      package.literalCombinedFreshPhaseLiveStructuralSelected_both A strategy
        hwin onePending twoPending hstructural
          ((env n).inputOne, (env n).inputTwo)
    have hnextCanonical := canonicalLaws.both n (.inl onePending)
      (.inl twoPending) trivial hcanonical hgraph
    refine ⟨⟨oneNext, twoNext, ?_, ?_, ?_, hnextCanonical.1⟩,
      hnextCanonical.2⟩
    · rfl
    · rfl
    · exact hnextStructural

/-! ## Pointwise access to the structural semantic run -/

/-- Every canonical semantic control pair is pending and structurally valid.
This is the convenient pointwise form for the later entry-state and emitted-
round alignment proofs. -/
theorem literalCombinedFreshPhaseLiveRootSemanticTrace_selected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralCombinedFreshPhaseLiveCanonicalSelected A strategy hwin env
      (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n).1
      (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n).2 n := by
  intro n
  induction n with
  | zero =>
      exact
        (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A strategy
          hwin env).initial
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only [literalCombinedFreshPhaseLiveRootSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using
            (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
              strategy hwin env).strictRight n _ _ trivial ih hgraph |>.1
      | left =>
          simpa only [literalCombinedFreshPhaseLiveRootSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using
            (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
              strategy hwin env).strictLeft n _ _ trivial ih hgraph |>.1
      | both =>
          simpa only [literalCombinedFreshPhaseLiveRootSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using
            (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
              strategy hwin env).both n _ _ trivial ih hgraph |>.1

/-! ## Acknowledged Mealy and Moore endpoints -/

/-- The acknowledged rooted Mealy controller follows the structurally valid
canonical semantic trace. -/
noncomputable def literalCombinedFreshPhaseLiveRootMealyTraceInvariant
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    (package.literalCombinedFreshPhaseLiveRootController A strategy hwin
      ).LiteralCrossMealyTraceInvariant env := by
  exact
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant
      (initialOne :=
        .inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
      (initialTwo :=
        .inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
      (noRecvOne :=
        package.literalCombinedFreshPhaseLiveNoRecvOne A strategy hwin)
      (noRecvTwo :=
        package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin)
      (openRecvOne := package.literalCombinedFreshPhaseLiveOpenRecvOne A
        strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
      (openRecvTwo := package.literalCombinedFreshPhaseLiveOpenRecvTwo A
        strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
      (close := package.literalCombinedFreshPhaseLiveClose A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
      (Rel := fun _ _ ↦ True)
      (BlindOne := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (BlindTwo := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (Selected := package.LiteralCombinedFreshPhaseLiveCanonicalSelected A
        strategy hwin env)
      (env := env)
      (expectedOutputOne :=
        package.literalCombinedFreshPhaseLiveRootSemanticOutputOne A strategy
          hwin env)
      (expectedOutputTwo :=
        package.literalCombinedFreshPhaseLiveRootSemanticOutputTwo A strategy
          hwin env)
      (package.literalCombinedFreshPhaseLiveRootBlindForkLaws A strategy hwin)
      (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A strategy
        hwin env)

/-- Moore-facing trace invariant for the actual finite physical controller. -/
noncomputable def literalCombinedFreshPhaseLiveRootTraceInvariant
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    (package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
      hwin).LiteralCrossGraphTraceInvariant env :=
  (package.literalCombinedFreshPhaseLiveRootMealyTraceInvariant A strategy hwin
    env).toMooreTraceInvariant _

/-- The actual physical trace word is the canonical phase-live reference
word. -/
theorem literalCombinedFreshPhaseLiveRootTraceWord_eq_referenceWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (package.literalCombinedFreshPhaseLiveRootTraceInvariant A strategy hwin
        env).referenceWord controller := by
  dsimp only
  exact
    (package.literalCombinedFreshPhaseLiveRootTraceInvariant A strategy hwin
      env).globalMachineTraceWord_eq_referenceWord _

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
