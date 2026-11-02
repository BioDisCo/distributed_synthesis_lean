/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveSelectedInvariant

/-!
# Pending-or-recurrent invariant of the phase-activated controller

The activation guard is evaluated independently at the two endpoints.  This
module proves the essential safety fact for the complete finite controller:
on its semantic run the endpoints are always both pending or both recurrent.
In the pending branch the corrected phase-live structural invariant is
preserved, and the two local activation guards agree.  A true guard therefore
moves both endpoints to the recurrent kernel in the same physical round;
afterwards the recurrent summand is absorbing.

This is a runtime-shape theorem, not an observability assumption.  Guard
agreement is proved from finite carried phases and the delivered finite stage;
no endpoint is told the graph, orientation, leader, hierarchy side, history,
or semantic view.
-/

namespace DistributedSynthesis

universe u v x y s

/-- On a persistent strict-reversal tail, an actual adjacent left-to-right
switch occurs after every prescribed prefix.  This is the graph-only witness
consumed by the local phase activation proof; it is never runtime input. -/
theorem PersistentStrictReversalTail.exists_adjacent_left_right_after
    {graphs : Nat → Graph} (h : PersistentStrictReversalTail graphs)
    (start : Nat) :
    ∃ n : Nat, start ≤ n ∧ graphs n = .left ∧ graphs (n + 1) = .right := by
  classical
  rcases h.1 with ⟨noBothFrom, hnoBoth⟩
  rcases h.2.1 (max start noBothFrom) with
    ⟨leftAt, hleftAt, hleft⟩
  have hexists : ∃ n : Nat, leftAt < n ∧ graphs n = .right := by
    rcases h.2.2 (leftAt + 1) with ⟨rightAt, hrightAt, hright⟩
    exact ⟨rightAt, by omega, hright⟩
  let firstRight := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hprevNotRight : graphs (firstRight - 1) ≠ .right := by
    intro hprevRight
    by_cases hpred : firstRight - 1 = leftAt
    · rw [hpred, hleft] at hprevRight
      contradiction
    · have hleftPred : leftAt < firstRight - 1 := by omega
      have hpredFirst : firstRight - 1 < firstRight := by omega
      exact Nat.find_min hexists hpredFirst ⟨hleftPred, hprevRight⟩
  have hprevNotBoth : graphs (firstRight - 1) ≠ .both := by
    apply hnoBoth
    have hNLeft : noBothFrom ≤ leftAt :=
      Nat.le_trans (Nat.le_max_right start noBothFrom) hleftAt
    omega
  have hprevLeft : graphs (firstRight - 1) = .left := by
    cases hgraph : graphs (firstRight - 1) with
    | right => exact False.elim (hprevNotRight hgraph)
    | left => rfl
    | both => exact False.elim (hprevNotBoth hgraph)
  refine ⟨firstRight - 1, ?_, hprevLeft, ?_⟩
  · have hstartLeft : start ≤ leftAt :=
      Nat.le_trans (Nat.le_max_left start noBothFrom) hleftAt
    exact hstartLeft.trans (Nat.le_sub_one_of_lt hfirst.1)
  · have hpositive : 1 ≤ firstRight := by omega
    rw [Nat.sub_add_cancel hpositive]
    exact hfirst.2

/-- Mirror boundary: after every prefix a strict-right block is followed by a
strict-left block. -/
theorem PersistentStrictReversalTail.exists_adjacent_right_left_after
    {graphs : Nat → Graph} (h : PersistentStrictReversalTail graphs)
    (start : Nat) :
    ∃ n : Nat, start ≤ n ∧ graphs n = .right ∧ graphs (n + 1) = .left := by
  classical
  rcases h.1 with ⟨noBothFrom, hnoBoth⟩
  rcases h.2.2 (max start noBothFrom) with
    ⟨rightAt, hrightAt, hright⟩
  have hexists : ∃ n : Nat, rightAt < n ∧ graphs n = .left := by
    rcases h.2.1 (rightAt + 1) with ⟨leftAt, hleftAt, hleft⟩
    exact ⟨leftAt, by omega, hleft⟩
  let firstLeft := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hprevNotLeft : graphs (firstLeft - 1) ≠ .left := by
    intro hprevLeft
    by_cases hpred : firstLeft - 1 = rightAt
    · rw [hpred, hright] at hprevLeft
      contradiction
    · have hrightPred : rightAt < firstLeft - 1 := by omega
      have hpredFirst : firstLeft - 1 < firstLeft := by omega
      exact Nat.find_min hexists hpredFirst ⟨hrightPred, hprevLeft⟩
  have hprevNotBoth : graphs (firstLeft - 1) ≠ .both := by
    apply hnoBoth
    have hNRight : noBothFrom ≤ rightAt :=
      Nat.le_trans (Nat.le_max_right start noBothFrom) hrightAt
    omega
  have hprevRight : graphs (firstLeft - 1) = .right := by
    cases hgraph : graphs (firstLeft - 1) with
    | right => rfl
    | left => exact False.elim (hprevNotLeft hgraph)
    | both => exact False.elim (hprevNotBoth hgraph)
  refine ⟨firstLeft - 1, ?_, hprevRight, ?_⟩
  · have hstartRight : start ≤ rightAt :=
      Nat.le_trans (Nat.le_max_left start noBothFrom) hrightAt
    exact hstartRight.trans (Nat.le_sub_one_of_lt hfirst.1)
  · have hpositive : 1 ≤ firstLeft := by omega
    rw [Nat.sub_add_cancel hpositive]
    exact hfirst.2

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

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
      package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
      package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

private abbrev OneRecurrent (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
    package

private abbrev TwoRecurrent (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
    package

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package (OneRecurrent A strategy hwin package)

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package (TwoRecurrent A strategy hwin package)

/-- Reachable sum shape of the activated controller.  The extra pending field
is precisely the agreement needed to rule out a mixed activation. -/
inductive LiteralCombinedFreshPhaseActivatedSelected
    (package : Package A strategy hwin (initial := initial)) :
    OneControl A strategy hwin package →
      TwoControl A strategy hwin package → Prop
  | pending (one : OnePending A strategy hwin package)
      (two : TwoPending A strategy hwin package)
      (structural :
        package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy
          hwin one two)
      (ready_eq :
        package.literalCombinedFreshRightActivationReadyOne A strategy hwin
            one =
          package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
            two one) :
      LiteralCombinedFreshPhaseActivatedSelected package (.inl one) (.inl two)
  | recurrent (one : OneRecurrent A strategy hwin package)
      (two : TwoRecurrent A strategy hwin package) :
      LiteralCombinedFreshPhaseActivatedSelected package (.inr one) (.inr two)

/-- The common root is safely pending. -/
theorem literalCombinedFreshPhaseActivatedSelected_initial
    (package : Package A strategy hwin (initial := initial)) :
    package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin
      (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
      (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy
        hwin)) := by
  apply LiteralCombinedFreshPhaseActivatedSelected.pending
  · exact package.literalCombinedFreshPhaseLiveStructuralSelected_initial A
      strategy hwin
  · exact (package.literalCombinedFreshRightActivationReady_initial A
      strategy hwin).1.trans
        (package.literalCombinedFreshRightActivationReady_initial A strategy
          hwin).2.symm

/-- Strict-right preservation.  This is the only graph case that may activate:
guard agreement makes the transition joint. -/
theorem LiteralCombinedFreshPhaseActivatedSelected.strictRight
    (package : Package A strategy hwin (initial := initial))
    {one : OneControl A strategy hwin package}
    {two : TwoControl A strategy hwin package}
    (selected : package.LiteralCombinedFreshPhaseActivatedSelected A strategy
      hwin one two)
    (input : In₁ × In₂) :
    package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin one
        input.1).1
      (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
        two input.2 one input.1).1 := by
  cases selected with
  | pending one two hstruct hreadyEq =>
      cases hreadyOne :
        package.literalCombinedFreshRightActivationReadyOne A strategy hwin one
      · have hreadyTwo :
            package.literalCombinedFreshRightActivationReadyTwo A strategy
              hwin two one = false := by
          rw [← hreadyEq]
          exact hreadyOne
        let oneNext : OnePending A strategy hwin package :=
          (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
            (package.literalCombinedFreshOnePendingStep A strategy hwin) one
              input.1).1
        let twoNext : TwoPending A strategy hwin package :=
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            input.2 one input.1).1.openControl
        have hnextStructural :=
          package.literalCombinedFreshPhaseLiveStructuralSelected_strictRight
            A strategy hwin one two hstruct input
        have hnextReady :
            package.literalCombinedFreshRightActivationReadyOne A strategy
                hwin oneNext =
              package.literalCombinedFreshRightActivationReadyTwo A strategy
                hwin twoNext oneNext := by
          apply package.literalCombinedFreshRightActivationReady_eq_of_phase_eq
          rfl
        simpa [literalCombinedFreshPhaseActivatedNoRecvOne,
          literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyOne, hreadyTwo,
          oneNext, twoNext] using
            (LiteralCombinedFreshPhaseActivatedSelected.pending
              (package := package) oneNext twoNext hnextStructural hnextReady)
      · have hreadyTwo :
            package.literalCombinedFreshRightActivationReadyTwo A strategy
              hwin two one = true := by
          rw [← hreadyEq]
          exact hreadyOne
        simp only [literalCombinedFreshPhaseActivatedNoRecvOne,
          literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyOne, hreadyTwo,
          if_true]
        unfold literalCombinedFreshRightSwitchNoRecvOne
          literalCombinedFreshRightSwitchRecvTwo
        exact LiteralCombinedFreshPhaseActivatedSelected.recurrent _ _
  | recurrent one two =>
      simpa [literalCombinedFreshPhaseActivatedNoRecvOne,
        literalCombinedFreshPhaseActivatedOpenRecvTwo] using
          (LiteralCombinedFreshPhaseActivatedSelected.recurrent
            (package := package)
            (package.literalRightSeamTaggedNoRecvOne A strategy hwin one
              input.1).1
            (package.literalRightSeamTaggedRecvTwo A strategy hwin two input.2
              one input.1).1)

/-- A strict-left round cannot activate the right kernel.  It stays pending,
or advances an already recurrent pair. -/
theorem LiteralCombinedFreshPhaseActivatedSelected.strictLeft
    (package : Package A strategy hwin (initial := initial))
    {one : OneControl A strategy hwin package}
    {two : TwoControl A strategy hwin package}
    (selected : package.LiteralCombinedFreshPhaseActivatedSelected A strategy
      hwin one two)
    (input : In₁ × In₂) :
    package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin
        one input.1 two input.2).1
      (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin two
        input.2).1 := by
  cases selected with
  | pending one two hstruct _ =>
      let oneNext : OnePending A strategy hwin package :=
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl
      let twoNext : TwoPending A strategy hwin package :=
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
            input.2).1
      have hnextStructural :=
        package.literalCombinedFreshPhaseLiveStructuralSelected_strictLeft A
          strategy hwin one two hstruct input
      have hnextReady :
          package.literalCombinedFreshRightActivationReadyOne A strategy hwin
              oneNext =
            package.literalCombinedFreshRightActivationReadyTwo A strategy
              hwin twoNext oneNext := by
        apply package.literalCombinedFreshRightActivationReady_eq_of_phase_eq
        rfl
      simpa [literalCombinedFreshPhaseActivatedOpenRecvOne,
        literalCombinedFreshPhaseActivatedNoRecvTwo, oneNext, twoNext] using
          (LiteralCombinedFreshPhaseActivatedSelected.pending
            (package := package) oneNext twoNext hnextStructural hnextReady)
  | recurrent one two =>
      simpa [literalCombinedFreshPhaseActivatedOpenRecvOne,
        literalCombinedFreshPhaseActivatedNoRecvTwo] using
          (LiteralCombinedFreshPhaseActivatedSelected.recurrent
            (package := package)
            (package.literalRightSeamTaggedRecvOne A strategy hwin one input.1
              two input.2).1
            (package.literalRightSeamTaggedNoRecvTwo A strategy hwin two
              input.2).1)

/-- A simultaneous round stays pending with both guards disabled, or advances
an already recurrent pair. -/
theorem LiteralCombinedFreshPhaseActivatedSelected.both
    (package : Package A strategy hwin (initial := initial))
    {one : OneControl A strategy hwin package}
    {two : TwoControl A strategy hwin package}
    (selected : package.LiteralCombinedFreshPhaseActivatedSelected A strategy
      hwin one two)
    (input : In₁ × In₂) :
    package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin one
        input.1 two input.2).1
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin one
        input.1 two input.2).2 := by
  cases selected with
  | pending one two hstruct _ =>
      let oneNext : OnePending A strategy hwin package :=
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.closedControl
      let twoNext : TwoPending A strategy hwin package :=
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.closedControl
      have hnextStructural :=
        package.literalCombinedFreshPhaseLiveStructuralSelected_both A strategy
          hwin one two hstruct input
      have hready := package.literalCombinedFreshRightActivationReady_after_both
        A strategy hwin one two input
      have hnextReady :
          package.literalCombinedFreshRightActivationReadyOne A strategy hwin
              oneNext =
            package.literalCombinedFreshRightActivationReadyTwo A strategy
              hwin twoNext oneNext := hready.1.trans hready.2.symm
      simpa [literalCombinedFreshPhaseActivatedClose, oneNext, twoNext] using
        (LiteralCombinedFreshPhaseActivatedSelected.pending
          (package := package) oneNext twoNext hnextStructural hnextReady)
  | recurrent one two =>
      simpa [literalCombinedFreshPhaseActivatedClose] using
        (LiteralCombinedFreshPhaseActivatedSelected.recurrent
          (package := package)
          (package.literalRightSeamTaggedRecvOne A strategy hwin one input.1
            two input.2).1
          (package.literalRightSeamTaggedRecvTwo A strategy hwin two input.2
            one input.1).1)

/-! ## The actual semantic trace -/

/-- Pair of endpoint controls before physical round `n`. -/
noncomputable def literalCombinedFreshPhaseActivatedSemanticTrace
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : Nat →
      OneControl A strategy hwin package × TwoControl A strategy hwin package :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
    (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
    (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
    (package.literalCombinedFreshPhaseActivatedClose A strategy hwin) env

/-- On every environment, mixed pending/recurrent controls are unreachable. -/
theorem literalCombinedFreshPhaseActivatedSemanticTrace_selected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n).1
      (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n).2 := by
  intro n
  induction n with
  | zero =>
      exact package.literalCombinedFreshPhaseActivatedSelected_initial A
        strategy hwin
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using ih.strictRight A strategy hwin package
              ((env n).inputOne, (env n).inputTwo)
      | left =>
          simpa only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using ih.strictLeft A strategy hwin package
              ((env n).inputOne, (env n).inputTwo)
      | both =>
          simpa only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using ih.both A strategy hwin package
              ((env n).inputOne, (env n).inputTwo)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
