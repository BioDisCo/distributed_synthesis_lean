/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchAwareStageLiveness
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveTableReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveTableSegment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedTraceInvariant

/-!
# Pending trace bridge and forced phase activation

Before the phase-activated controller enters its recurrent summand, its
pending controls are exactly those of the corrected phase-live controller.
This file couples those two semantic traces.  Root-prefix reachability of the
phase-live table then makes every honest strict-left receive retain a live
right stage.  Consequently an adjacent left-to-right switch activates both
endpoints jointly.

All trace alignment, graph cases, and reachability witnesses are proof-side.
The executable endpoints inspect only their finite phase and retained stage;
they receive no graph, hierarchy side, leader flag, history, or semantic view.
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

private abbrev OneRecurrent (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
    package

private abbrev TwoRecurrent (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
    package

private abbrev ActivatedOneControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package (OneRecurrent A strategy hwin package)

private abbrev ActivatedTwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package (TwoRecurrent A strategy hwin package)

private abbrev PhaseLiveOneControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package) Unit

private abbrev PhaseLiveTwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package) Unit

/-! ## From the synchronized table witness to receiver-only reachability -/

theorem literalRightSeamReceiverTableLocallyReachable_of_rootReachable
    (package : Package A strategy hwin (initial := initial))
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (sender :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package)
    (hreach : package.LiteralRightSeamTableRootReachable A strategy hwin
      receiver sender) :
    package.LiteralRightSeamReceiverTableLocallyReachable A strategy hwin
      receiver := by
  rcases hreach with ⟨past, _hsender, hreceiver⟩
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      (package.literalRightSeamInstalled A strategy hwin receiver.1)
  refine ⟨finiteCrossAnchorSenderAtPrefix table past, past, rfl, ?_⟩
  exact hreceiver

/-! ## Every strict-left pending step leaves a live stage -/

theorem exists_literalCombinedFreshPhaseLiveRecvOne_open_stage_of_rootReachable
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
        hwin package,
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl.2.1).2.2.2 = some stage := by
  classical
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  apply package.exists_literalRightSeamBranchRestartedReceiverRecv_stage_of_tableReachable
    A strategy hwin
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A
      strategy hwin one two hone]
    exact package.literalRightSeamReceiverTableLocallyReachable_initial A
      strategy hwin _ _ _
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A
      strategy hwin one two hone]
    exact package.literalRightSeamReceiverTableLocallyReachable_initial A
      strategy hwin _ _ _
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A
      strategy hwin one two hone]
    simp only [LiteralCombinedFreshPhaseLiveRootReachableSelected,
      LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo] at hselected
    exact package.literalRightSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin _ _ hselected.2.1
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A
      strategy hwin one two hone]
    simp only [LiteralCombinedFreshPhaseLiveRootReachableSelected,
      LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo] at hselected
    exact package.literalRightSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin _ _ hselected.2

/-- A strict-left step whose physically live right receiver is already in the
canonical row leaves both activation guards true.  A right-to-left switch
installs exactly this row, and repeated left rounds preserve it. -/
theorem literalCombinedFreshRightActivationReady_after_reachable_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.openControl
    let twoNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two input.2
    package.literalCombinedFreshRightActivationReadyOne A strategy hwin
        oneNext = true ∧
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
        twoNext.1 oneNext = true := by
  dsimp only
  obtain ⟨stage, hstage⟩ :=
    package.exists_literalCombinedFreshPhaseLiveRecvOne_open_stage_of_rootReachable
      A strategy hwin one two hselected input
  apply package.literalCombinedFreshRightActivationReady_of_live_pair A
    strategy hwin _ _ stage
  · exact hstage
  · rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A
      strategy hwin] at hstage
    exact
      package.literalRightSeamBranchRestartedReceiverRecv_stage_row A strategy
        hwin _ _ _ stage hstage
  · rfl
  · rfl

/-! ## Pending activated traces coincide with the phase-live trace -/

/-- Non-dependent case splitter for the indexed activated invariant. -/
theorem LiteralCombinedFreshPhaseActivatedSelected.pending_or_recurrent
    (package : Package A strategy hwin (initial := initial))
    {one : ActivatedOneControl A strategy hwin package}
    {two : ActivatedTwoControl A strategy hwin package}
    (selected : package.LiteralCombinedFreshPhaseActivatedSelected A strategy
      hwin one two) :
    (∃ onePending : OnePending A strategy hwin package,
      ∃ twoPending : TwoPending A strategy hwin package,
        one = .inl onePending ∧ two = .inl twoPending ∧
          package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy
            hwin onePending twoPending ∧
          package.literalCombinedFreshRightActivationReadyOne A strategy hwin
              onePending =
            package.literalCombinedFreshRightActivationReadyTwo A strategy
              hwin twoPending onePending) ∨
      (∃ oneRecurrent : OneRecurrent A strategy hwin package,
        ∃ twoRecurrent : TwoRecurrent A strategy hwin package,
          one = .inr oneRecurrent ∧ two = .inr twoRecurrent) := by
  cases selected with
  | pending one two structural readyEq =>
      exact Or.inl ⟨one, two, rfl, rfl, structural, readyEq⟩
  | recurrent one two =>
      exact Or.inr ⟨one, two, rfl, rfl⟩

/-- Up to the (unique) activation round, the activated semantic trace is
literally the canonical phase-live trace.  This is deliberately conditional
on the activated trace still being pending: after activation its recurrent
summand has a different control type and no such equality is intended. -/
theorem literalCombinedFreshPhaseActivatedSemanticTrace_pending_eq_phaseLive
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ (n : Nat)
      (one : OnePending A strategy hwin package)
      (two : TwoPending A strategy hwin package),
    package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inl one, .inl two) →
      package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n = (.inl one, .inl two) := by
  intro n
  induction n with
  | zero =>
      intro one two hactivated
      have hone := Sum.inl.inj (congrArg Prod.fst hactivated)
      have htwo := Sum.inl.inj (congrArg Prod.snd hactivated)
      subst one
      subst two
      rfl
  | succ n ih =>
      intro one two hactivated
      have hselected :=
        package.literalCombinedFreshPhaseActivatedSemanticTrace_selected A
          strategy hwin env n
      rcases hselected.pending_or_recurrent A strategy hwin package with
        hpending | hrecurrent
      · rcases hpending with
          ⟨oldOne, oldTwo, honeOld, htwoOld, _hstructural, hreadyEq⟩
        have holdActivated :
              package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env n = (.inl oldOne, .inl oldTwo) := by
            apply Prod.ext
            · exact honeOld
            · exact htwoOld
        have holdPhase := ih oldOne oldTwo holdActivated
        cases hgraph : (env n).graph with
        | right =>
            have hactivatedStep :
                package.literalCombinedFreshPhaseActivatedSemanticTrace A
                    strategy hwin env (n + 1) =
                  ((package.literalCombinedFreshPhaseActivatedNoRecvOne A
                      strategy hwin
                      (package.literalCombinedFreshPhaseActivatedSemanticTrace
                        A strategy hwin env n).1 (env n).inputOne).1,
                    (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A
                      strategy hwin
                      (package.literalCombinedFreshPhaseActivatedSemanticTrace
                        A strategy hwin env n).2 (env n).inputTwo
                      (package.literalCombinedFreshPhaseActivatedSemanticTrace
                        A strategy hwin env n).1 (env n).inputOne).1) := by
              simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdActivated] at hactivatedStep
            have hcomputed := hactivatedStep.symm.trans hactivated
            cases hreadyOne :
              package.literalCombinedFreshRightActivationReadyOne A strategy
                hwin oldOne
            · have hreadyTwo :
                  package.literalCombinedFreshRightActivationReadyTwo A
                      strategy hwin oldTwo oldOne = false := by
                rw [← hreadyEq]
                exact hreadyOne
              simp only [literalCombinedFreshPhaseActivatedNoRecvOne,
                literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyOne,
                hreadyTwo, Bool.false_eq_true, if_false] at hcomputed
              have honeNext := Sum.inl.inj (congrArg Prod.fst hcomputed)
              have htwoNext := Sum.inl.inj (congrArg Prod.snd hcomputed)
              subst one
              subst two
              have hphaseStep :
                  package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                      strategy hwin env (n + 1) =
                    ((package.literalCombinedFreshPhaseLiveNoRecvOne A
                      strategy hwin
                      (package.literalCombinedFreshPhaseLiveRootSemanticTrace
                        A strategy hwin env n).1 (env n).inputOne).1,
                    (package.literalCombinedFreshPhaseLiveOpenRecvTwo A
                      strategy hwin
                      (package.literalCombinedFreshPendingOnlyInitialTwo A
                        strategy hwin)
                      (package.literalCombinedFreshPhaseLiveRootSemanticTrace
                        A strategy hwin env n).2 (env n).inputTwo
                      (package.literalCombinedFreshPhaseLiveRootSemanticTrace
                        A strategy hwin env n).1 (env n).inputOne).1) := by
                simp only [literalCombinedFreshPhaseLiveRootSemanticTrace,
                  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                  hgraph]
              rw [holdPhase] at hphaseStep
              exact hphaseStep
            · have hreadyTwo :
                  package.literalCombinedFreshRightActivationReadyTwo A
                      strategy hwin oldTwo oldOne = true := by
                rw [← hreadyEq]
                exact hreadyOne
              simp [literalCombinedFreshPhaseActivatedNoRecvOne,
                literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyOne,
                hreadyTwo, literalCombinedFreshRightSwitchNoRecvOne,
                literalCombinedFreshRightSwitchRecvTwo] at hcomputed
        | left =>
            have hactivatedStep :
                package.literalCombinedFreshPhaseActivatedSemanticTrace A
                    strategy hwin env (n + 1) =
                  ((package.literalCombinedFreshPhaseActivatedOpenRecvOne A
                      strategy hwin
                      (package.literalCombinedFreshPhaseActivatedSemanticTrace
                        A strategy hwin env n).1 (env n).inputOne
                      (package.literalCombinedFreshPhaseActivatedSemanticTrace
                        A strategy hwin env n).2 (env n).inputTwo).1,
                    (package.literalCombinedFreshPhaseActivatedNoRecvTwo A
                      strategy hwin
                      (package.literalCombinedFreshPhaseActivatedSemanticTrace
                        A strategy hwin env n).2 (env n).inputTwo).1) := by
              simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdActivated] at hactivatedStep
            have hcomputed := hactivatedStep.symm.trans hactivated
            simp only [literalCombinedFreshPhaseActivatedOpenRecvOne,
              literalCombinedFreshPhaseActivatedNoRecvTwo] at hcomputed
            have honeNext := Sum.inl.inj (congrArg Prod.fst hcomputed)
            have htwoNext := Sum.inl.inj (congrArg Prod.snd hcomputed)
            subst one
            subst two
            have hphaseStep :
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                    strategy hwin env (n + 1) =
                  ((package.literalCombinedFreshPhaseLiveOpenRecvOne A
                    strategy hwin
                    (package.literalCombinedFreshPendingOnlyInitialOne A
                      strategy hwin)
                    (package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                      strategy hwin env n).1 (env n).inputOne
                    (package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo).1,
                  (package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy
                    hwin
                    (package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo).1) := by
              simp only [literalCombinedFreshPhaseLiveRootSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdPhase] at hphaseStep
            exact hphaseStep
        | both =>
            have hactivatedStep :
                package.literalCombinedFreshPhaseActivatedSemanticTrace A
                    strategy hwin env (n + 1) =
                  package.literalCombinedFreshPhaseActivatedClose A strategy
                    hwin
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).1 (env n).inputOne
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo := by
              simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdActivated] at hactivatedStep
            have hcomputed := hactivatedStep.symm.trans hactivated
            simp only [literalCombinedFreshPhaseActivatedClose] at hcomputed
            have honeNext := Sum.inl.inj (congrArg Prod.fst hcomputed)
            have htwoNext := Sum.inl.inj (congrArg Prod.snd hcomputed)
            subst one
            subst two
            have hphaseStep :
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                    strategy hwin env (n + 1) =
                  package.literalCombinedFreshPhaseLiveClose A strategy hwin
                    (package.literalCombinedFreshPendingOnlyInitialOne A
                      strategy hwin)
                    (package.literalCombinedFreshPendingOnlyInitialTwo A
                      strategy hwin)
                    (package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                      strategy hwin env n).1 (env n).inputOne
                    (package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo := by
              simp only [literalCombinedFreshPhaseLiveRootSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdPhase] at hphaseStep
            exact hphaseStep
      · rcases hrecurrent with
          ⟨oldOne, oldTwo, honeOld, htwoOld⟩
        have holdActivated :
              package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env n = (.inr oldOne, .inr oldTwo) := by
            apply Prod.ext
            · exact honeOld
            · exact htwoOld
        cases hgraph : (env n).graph with
        | right =>
            have hstep :
                package.literalCombinedFreshPhaseActivatedSemanticTrace A
                    strategy hwin env (n + 1) =
                  ((package.literalCombinedFreshPhaseActivatedNoRecvOne A
                    strategy hwin
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).1 (env n).inputOne).1,
                  (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A
                    strategy hwin
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).1 (env n).inputOne).1) := by
              simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdActivated] at hstep
            have hcomputed := hstep.symm.trans hactivated
            simp [literalCombinedFreshPhaseActivatedNoRecvOne,
              literalCombinedFreshPhaseActivatedOpenRecvTwo] at hcomputed
        | left =>
            have hstep :
                package.literalCombinedFreshPhaseActivatedSemanticTrace A
                    strategy hwin env (n + 1) =
                  ((package.literalCombinedFreshPhaseActivatedOpenRecvOne A
                    strategy hwin
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).1 (env n).inputOne
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo).1,
                  (package.literalCombinedFreshPhaseActivatedNoRecvTwo A
                    strategy hwin
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo).1) := by
              simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdActivated] at hstep
            have hcomputed := hstep.symm.trans hactivated
            simp [literalCombinedFreshPhaseActivatedOpenRecvOne,
              literalCombinedFreshPhaseActivatedNoRecvTwo] at hcomputed
        | both =>
            have hstep :
                package.literalCombinedFreshPhaseActivatedSemanticTrace A
                    strategy hwin env (n + 1) =
                  package.literalCombinedFreshPhaseActivatedClose A strategy
                    hwin
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).1 (env n).inputOne
                    (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                      strategy hwin env n).2 (env n).inputTwo := by
              simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph]
            rw [holdActivated] at hstep
            have hcomputed := hstep.symm.trans hactivated
            simp [literalCombinedFreshPhaseActivatedClose] at hcomputed

/-- A pending activated semantic state therefore inherits the exact
root-prefix table witness of the canonical phase-live run. -/
theorem literalCombinedFreshPhaseActivatedSemanticTrace_pending_rootReachable
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hactivated :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inl one, .inl two)) :
    package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy hwin
      one two := by
  have hphase :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_pending_eq_phaseLive
      A strategy hwin env n one two hactivated
  have hreachable :=
    package.literalCombinedFreshPhaseLiveRootSemanticTrace_rootReachable A
      strategy hwin env n
  rw [hphase] at hreachable
  rcases hreachable with
    ⟨onePending, twoPending, hone, htwo, hselected, _htrace⟩
  have honeEq := Sum.inl.inj hone
  have htwoEq := Sum.inl.inj htwo
  subst onePending
  subst twoPending
  exact hselected

/-! ## A witnessed left round arms the next strict-right round -/

/-- If the proof-side activated trace is still pending at a strict-left
round, its next pending controls carry a live stage and both finite local
activation tests are true. -/
theorem
    literalCombinedFreshPhaseActivatedSemanticTrace_strictLeft_pending_ready
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hactivated :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inl one, .inl two))
    (hgraph : (env n).graph = .left) :
    ∃ oneNext : OnePending A strategy hwin package,
      ∃ twoNext : TwoPending A strategy hwin package,
        package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
            env (n + 1) = (.inl oneNext, .inl twoNext) ∧
          package.literalCombinedFreshRightActivationReadyOne A strategy hwin
              oneNext = true ∧
          package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
              twoNext oneNext = true := by
  let oneNext : OnePending A strategy hwin package :=
    (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
      (env n).inputOne two (env n).inputTwo).1.openControl
  let twoNext : TwoPending A strategy hwin package :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
        (env n).inputTwo).1
  have hroot :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_pending_rootReachable
      A strategy hwin env n one two hactivated
  have hready :=
    package.literalCombinedFreshRightActivationReady_after_reachable_strictLeft
      A strategy hwin one two hroot
        ((env n).inputOne, (env n).inputTwo)
  have hstep :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
          env (n + 1) =
        ((package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin
          (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env n).1 (env n).inputOne
          (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env n).2 (env n).inputTwo).1,
        (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin
          (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env n).2 (env n).inputTwo).1) := by
    simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hgraph]
  rw [hactivated] at hstep
  refine ⟨oneNext, twoNext, ?_, ?_, ?_⟩
  · simpa only [literalCombinedFreshPhaseActivatedOpenRecvOne,
      literalCombinedFreshPhaseActivatedNoRecvTwo, oneNext, twoNext] using hstep
  · exact hready.1
  · exact hready.2

/-- The proof-side activated trace is jointly in its recurrent summand at
round `n`. -/
def LiteralCombinedFreshPhaseActivatedRecurrentAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  ∃ one : OneRecurrent A strategy hwin package,
    ∃ two : TwoRecurrent A strategy hwin package,
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two)

/-- Before activation, `Armed` means that both local guards agree and are
true.  After activation the recurrent alternative is permanent. -/
def LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin env n ∨
    ∃ one : OnePending A strategy hwin package,
      ∃ two : TwoPending A strategy hwin package,
        package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
            env n = (.inl one, .inl two) ∧
          package.literalCombinedFreshRightActivationReadyOne A strategy hwin
              one = true ∧
            package.literalCombinedFreshRightActivationReadyTwo A strategy
                hwin two one = true

/-- Once recurrent, one further semantic round remains recurrent, for every
graph value. -/
theorem LiteralCombinedFreshPhaseActivatedRecurrentAt.succ
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hrecurrent :
      package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin env
        n) :
    package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin env
      (n + 1) := by
  rcases hrecurrent with ⟨one, two, htrace⟩
  cases hgraph : (env n).graph with
  | right =>
      have hstep :
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
              hwin env (n + 1) =
            ((package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy
              hwin
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).1 (env n).inputOne).1,
            (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy
              hwin
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).2 (env n).inputTwo
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).1 (env n).inputOne).1) := by
        simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
          hgraph]
      rw [htrace] at hstep
      refine ⟨
        (package.literalRightSeamTaggedNoRecvOne A strategy hwin one
          (env n).inputOne).1,
        (package.literalRightSeamTaggedRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).1, ?_⟩
      simpa [literalCombinedFreshPhaseActivatedNoRecvOne,
        literalCombinedFreshPhaseActivatedOpenRecvTwo] using hstep
  | left =>
      have hstep :
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
              hwin env (n + 1) =
            ((package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy
              hwin
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).1 (env n).inputOne
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).2 (env n).inputTwo).1,
            (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy
              hwin
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).2 (env n).inputTwo).1) := by
        simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
          hgraph]
      rw [htrace] at hstep
      refine ⟨
        (package.literalRightSeamTaggedRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1,
        (package.literalRightSeamTaggedNoRecvTwo A strategy hwin two
          (env n).inputTwo).1, ?_⟩
      simpa [literalCombinedFreshPhaseActivatedOpenRecvOne,
        literalCombinedFreshPhaseActivatedNoRecvTwo] using hstep
  | both =>
      have hstep :
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
              hwin env (n + 1) =
            package.literalCombinedFreshPhaseActivatedClose A strategy hwin
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).1 (env n).inputOne
              (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                strategy hwin env n).2 (env n).inputTwo := by
        simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
          hgraph]
      rw [htrace] at hstep
      refine ⟨
        (package.literalRightSeamTaggedRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1,
        (package.literalRightSeamTaggedRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).1, ?_⟩
      simpa [literalCombinedFreshPhaseActivatedClose] using hstep

/-- An armed pending pair activates on the next strict-right round. -/
theorem literalCombinedFreshPhaseActivatedRecurrentAt_of_armed_strictRight
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (htrace :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inl one, .inl two))
    (hreadyOne :
      package.literalCombinedFreshRightActivationReadyOne A strategy hwin one =
        true)
    (hreadyTwo :
      package.literalCombinedFreshRightActivationReadyTwo A strategy hwin two
        one = true)
    (hright : (env n).graph = .right) :
    package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin env
      (n + 1) := by
  let oneNext :=
    (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin
      (.inl one) (env n).inputOne).1
  let twoNext :=
    (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
      (.inl two) (env n).inputTwo (.inl one) (env n).inputOne).1
  have hstep :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
          env (n + 1) = (oneNext, twoNext) := by
    have hraw :
        package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
            env (n + 1) =
          ((package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin
            (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
              hwin env n).1 (env n).inputOne).1,
          (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy
            hwin
            (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
              hwin env n).2 (env n).inputTwo
            (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
              hwin env n).1 (env n).inputOne).1) := by
      simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hright]
    rw [htrace] at hraw
    simpa only [oneNext, twoNext] using hraw
  have honeShape : ∃ recurrent : OneRecurrent A strategy hwin package,
      oneNext = .inr recurrent := by
    simp [oneNext, literalCombinedFreshPhaseActivatedNoRecvOne, hreadyOne,
      literalCombinedFreshRightSwitchNoRecvOne]
  have htwoShape : ∃ recurrent : TwoRecurrent A strategy hwin package,
      twoNext = .inr recurrent := by
    simp [twoNext, literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyTwo,
      literalCombinedFreshRightSwitchRecvTwo]
  rcases honeShape with ⟨oneRecurrent, hone⟩
  rcases htwoShape with ⟨twoRecurrent, htwo⟩
  exact ⟨oneRecurrent, twoRecurrent, hstep.trans (Prod.ext hone htwo)⟩

/-- A left round preserves an armed pending pair.  Readiness itself exposes
the canonical receiver row required by the strict-left liveness bridge. -/
theorem literalCombinedFreshPhaseActivatedArmedOrRecurrentAt_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (harmed :
      package.LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt A strategy
        hwin env n)
    (hleft : (env n).graph = .left) :
    package.LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt A strategy
      hwin env (n + 1) := by
  rcases harmed with hrecurrent | ⟨one, two, htrace, hreadyOne, _hreadyTwo⟩
  · exact Or.inl (hrecurrent.succ A strategy hwin package env n)
  · rcases
        package.literalCombinedFreshPhaseActivatedSemanticTrace_strictLeft_pending_ready
          A strategy hwin env n one two htrace hleft with
      ⟨oneNext, twoNext, hnext, hnextReadyOne, hnextReadyTwo⟩
    exact Or.inr
      ⟨oneNext, twoNext, hnext, hnextReadyOne, hnextReadyTwo⟩

/-- A strict-right round turns an armed-or-recurrent cut into a recurrent
cut. -/
theorem literalCombinedFreshPhaseActivatedRecurrentAt_of_armedOrRecurrent_right
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (harmed :
      package.LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt A strategy
        hwin env n)
    (hright : (env n).graph = .right) :
    package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin env
      (n + 1) := by
  rcases harmed with hrecurrent | ⟨one, two, htrace, hreadyOne, hreadyTwo⟩
  · exact hrecurrent.succ A strategy hwin package env n
  · exact
      package.literalCombinedFreshPhaseActivatedRecurrentAt_of_armed_strictRight
        A strategy hwin env n one two htrace hreadyOne hreadyTwo hright

/-- If activation has not happened at a right-to-left boundary, the right
round resets the delivered member to `false`; the following left receive
therefore initializes the retained right receiver in row `.first` and arms
both endpoints. -/
theorem
    literalCombinedFreshPhaseActivatedArmedOrRecurrentAt_of_pending_right_left
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (htrace :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inl one, .inl two))
    (hright : (env n).graph = .right)
    (hleft : (env (n + 1)).graph = .left) :
    package.LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt A strategy
      hwin env (n + 2) := by
  have hselected :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_selected A
      strategy hwin env n
  rw [htrace] at hselected
  cases hselected with
  | pending _ _ _ hreadyEq =>
      cases hreadyOne :
        package.literalCombinedFreshRightActivationReadyOne A strategy hwin one
      · have hreadyTwo :
            package.literalCombinedFreshRightActivationReadyTwo A strategy
                hwin two one = false := by
          rw [← hreadyEq]
          exact hreadyOne
        let oneRight : OnePending A strategy hwin package :=
          (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
            (package.literalCombinedFreshOnePendingStep A strategy hwin) one
              (env n).inputOne).1
        let twoRight : TwoPending A strategy hwin package :=
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            (env n).inputTwo one (env n).inputOne).1.openControl
        have hraw :
            package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
                hwin env (n + 1) =
              ((package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy
                hwin
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env n).1 (env n).inputOne).1,
              (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy
                hwin
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env n).2 (env n).inputTwo
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env n).1 (env n).inputOne).1) := by
          simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hright]
        rw [htrace] at hraw
        have hnext :
            package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
                hwin env (n + 1) = (.inl oneRight, .inl twoRight) := by
          simpa [literalCombinedFreshPhaseActivatedNoRecvOne,
            literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyOne,
            hreadyTwo, oneRight, twoRight] using hraw
        rcases
            package.literalCombinedFreshPhaseActivatedSemanticTrace_strictLeft_pending_ready
              A strategy hwin env (n + 1) oneRight twoRight hnext hleft with
          ⟨oneNext, twoNext, hnextTrace, hnextReadyOne, hnextReadyTwo⟩
        exact Or.inr
          ⟨oneNext, twoNext, by simpa only [Nat.add_assoc, Nat.reduceAdd] using
            hnextTrace, hnextReadyOne, hnextReadyTwo⟩
      · have hreadyTwo :
            package.literalCombinedFreshRightActivationReadyTwo A strategy
                hwin two one = true := by
          rw [← hreadyEq]
          exact hreadyOne
        have hrecurrent :=
          package.literalCombinedFreshPhaseActivatedRecurrentAt_of_armed_strictRight
            A strategy hwin env n one two htrace hreadyOne hreadyTwo hright
        exact Or.inl (hrecurrent.succ A strategy hwin package env (n + 1))

/-- Armed-or-recurrent status propagates across every finite segment without
simultaneous rounds. -/
theorem literalCombinedFreshPhaseActivatedArmedOrRecurrentAt_add_of_strict
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hstart :
      package.LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt A strategy
        hwin env start) : ∀ d : Nat,
    (∀ k : Nat, k < d → (env (start + k)).graph ≠ .both) →
      package.LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt A strategy
        hwin env (start + d) := by
  intro d
  induction d with
  | zero =>
      intro _hstrict
      simpa only [Nat.add_zero] using hstart
  | succ d ih =>
      intro hstrict
      have hbefore := ih (fun k hk ↦ hstrict k (Nat.lt_succ_of_lt hk))
      have hnotBoth := hstrict d (Nat.lt_succ_self d)
      cases hgraph : (env (start + d)).graph with
      | right =>
          have hrecurrent :=
            package.literalCombinedFreshPhaseActivatedRecurrentAt_of_armedOrRecurrent_right
              A strategy hwin env (start + d) hbefore hgraph
          exact Or.inl (by
            simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hrecurrent)
      | left =>
          have hnext :=
            package.literalCombinedFreshPhaseActivatedArmedOrRecurrentAt_strictLeft
              A strategy hwin env (start + d) hbefore hgraph
          simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hnext
      | both => exact False.elim (hnotBoth hgraph)

/-- An actual adjacent strict-left/strict-right pair forces the proof-side
classifier recurrent unless it was recurrent already.  The interesting
pending branch is discharged by the arbitrary-depth table reachability
theorem above, not just by the first root block. -/
theorem literalCombinedFreshPhaseActivatedRecurrentAt_of_pending_left_right
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hactivated :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inl one, .inl two))
    (hleft : (env n).graph = .left)
    (hright : (env (n + 1)).graph = .right)
    (hliveRow :
      (package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy hwin
        one two).2.1 = .first) :
    package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin env
      (n + 2) := by
  rcases
      package.literalCombinedFreshPhaseActivatedSemanticTrace_strictLeft_pending_ready
        A strategy hwin env n one two hactivated hleft with
    ⟨oneNext, twoNext, hnext, hreadyOne, hreadyTwo⟩
  have hstep :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
          env ((n + 1) + 1) =
        ((package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin
          (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env (n + 1)).1 (env (n + 1)).inputOne).1,
        (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
          (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env (n + 1)).2 (env (n + 1)).inputTwo
          (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env (n + 1)).1 (env (n + 1)).inputOne).1) := by
    simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hright]
  rw [hnext] at hstep
  have honeShape :
      ∃ oneRecurrent : OneRecurrent A strategy hwin package,
        (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin
          (.inl oneNext) (env (n + 1)).inputOne).1 =
            .inr oneRecurrent := by
    simp [literalCombinedFreshPhaseActivatedNoRecvOne, hreadyOne,
      literalCombinedFreshRightSwitchNoRecvOne]
  have htwoShape :
      ∃ twoRecurrent : TwoRecurrent A strategy hwin package,
        (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
          (.inl twoNext) (env (n + 1)).inputTwo (.inl oneNext)
            (env (n + 1)).inputOne).1 = .inr twoRecurrent := by
    simp [literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyTwo,
      literalCombinedFreshRightSwitchRecvTwo]
  rcases honeShape with ⟨oneRecurrent, honeRecurrent⟩
  rcases htwoShape with ⟨twoRecurrent, htwoRecurrent⟩
  refine ⟨oneRecurrent, twoRecurrent, ?_⟩
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    hstep.trans (Prod.ext honeRecurrent htwoRecurrent)

/-- Persistent strict reversal cannot remain forever in the proof-side
pending classifier.  A right-to-left boundary safely arms the canonical row;
the next strict-right round then enters the recurrent summand. -/
theorem
    exists_literalCombinedFreshPhaseActivatedRecurrentAt_of_persistentReversal
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ n : Nat,
      package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin env
        n := by
  rcases hreversal.1 with ⟨noBothFrom, hnoBoth⟩
  rcases hreversal.exists_adjacent_right_left_after noBothFrom with
    ⟨n, hn, hright, hleft⟩
  have hselected :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_selected A strategy
      hwin env n
  have harmedAt :
      package.LiteralCombinedFreshPhaseActivatedArmedOrRecurrentAt A strategy
        hwin env (n + 2) := by
    rcases hselected.pending_or_recurrent A strategy hwin package with
      hpending | hrecurrent
    · rcases hpending with
      ⟨one, two, hone, htwo, _hstructural, _hreadyEq⟩
      have htrace :
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env n = (.inl one, .inl two) := by
        apply Prod.ext
        · exact hone
        · exact htwo
      exact
        package.literalCombinedFreshPhaseActivatedArmedOrRecurrentAt_of_pending_right_left
          A strategy hwin env n one two htrace hright hleft
    · rcases hrecurrent with ⟨one, two, hone, htwo⟩
      have hrecurrentAt :
          package.LiteralCombinedFreshPhaseActivatedRecurrentAt A strategy hwin
            env n := by
        refine ⟨one, two, ?_⟩
        apply Prod.ext
        · exact hone
        · exact htwo
      have hnext := hrecurrentAt.succ A strategy hwin package env n
      have hnextNext := hnext.succ A strategy hwin package env (n + 1)
      exact Or.inl (by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using hnextNext)
  rcases hreversal.2.2 (n + 2) with ⟨rightAt, hrightAt, hrightGraph⟩
  have hstrictSegment : ∀ k : Nat, k < rightAt - (n + 2) →
      (env ((n + 2) + k)).graph ≠ .both := by
    intro k _hk
    apply hnoBoth
    omega
  have harmedRight :=
    package.literalCombinedFreshPhaseActivatedArmedOrRecurrentAt_add_of_strict
      A strategy hwin env (n + 2) harmedAt (rightAt - (n + 2))
        hstrictSegment
  have hsum : (n + 2) + (rightAt - (n + 2)) = rightAt := by omega
  rw [hsum] at harmedRight
  exact ⟨rightAt + 1,
    package.literalCombinedFreshPhaseActivatedRecurrentAt_of_armedOrRecurrent_right
      A strategy hwin env rightAt harmedRight hrightGraph⟩

/-! ## Physical phase-live cut classification -/

/-- Strong proof-side classification of every strict-left round of the
actual phase-live semantic controller.  It exposes the pending pair before
the round, the exact pending pair after it, the retained literal stage (whose
fields name the selected child, row, and recurrent root), and the honest
table-input segment ending at that cut.  Thus a following strict-right round
has a finite selected member without changing the physical controller or
telling either endpoint who is the strict leader. -/
theorem literalCombinedFreshPhaseLive_strictLeft_cut_classified
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hleft : (env n).graph = .left) :
    ∃ one : OnePending A strategy hwin package,
      ∃ two : TwoPending A strategy hwin package,
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
            env n = (.inl one, .inl two) ∧
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
              (env n).inputOne two (env n).inputTwo).1.openControl
          let twoNext : TwoPending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
                (env n).inputTwo).1
          package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
              hwin env (n + 1) = (.inl oneNext, .inl twoNext) ∧
            package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A strategy
                hwin env (n + 1) oneNext twoNext ∧
              ∃ stage :
                  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
                    hwin package,
                (package.literalCombinedFreshOneReceiver A strategy hwin
                  oneNext.1 oneNext.2.1).2.2.2 = some stage := by
  have hsegmentCanonical :=
    package.literalCombinedFreshPhaseLiveRootSemanticTrace_tableSegment A
      strategy hwin env n
  rcases hsegmentCanonical with
    ⟨one, two, hone, htwo, hsegmentSelected, hcanonical⟩
  have hbefore :
      package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n = (.inl one, .inl two) := by
    apply Prod.ext
    · exact hone
    · exact htwo
  have hrootCanonical :=
    package.literalCombinedFreshPhaseLiveRootSemanticTrace_rootReachable A
      strategy hwin env n
  rw [hbefore] at hrootCanonical
  rcases hrootCanonical with
    ⟨rootOne, rootTwo, hrootOne, hrootTwo, hrootSelected, _hrootTrace⟩
  have hrootOneEq := Sum.inl.inj hrootOne
  have hrootTwoEq := Sum.inl.inj hrootTwo
  subst rootOne
  subst rootTwo
  let oneNext : OnePending A strategy hwin package :=
    (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
      (env n).inputOne two (env n).inputTwo).1.openControl
  let twoNext : TwoPending A strategy hwin package :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
        (env n).inputTwo).1
  have hafter :
      package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env (n + 1) = (.inl oneNext, .inl twoNext) := by
    have hstep :
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
            env (n + 1) =
          ((package.literalCombinedFreshPhaseLiveOpenRecvOne A strategy hwin
            (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
            (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
              hwin env n).1 (env n).inputOne
            (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
              hwin env n).2 (env n).inputTwo).1,
          (package.literalCombinedFreshPhaseLiveNoRecvTwo A strategy hwin
            (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
              hwin env n).2 (env n).inputTwo).1) := by
      simp only [literalCombinedFreshPhaseLiveRootSemanticTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hleft]
    rw [hbefore] at hstep
    simpa only [literalCombinedFreshPhaseLiveOpenRecvOne,
      literalCombinedFreshPhaseLiveNoRecvTwo, oneNext, twoNext] using hstep
  have hsegmentAfter :=
    package.literalCombinedFreshPhaseLiveTableRootSegmentAt_strictLeft A
      strategy hwin env n one two hsegmentSelected.1 hsegmentSelected.2
  obtain ⟨stage, hstage⟩ :=
    package.exists_literalCombinedFreshPhaseLiveRecvOne_open_stage_of_rootReachable
      A strategy hwin one two hrootSelected
        ((env n).inputOne, (env n).inputTwo)
  refine ⟨one, two, hbefore, hafter, hsegmentAfter, stage, ?_⟩
  simpa only [oneNext] using hstage

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
