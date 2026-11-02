/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedRecurrentReroot
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyControllerTrace
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingRelationalInvariant

/-!
# Physical selection for the phase-activated controller

The phase-activated semantic controller is wrapped in the acknowledged
open/closed-fork relay.  This file records the part of the runtime invariant
which does not require blind-output coherence: at every physical time the two
actual relays mutually select one semantic pair, and that pair is either
jointly pending or jointly recurrent.

This is the exact suffix interface needed by an all-`.both` audit.  In
particular, it does not pretend that an arbitrary selected recurrent pair is
the root of the independently selected hybrid common policy.  No executable
map receives a graph, orientation, hierarchy side, leader bit, history, or
semantic view.
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

private abbrev ActivatedController (package : Package A strategy hwin
    (initial := initial)) :=
  package.literalCombinedFreshPhaseActivatedController A strategy hwin

/-! ## Selection below the acknowledgement wrapper -/

/-- The pending-or-recurrent semantic invariant supplies the four relation
laws required by the generic acknowledged exact-close relay. -/
noncomputable def literalCombinedFreshPhaseActivatedSelectedRelationLaws
    (package : Package A strategy hwin (initial := initial)) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelationLaws
      (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
      (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
      (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
      (package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin) where
  initial :=
    package.literalCombinedFreshPhaseActivatedSelected_initial A strategy hwin
  strictRight := by
    intro one inputOne two inputTwo hselected
    exact hselected.strictRight A strategy hwin package (inputOne, inputTwo)
  strictLeft := by
    intro one inputOne two inputTwo hselected
    exact hselected.strictLeft A strategy hwin package (inputOne, inputTwo)
  both := by
    intro one inputOne two inputTwo hselected
    exact hselected.both A strategy hwin package (inputOne, inputTwo)

/-- The underlying acknowledged relays of the executable Mealy trace always
mutually select a jointly pending or jointly recurrent semantic pair. -/
theorem literalCombinedFreshPhaseActivatedSemanticControlTrace_selects
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelaysSatisfy
      (package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin)
      ((ActivatedController A strategy hwin package).semanticControlTrace env
        n).1
      ((ActivatedController A strategy hwin package).semanticControlTrace env
        n).2 := by
  intro n
  induction n with
  | zero =>
      exact (package.literalCombinedFreshPhaseActivatedSelectedRelationLaws A
        strategy hwin).initial_relays _ _ _ _ _ _ _ _
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            ActivatedController, literalCombinedFreshPhaseActivatedController,
            FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
            FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
            (FiniteAcknowledgedDelayedCarrier.ExactClosingRelaysSatisfy.strictRight
              (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy
                hwin)
              (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A
                strategy hwin)
              (package.literalCombinedFreshPhaseActivatedClose A strategy
                hwin)
              (package.LiteralCombinedFreshPhaseActivatedSelected A strategy
                hwin)
              (fun one inputOne two inputTwo hselected =>
                hselected.strictRight A strategy hwin package
                  (inputOne, inputTwo))
              ((ActivatedController A strategy hwin package
                ).semanticControlTrace env n).1
              ((ActivatedController A strategy hwin package
                ).semanticControlTrace env n).2
              (env n).inputOne (env n).inputTwo ih)
      | left =>
          simpa only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            ActivatedController, literalCombinedFreshPhaseActivatedController,
            FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
            FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
            (FiniteAcknowledgedDelayedCarrier.ExactClosingRelaysSatisfy.strictLeft
              (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy
                hwin)
              (package.literalCombinedFreshPhaseActivatedOpenRecvOne A
                strategy hwin)
              (package.literalCombinedFreshPhaseActivatedClose A strategy
                hwin)
              (package.LiteralCombinedFreshPhaseActivatedSelected A strategy
                hwin)
              (fun one inputOne two inputTwo hselected =>
                hselected.strictLeft A strategy hwin package
                  (inputOne, inputTwo))
              ((ActivatedController A strategy hwin package
                ).semanticControlTrace env n).1
              ((ActivatedController A strategy hwin package
                ).semanticControlTrace env n).2
              (env n).inputOne (env n).inputTwo ih)
      | both =>
          simpa only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            ActivatedController, literalCombinedFreshPhaseActivatedController,
            FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
            FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
            (FiniteAcknowledgedDelayedCarrier.ExactClosingRelaysSatisfy.both
              (package.literalCombinedFreshPhaseActivatedOpenRecvOne A
                strategy hwin)
              (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A
                strategy hwin)
              (package.literalCombinedFreshPhaseActivatedClose A strategy
                hwin)
              (package.LiteralCombinedFreshPhaseActivatedSelected A strategy
                hwin)
              (fun one inputOne two inputTwo hselected =>
                hselected.both A strategy hwin package (inputOne, inputTwo))
              ((ActivatedController A strategy hwin package
                ).semanticControlTrace env n).1
              ((ActivatedController A strategy hwin package
                ).semanticControlTrace env n).2
              (env n).inputOne (env n).inputTwo ih)

/-- Moore-facing form.  The generic trace projection removes only the stored
last outputs; the theorem above then identifies the selected semantic pair. -/
theorem literalCombinedFreshPhaseActivatedPhysicalState_selects
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let state := controller.globalMachine.globalStateTrace env n
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelaysSatisfy
      (package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin)
      state.1.1 state.2.1 := by
  dsimp only
  let mealy := ActivatedController A strategy hwin package
  have hprojection := mealy.mooreize_globalStateTrace_underlying env n
  have hselect :=
    package.literalCombinedFreshPhaseActivatedSemanticControlTrace_selects A
      strategy hwin env n
  change
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelaysSatisfy
      (package.LiteralCombinedFreshPhaseActivatedSelected A strategy hwin)
      ((mealy.mooreize).globalMachine.globalStateTrace env n).1.1
      ((mealy.mooreize).globalMachine.globalStateTrace env n).2.1
  change
    (((mealy.mooreize).globalMachine.globalStateTrace env n).1.1,
      ((mealy.mooreize).globalMachine.globalStateTrace env n).2.1) =
        mealy.semanticControlTrace env n at hprojection
  have hone :
      ((mealy.mooreize).globalMachine.globalStateTrace env n).1.1 =
        (mealy.semanticControlTrace env n).1 := by
    simpa only [Prod.fst] using congrArg Prod.fst hprojection
  have htwo :
      ((mealy.mooreize).globalMachine.globalStateTrace env n).2.1 =
        (mealy.semanticControlTrace env n).2 := by
    simpa only [Prod.snd] using congrArg Prod.snd hprojection
  rw [hone, htwo]
  exact hselect

/-- Exact runtime classification at an arbitrary suffix cut.  The recurrent
branch deliberately exposes an arbitrary selected recurrent pair: no reset to
the unrelated hybrid common-policy root is derivable from the controller. -/
theorem literalCombinedFreshPhaseActivatedPhysicalState_pending_or_recurrent
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let state := controller.globalMachine.globalStateTrace env n
    (∃ one two,
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        (.inl one) (.inl two)) ∨
    (∃ one two,
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        (.inr one) (.inr two)) := by
  dsimp only
  rcases package.literalCombinedFreshPhaseActivatedPhysicalState_selects A
      strategy hwin env n with
    ⟨actualOne, actualTwo, hselects, hselected⟩
  cases hselected with
  | pending one two _ _ => exact Or.inl ⟨one, two, hselects⟩
  | recurrent one two => exact Or.inr ⟨one, two, hselects⟩

/-! ## The exact simultaneous-round output seam -/

/-- On a simultaneous physical round, relay ambiguity does not affect the
current output: both receive handlers first resolve the same selected
semantic pair.  Unlike a no-receive equation, this needs no blind-output
coherence hypothesis. -/
theorem literalCombinedFreshPhaseActivatedPhysicalOutput_both_of_pairSelects
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (actualOne : OneControl A strategy hwin package)
    (actualTwo : TwoControl A strategy hwin package)
    (hgraph : (env n).graph = .both)
    (hselects :
      let controller :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin
      let state := controller.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        actualOne actualTwo) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let nextState := controller.globalMachine.globalStateTrace env (n + 1)
    (controller.globalOutputOne nextState,
      controller.globalOutputTwo nextState) =
      ((package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin
          actualOne (env n).inputOne actualTwo (env n).inputTwo).2,
        (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
          actualTwo (env n).inputTwo actualOne (env n).inputOne).2) := by
  let mealy := ActivatedController A strategy hwin package
  let controller := mealy.mooreize
  let state := controller.globalMachine.globalStateTrace env n
  change FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
    actualOne actualTwo at hselects
  change
    (controller.globalOutputOne
        (controller.globalMachine.globalStateTrace env (n + 1)),
      controller.globalOutputTwo
        (controller.globalMachine.globalStateTrace env (n + 1))) = _
  rcases hselects with ⟨hone, htwo⟩
  change
    FiniteAcknowledgedDelayedCarrier.resolvedControl
        state.1.1 state.2.1 =
      actualOne at hone
  change
    FiniteAcknowledgedDelayedCarrier.resolvedControl
        state.2.1 state.1.1 =
      actualTwo at htwo
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
  change
    (controller.outputOne
        (controller.advanceControls state (env n)).1,
      controller.outputTwo
        (controller.advanceControls state (env n)).2) = _
  simp only [FinitePairedPhysicalController.advanceControls, hgraph]
  rw [mealy.mooreize_recvOne_output, mealy.mooreize_recvTwo_output]
  change
    ((FiniteAcknowledgedDelayedCarrier.recvReforkMealy
        (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
          (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy
            hwin)
          (package.literalCombinedFreshPhaseActivatedClose A strategy hwin))
        state.1.1 (env n).inputOne state.2.1 (env n).inputTwo).2,
      (FiniteAcknowledgedDelayedCarrier.recvReforkMealy
        (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
          (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy
            hwin)
          (package.literalCombinedFreshPhaseActivatedClose A strategy hwin))
        state.2.1 (env n).inputTwo state.1.1 (env n).inputOne).2) = _
  simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy,
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne,
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo, hone, htwo]

/-- Recurrent specialization of the simultaneous-round output seam.  This is
the first exact letter of the arbitrary recurrent reroot; it is not, without
an additional state identification, a letter of the independently selected
hybrid forever-common word. -/
theorem literalCombinedFreshPhaseActivatedPhysicalOutput_both_recurrent
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hgraph : (env n).graph = .both)
    (hselects :
      let controller :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin
      let state := controller.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        (.inr one) (.inr two)) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let nextState := controller.globalMachine.globalStateTrace env (n + 1)
    (controller.globalOutputOne nextState,
      controller.globalOutputTwo nextState) =
      ((package.literalRightSeamTaggedRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).2,
        (package.literalRightSeamTaggedRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).2) := by
  simpa only [literalCombinedFreshPhaseActivatedOpenRecvOne,
    literalCombinedFreshPhaseActivatedOpenRecvTwo] using
    package.literalCombinedFreshPhaseActivatedPhysicalOutput_both_of_pairSelects
      A strategy hwin env n (.inr one) (.inr two) hgraph hselects

/-- The post-round physical relays select the exact joint close of the
pre-round selected semantic pair.  This is the state counterpart of the
receive-output theorem above. -/
theorem literalCombinedFreshPhaseActivatedPhysicalState_both_pairSelects_close
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (actualOne : OneControl A strategy hwin package)
    (actualTwo : TwoControl A strategy hwin package)
    (hgraph : (env n).graph = .both)
    (hselects :
      let controller :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin
      let state := controller.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        actualOne actualTwo) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let nextState := controller.globalMachine.globalStateTrace env (n + 1)
    FiniteAcknowledgedDelayedCarrier.PairSelects nextState.1.1 nextState.2.1
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin
        actualOne (env n).inputOne actualTwo (env n).inputTwo).1
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin
        actualOne (env n).inputOne actualTwo (env n).inputTwo).2 := by
  let mealy := ActivatedController A strategy hwin package
  let controller := mealy.mooreize
  let state := controller.globalMachine.globalStateTrace env n
  change FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
    actualOne actualTwo at hselects
  rcases hselects with ⟨hone, htwo⟩
  change FiniteAcknowledgedDelayedCarrier.resolvedControl state.1.1 state.2.1 =
    actualOne at hone
  change FiniteAcknowledgedDelayedCarrier.resolvedControl state.2.1 state.1.1 =
    actualTwo at htwo
  change FiniteAcknowledgedDelayedCarrier.PairSelects
    (controller.globalMachine.globalStateTrace env (n + 1)).1.1
    (controller.globalMachine.globalStateTrace env (n + 1)).2.1 _ _
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
  change FiniteAcknowledgedDelayedCarrier.PairSelects
    (controller.advanceControls state (env n)).1.1
    (controller.advanceControls state (env n)).2.1 _ _
  simp only [FinitePairedPhysicalController.advanceControls, hgraph]
  change FiniteAcknowledgedDelayedCarrier.PairSelects
    (FiniteAcknowledgedDelayedCarrier.recvReforkMealy
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedClose A strategy hwin))
      state.1.1 (env n).inputOne state.2.1 (env n).inputTwo).1
    (FiniteAcknowledgedDelayedCarrier.recvReforkMealy
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedClose A strategy hwin))
      state.2.1 (env n).inputTwo state.1.1 (env n).inputOne).1 _ _
  have hnext :=
    FiniteAcknowledgedDelayedCarrier.exactClosing_pairSelects_both
      (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
      state.1.1 state.2.1 (env n).inputOne (env n).inputTwo
  simpa only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy, hone, htwo]
    using hnext

/-- Recurrent specialization: one simultaneous physical round preserves the
selected recurrent pair and advances it by the literal tagged-kernel close. -/
theorem literalCombinedFreshPhaseActivatedPhysicalState_both_recurrent
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hgraph : (env n).graph = .both)
    (hselects :
      let controller :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin
      let state := controller.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        (.inr one) (.inr two)) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let nextState := controller.globalMachine.globalStateTrace env (n + 1)
    FiniteAcknowledgedDelayedCarrier.PairSelects nextState.1.1 nextState.2.1
      (.inr (package.literalRightSeamTaggedClose A strategy hwin one
        (env n).inputOne two (env n).inputTwo).1)
      (.inr (package.literalRightSeamTaggedClose A strategy hwin one
        (env n).inputOne two (env n).inputTwo).2) := by
  simpa only [literalCombinedFreshPhaseActivatedClose] using
    package.literalCombinedFreshPhaseActivatedPhysicalState_both_pairSelects_close
      A strategy hwin env n (.inr one) (.inr two) hgraph hselects

/-! ## All-simultaneous recurrent suffix -/

/-- Once an actual physical cut selects a recurrent pair, an all-`.both`
suffix selects exactly the re-rooted tagged semantic trace at every later
round.  The induction uses only simultaneous receive resolution; the invalid
global blind-fork law across the activation boundary is not assumed. -/
theorem literalCombinedFreshPhaseActivatedPhysicalState_recurrent_allBoth
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hall : ∀ k : Nat, (env (start + k)).graph = .both)
    (hselects :
      let controller :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin
      let state := controller.globalMachine.globalStateTrace env start
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        (.inr one) (.inr two)) : ∀ k : Nat,
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let state := controller.globalMachine.globalStateTrace env (start + k)
    let semantic :=
      package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one two
        (OmegaWord.drop env start) k
    FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
      (.inr semantic.1) (.inr semantic.2) := by
  intro k
  induction k with
  | zero =>
      simpa only [Nat.add_zero, literalRightSeamTaggedSemanticTraceFrom,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace] using
        hselects
  | succ k ih =>
      let semantic :=
        package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one
          two (OmegaWord.drop env start) k
      have hstep :=
        package.literalCombinedFreshPhaseActivatedPhysicalState_both_recurrent
          A strategy hwin env (start + k) semantic.1 semantic.2 (hall k) ih
      change
        FiniteAcknowledgedDelayedCarrier.PairSelects
          ((package.literalCombinedFreshPhaseActivatedPhysicalController A
            strategy hwin).globalMachine.globalStateTrace env
              (start + (k + 1))).1.1
          ((package.literalCombinedFreshPhaseActivatedPhysicalController A
            strategy hwin).globalMachine.globalStateTrace env
              (start + (k + 1))).2.1 _ _
      rw [show start + (k + 1) = (start + k) + 1 by omega]
      simpa only [semantic, literalRightSeamTaggedSemanticTraceFrom,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
        OmegaWord.drop, hall k, literalRightSeamTaggedClose] using hstep

/-- Literal physical word of the tagged semantic controller re-rooted at an
arbitrary recurrent pair. -/
noncomputable def literalRightSeamTaggedSemanticPhysicalWordFrom
    (package : Package A strategy hwin (initial := initial))
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne :=
        package.literalRightSeamTaggedSemanticOutputOneFrom A strategy hwin
          one two env n
      outputTwo :=
        package.literalRightSeamTaggedSemanticOutputTwoFrom A strategy hwin
          one two env n }

/-- Exact executable suffix equality in the recurrent all-`.both` case.  The
acknowledged relay has disappeared completely: the dropped Moore word is the
literal tagged semantic word re-rooted at the actually selected recurrent
pair.  What remains outside this theorem is an acceptance theorem for that
arbitrary reachable recurrent reroot; it cannot be replaced by the unrelated
hybrid forever-common root. -/
theorem literalCombinedFreshPhaseActivatedPhysicalWord_recurrent_allBoth
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hall : ∀ k : Nat, (env (start + k)).graph = .both)
    (hselects :
      let controller :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin
      let state := controller.globalMachine.globalStateTrace env start
      FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
        (.inr one) (.inr two)) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    OmegaWord.drop
        (controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env)
        start =
      package.literalRightSeamTaggedSemanticPhysicalWordFrom A strategy hwin
        one two (OmegaWord.drop env start) := by
  dsimp only
  funext k
  let semantic :=
    package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one two
      (OmegaWord.drop env start) k
  have hselected :=
    package.literalCombinedFreshPhaseActivatedPhysicalState_recurrent_allBoth
      A strategy hwin env start one two hall hselects k
  have houtput :=
    package.literalCombinedFreshPhaseActivatedPhysicalOutput_both_recurrent A
      strategy hwin env (start + k) semantic.1 semantic.2 (hall k) hselected
  have hsemanticOutput :
      let controller :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin
      ((controller.globalOutputOne
          (controller.globalMachine.globalStateTrace env (start + k + 1))),
        (controller.globalOutputTwo
          (controller.globalMachine.globalStateTrace env (start + k + 1)))) =
        (package.literalRightSeamTaggedSemanticOutputOneFrom A strategy hwin
            one two (OmegaWord.drop env start) k,
          package.literalRightSeamTaggedSemanticOutputTwoFrom A strategy hwin
            one two (OmegaWord.drop env start) k) := by
    simpa only [literalRightSeamTaggedSemanticOutputOneFrom,
      literalRightSeamTaggedSemanticOutputTwoFrom,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo,
      semantic, OmegaWord.drop, hall k] using houtput
  have hrecord := congrArg
    (fun output : Out₁ × Out₂ ↦
      RoundRecord.mk (env (start + k)).inputOne
        (env (start + k)).inputTwo (env (start + k)).graph output.1 output.2)
    hsemanticOutput
  simpa only [OmegaWord.drop,
    FiniteGlobalRoundMachine.globalMachineTraceWord,
    literalRightSeamTaggedSemanticPhysicalWordFrom] using hrecord

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
