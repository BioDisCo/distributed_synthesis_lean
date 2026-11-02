/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedPendingBridge
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedDelayedCarrierDuplicate
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingSemanticSelectionTrace
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachineReroot

/-!
# Re-rooting the phase-activated semantic suffix

Once the phase-activated semantic controller has entered its recurrent
summand, that summand is absorbing and its four local maps are literally the
exact tagged recurrent-kernel maps.  This file records the corresponding
suffix identity.  The selected tagged child remains inside the recurrent
controls; no endpoint is given a graph, hierarchy side, leader bit, history,
or semantic view.

This is deliberately the semantic-control layer.  The acknowledged physical
relay still needs a separate, finite flushing lemma before its Moore word can
be identified with this suffix: the activation receive temporarily stores an
open recurrent candidate beside a closed pending candidate.  Keeping that
boundary explicit prevents an invalid use of the ordinary blind-fork
invariant across the activation round.
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

private abbrev ActivatedPhysical (package : Package A strategy hwin
    (initial := initial)) :=
  package.literalCombinedFreshPhaseActivatedPhysicalController A strategy hwin

private abbrev TaggedKernel (package : Package A strategy hwin
    (initial := initial)) :=
  package.literalRightSeamTaggedExecutableKernel A strategy hwin

/-! ## The exact tagged recurrent semantic machine -/

/-- Joint close of the tagged recurrent maps.  In the recurrent summand the
open and simultaneous receive controls are the same tagged-kernel step. -/
noncomputable def literalRightSeamTaggedClose
    (package : Package A strategy hwin (initial := initial))
    (one : OneRecurrent A strategy hwin package) (own : In₁)
    (two : TwoRecurrent A strategy hwin package) (delivered : In₂) :
    OneRecurrent A strategy hwin package ×
      TwoRecurrent A strategy hwin package :=
  ((package.literalRightSeamTaggedRecvOne A strategy hwin one own two
      delivered).1,
    (package.literalRightSeamTaggedRecvTwo A strategy hwin two delivered one
      own).1)

/-- The tagged recurrent control pair before suffix round `k`, re-rooted at
an arbitrary already reached recurrent pair. -/
noncomputable def literalRightSeamTaggedSemanticTraceFrom
    (package : Package A strategy hwin (initial := initial))
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) : Nat →
      OneRecurrent A strategy hwin package ×
        TwoRecurrent A strategy hwin package :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace one two
    (package.literalRightSeamTaggedNoRecvOne A strategy hwin)
    (package.literalRightSeamTaggedNoRecvTwo A strategy hwin)
    (package.literalRightSeamTaggedRecvOne A strategy hwin)
    (package.literalRightSeamTaggedRecvTwo A strategy hwin)
    (package.literalRightSeamTaggedClose A strategy hwin) env

/-- Process-one output of the re-rooted tagged recurrent semantic word. -/
noncomputable def literalRightSeamTaggedSemanticOutputOneFrom
    (package : Package A strategy hwin (initial := initial))
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₁ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne one two
    (package.literalRightSeamTaggedNoRecvOne A strategy hwin)
    (package.literalRightSeamTaggedNoRecvTwo A strategy hwin)
    (package.literalRightSeamTaggedRecvOne A strategy hwin)
    (package.literalRightSeamTaggedRecvTwo A strategy hwin)
    (package.literalRightSeamTaggedClose A strategy hwin) env

/-- Process-two mirror output. -/
noncomputable def literalRightSeamTaggedSemanticOutputTwoFrom
    (package : Package A strategy hwin (initial := initial))
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) : Nat → Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo one two
    (package.literalRightSeamTaggedNoRecvOne A strategy hwin)
    (package.literalRightSeamTaggedNoRecvTwo A strategy hwin)
    (package.literalRightSeamTaggedRecvOne A strategy hwin)
    (package.literalRightSeamTaggedRecvTwo A strategy hwin)
    (package.literalRightSeamTaggedClose A strategy hwin) env

/-! ## Absorbing suffix identity -/

/-- After a recurrent cut, the complete activated semantic suffix is exactly
the same tagged recurrent run, with only the two `Sum.inr` embeddings left. -/
theorem literalCombinedFreshPhaseActivatedSemanticTrace_recurrent_reroot
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hstart :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env start = (.inr one, .inr two)) : ∀ k : Nat,
    package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env (start + k) =
      (.inr
          (package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one
            two (OmegaWord.drop env start) k).1,
        .inr
          (package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one
            two (OmegaWord.drop env start) k).2) := by
  intro k
  induction k with
  | zero => simpa [literalRightSeamTaggedSemanticTraceFrom] using hstart
  | succ k ih =>
      rw [show start + (k + 1) = (start + k) + 1 by omega]
      cases hgraph : (env (start + k)).graph with
      | right =>
          simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph]
          change
            ((package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy
                hwin
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).1
                (env (start + k)).inputOne).1,
              (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy
                hwin
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).2
                (env (start + k)).inputTwo
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).1
                (env (start + k)).inputOne).1) = _
          rw [ih]
          simp only [literalCombinedFreshPhaseActivatedNoRecvOne,
            literalCombinedFreshPhaseActivatedOpenRecvTwo]
          simp only [literalRightSeamTaggedSemanticTraceFrom,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            OmegaWord.drop, hgraph]
      | left =>
          simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph]
          change
            ((package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy
                hwin
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).1
                (env (start + k)).inputOne
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).2
                (env (start + k)).inputTwo).1,
              (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy
                hwin
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).2
                (env (start + k)).inputTwo).1) = _
          rw [ih]
          simp only [literalCombinedFreshPhaseActivatedOpenRecvOne,
            literalCombinedFreshPhaseActivatedNoRecvTwo]
          simp only [literalRightSeamTaggedSemanticTraceFrom,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            OmegaWord.drop, hgraph]
      | both =>
          simp only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph]
          change
            package.literalCombinedFreshPhaseActivatedClose A strategy hwin
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).1
                (env (start + k)).inputOne
                (package.literalCombinedFreshPhaseActivatedSemanticTrace A
                  strategy hwin env (start + k)).2
                (env (start + k)).inputTwo = _
          rw [ih]
          simp only [literalCombinedFreshPhaseActivatedClose]
          simp only [literalRightSeamTaggedSemanticTraceFrom,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            OmegaWord.drop, hgraph]
          simp only [literalRightSeamTaggedClose]

/-- The controls stored by the actual Moore controller select exactly the
canonical phase-activated semantic trace.  This specializes the generic
five-colour relay theorem; it does not use the graph as runtime information
and remains valid at the mixed activation fork. -/
theorem literalCombinedFreshPhaseActivatedPhysicalTrace_pairSelects
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let actual := ActivatedPhysical A strategy hwin package
    let state := actual.globalMachine.globalStateTrace env n
    let semantic :=
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n
    FiniteAcknowledgedDelayedCarrier.PairSelects
      state.1.1 state.2.1 semantic.1 semantic.2 := by
  simpa [ActivatedPhysical,
    literalCombinedFreshPhaseActivatedPhysicalController,
    literalCombinedFreshPhaseActivatedController,
    literalCombinedFreshPhaseActivatedSemanticTrace] using
    (FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController_globalStateTrace_pairSelects
        (.inl
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
        (.inl
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin))
        (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
        env n)

/-! ## Duplicate-relay physical suffix -/

/-- After both post-activation ambiguities have been flushed by a receive,
the acknowledged physical relay carries exactly one recurrent tagged control
at each endpoint.  A fork is allowed syntactically, but both of its candidates
must be that same recurrent control.  Stored Moore outputs are coupled
literally to the tagged kernel outputs. -/
structure LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt
    (package : Package A strategy hwin (initial := initial))
    (activated : (ActivatedPhysical A strategy hwin package).globalMachine.State)
    (tagged : (TaggedKernel A strategy hwin package).globalMachine.State) :
    Prop where
  one : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
    activated.1.1 (.inr tagged.1.1)
  two : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
    activated.2.1 (.inr tagged.2.1)
  outputOne : activated.1.2 = tagged.1.2
  outputTwo : activated.2.2 = tagged.2.2

/-- Related duplicate-recurrent states expose the same physical Moore
outputs. -/
theorem LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.outputs_eq
    (package : Package A strategy hwin (initial := initial))
    {activated :
      (ActivatedPhysical A strategy hwin package).globalMachine.State}
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (hrel :
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
        strategy hwin activated tagged) :
    ((ActivatedPhysical A strategy hwin package).globalOutputOne activated,
        (ActivatedPhysical A strategy hwin package).globalOutputTwo activated) =
      ((TaggedKernel A strategy hwin package).globalOutputOne tagged,
        (TaggedKernel A strategy hwin package).globalOutputTwo tagged) := by
  exact Prod.ext hrel.outputOne hrel.outputTwo

/-- In the recurrent summand, process one's exact-closing receive fork is
diagonal: ordinary and simultaneous receipt use the same tagged step. -/
theorem literalCombinedFreshPhaseActivatedRecvForkOne_recurrent
    (package : Package A strategy hwin (initial := initial))
    (one : OneRecurrent A strategy hwin package) (own : In₁)
    (two : TwoRecurrent A strategy hwin package) (delivered : In₂) :
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
        (.inr one) own (.inr two) delivered =
      let next := package.literalRightSeamTaggedRecvOne A strategy hwin one
        own two delivered
      (⟨.inr next.1, .inr next.1⟩, next.2) := by
  rfl

/-- Process-two mirror diagonal fork. -/
theorem literalCombinedFreshPhaseActivatedRecvForkTwo_recurrent
    (package : Package A strategy hwin (initial := initial))
    (two : TwoRecurrent A strategy hwin package) (own : In₂)
    (one : OneRecurrent A strategy hwin package) (delivered : In₁) :
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
        (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
        (.inr two) own (.inr one) delivered =
      let next := package.literalRightSeamTaggedRecvTwo A strategy hwin two
        own one delivered
      (⟨.inr next.1, .inr next.1⟩, next.2) := by
  rfl

/-- A process-one receive flushes an arbitrary old relay presentation as soon
as the two relays select a recurrent semantic pair.  The newly installed fork
is diagonal, so no pre-existing duplicate hypothesis is needed. -/
theorem literalCombinedFreshPhaseActivatedRecvOne_duplicate_of_pairSelects
    (package : Package A strategy hwin (initial := initial))
    (oneRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).OneControl)
    (twoRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).TwoControl)
    (one : OneRecurrent A strategy hwin package) (own : In₁)
    (two : TwoRecurrent A strategy hwin package) (delivered : In₂)
    (hselects : FiniteAcknowledgedDelayedCarrier.PairSelects
      oneRelay twoRelay (.inr one) (.inr two)) :
    let next := package.literalRightSeamTaggedRecvOne A strategy hwin one own
      two delivered
    FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
        ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
          ).recvOne oneRelay own twoRelay delivered).1 (.inr next.1) ∧
      ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).recvOne oneRelay own twoRelay delivered).2 = next.2 := by
  let transition :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
  let next := package.literalRightSeamTaggedRecvOne A strategy hwin one own
    two delivered
  have htransition :
      transition (.inr one) own (.inr two) delivered =
        (⟨.inr next.1, .inr next.1⟩, next.2) :=
    package.literalCombinedFreshPhaseActivatedRecvForkOne_recurrent A strategy
      hwin one own two delivered
  simpa [literalCombinedFreshPhaseActivatedController,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
    (FiniteAcknowledgedDelayedCarrier.carriesDuplicate_recvReforkMealy_of_pairSelects
      transition oneRelay own
        twoRelay delivered (.inr one) (.inr two) (.inr next.1) next.2
        hselects htransition)

/-- Process-two mirror of the arbitrary-presentation flushing receive. -/
theorem literalCombinedFreshPhaseActivatedRecvTwo_duplicate_of_pairSelects
    (package : Package A strategy hwin (initial := initial))
    (twoRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).TwoControl)
    (oneRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).OneControl)
    (two : TwoRecurrent A strategy hwin package) (own : In₂)
    (one : OneRecurrent A strategy hwin package) (delivered : In₁)
    (hselects : FiniteAcknowledgedDelayedCarrier.PairSelects
      twoRelay oneRelay (.inr two) (.inr one)) :
    let next := package.literalRightSeamTaggedRecvTwo A strategy hwin two own
      one delivered
    FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
        ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
          ).recvTwo twoRelay own oneRelay delivered).1 (.inr next.1) ∧
      ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).recvTwo twoRelay own oneRelay delivered).2 = next.2 := by
  let transition :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
  let next := package.literalRightSeamTaggedRecvTwo A strategy hwin two own
    one delivered
  have htransition :
      transition (.inr two) own (.inr one) delivered =
        (⟨.inr next.1, .inr next.1⟩, next.2) :=
    package.literalCombinedFreshPhaseActivatedRecvForkTwo_recurrent A strategy
      hwin two own one delivered
  simpa [literalCombinedFreshPhaseActivatedController,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
    (FiniteAcknowledgedDelayedCarrier.carriesDuplicate_recvReforkMealy_of_pairSelects
      transition twoRelay own
        oneRelay delivered (.inr two) (.inr one) (.inr next.1) next.2
        hselects htransition)

/-! ## The two-receive physical flush -/

/-- Exact output of the two-receive flush.  Besides the duplicate relation it
records that the tagged state is not freshly chosen: it is literally the
state reached by running the tagged recurrent kernel for the same two rounds
from the selected recurrent controls and the actual stored outputs.  This is
the composition socket for the same-child recurrent invariant. -/
structure LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package) where
  left : (env n).graph = .left
  right : (env (n + 1)).graph = .right
  tagged : (TaggedKernel A strategy hwin package).globalMachine.State
  duplicate :
    package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
      strategy hwin
      ((ActivatedPhysical A strategy hwin package).globalMachine.globalStateTrace
        env (n + 2))
      tagged
  descendant :
    tagged =
      let actual := ActivatedPhysical A strategy hwin package
      let state := actual.globalMachine.globalStateTrace env n
      let taggedStart :
          (TaggedKernel A strategy hwin package).globalMachine.State :=
        ((one, state.1.2), (two, state.2.2))
      ((TaggedKernel A strategy hwin package).globalMachine.reroot taggedStart
        ).globalStateTrace (OmegaWord.drop env n) 2

/-- If the semantic controller is recurrent before an adjacent strict-left /
strict-right pair, then two physical rounds suffice to flush both relay
candidates.  The resulting actual Moore state is related to one literal
tagged-kernel state, with the actual stored outputs retained verbatim.

The adjacent pair is a proof-side fact about the environment.  Neither local
transition is told that it is the first or second half of the pair. -/
theorem
    nonempty_literalCombinedFreshPhaseActivatedLeftRightFlushWitness
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (hleft : (env n).graph = .left)
    (hright : (env (n + 1)).graph = .right) :
    Nonempty
      (package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two) := by
  let actual := ActivatedPhysical A strategy hwin package
  let state₀ := actual.globalMachine.globalStateTrace env n
  let state₁ := actual.globalMachine.globalStateTrace env (n + 1)
  let state₂ := actual.globalMachine.globalStateTrace env (n + 2)
  let one₁ :=
    (package.literalRightSeamTaggedRecvOne A strategy hwin one
      (env n).inputOne two (env n).inputTwo).1
  let two₁ :=
    (package.literalRightSeamTaggedNoRecvTwo A strategy hwin two
      (env n).inputTwo).1
  let one₂ :=
    (package.literalRightSeamTaggedNoRecvOne A strategy hwin one₁
      (env (n + 1)).inputOne).1
  let two₂ :=
    (package.literalRightSeamTaggedRecvTwo A strategy hwin two₁
      (env (n + 1)).inputTwo one₁ (env (n + 1)).inputOne).1
  have hsemantic₁ :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env (n + 1) = (.inr one₁, .inr two₁) := by
    have hreroot :=
      package.literalCombinedFreshPhaseActivatedSemanticTrace_recurrent_reroot
        A strategy hwin env n one two hsemantic 1
    simpa [literalRightSeamTaggedSemanticTraceFrom,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hleft,
      one₁, two₁] using hreroot
  have hselect₀ :=
    package.literalCombinedFreshPhaseActivatedPhysicalTrace_pairSelects A
      strategy hwin env n
  dsimp only at hselect₀
  rw [hsemantic] at hselect₀
  have hone₁Raw :=
    package.literalCombinedFreshPhaseActivatedRecvOne_duplicate_of_pairSelects
      A strategy hwin state₀.1.1 state₀.2.1 one (env n).inputOne two
        (env n).inputTwo hselect₀
  have hone₁ :
      FiniteAcknowledgedDelayedCarrier.CarriesDuplicate state₁.1.1
        (.inr one₁) := by
    dsimp only [state₁]
    rw [show n + 1 = Nat.succ n by omega,
      FiniteGlobalRoundMachine.globalStateTrace_succ]
    simpa [state₀, actual, ActivatedPhysical,
      literalCombinedFreshPhaseActivatedPhysicalController,
      FinitePairedPhysicalController.advanceControls, hleft] using
      hone₁Raw.1
  have hselect₁ :=
    package.literalCombinedFreshPhaseActivatedPhysicalTrace_pairSelects A
      strategy hwin env (n + 1)
  dsimp only at hselect₁
  rw [hsemantic₁] at hselect₁
  have hone₂Raw :=
    FiniteAcknowledgedDelayedCarrier.carriesDuplicate_noRecvMealy
      (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin)
      state₁.1.1 (.inr one₁) (env (n + 1)).inputOne hone₁
  have htwo₂Raw :=
    package.literalCombinedFreshPhaseActivatedRecvTwo_duplicate_of_pairSelects
      A strategy hwin state₁.2.1 state₁.1.1 two₁
        (env (n + 1)).inputTwo one₁ (env (n + 1)).inputOne
        ⟨hselect₁.2, hselect₁.1⟩
  have hone₂ :
      FiniteAcknowledgedDelayedCarrier.CarriesDuplicate state₂.1.1
        (.inr one₂) := by
    dsimp only [state₂]
    rw [show n + 2 = Nat.succ (n + 1) by omega,
      FiniteGlobalRoundMachine.globalStateTrace_succ]
    simpa [state₁, actual, ActivatedPhysical,
      literalCombinedFreshPhaseActivatedPhysicalController,
      FinitePairedPhysicalController.advanceControls, hright] using
      hone₂Raw.1
  have htwo₂ :
      FiniteAcknowledgedDelayedCarrier.CarriesDuplicate state₂.2.1
        (.inr two₂) := by
    dsimp only [state₂]
    rw [show n + 2 = Nat.succ (n + 1) by omega,
      FiniteGlobalRoundMachine.globalStateTrace_succ]
    simpa [state₁, actual, ActivatedPhysical,
      literalCombinedFreshPhaseActivatedPhysicalController,
      FinitePairedPhysicalController.advanceControls, hright] using
      htwo₂Raw.1
  let kernel := TaggedKernel A strategy hwin package
  let taggedStart : kernel.globalMachine.State :=
    ((one, state₀.1.2), (two, state₀.2.2))
  let taggedState :=
    (kernel.globalMachine.reroot taggedStart).globalStateTrace
      (OmegaWord.drop env n) 2
  have htaggedOne : taggedState.1.1 = one₂ := by
    simp [taggedState, taggedStart, kernel, TaggedKernel,
      FiniteGlobalRoundMachine.globalStateTrace_succ,
      FiniteGlobalRoundMachine.reroot,
      ProfiledRawJointLeaderFreeKernel.globalMachine,
      FinitePairedPhysicalController.advanceControls, OmegaWord.drop, hleft,
      hright, literalRightSeamTaggedRecvOne,
      literalRightSeamTaggedNoRecvOne, one₁, one₂]
  have htaggedTwo : taggedState.2.1 = two₂ := by
    simp [taggedState, taggedStart, kernel, TaggedKernel,
      FiniteGlobalRoundMachine.globalStateTrace_succ,
      FiniteGlobalRoundMachine.reroot,
      ProfiledRawJointLeaderFreeKernel.globalMachine,
      FinitePairedPhysicalController.advanceControls, OmegaWord.drop, hleft,
      hright, literalRightSeamTaggedRecvOne,
      literalRightSeamTaggedNoRecvTwo,
      literalRightSeamTaggedRecvTwo, one₁, two₁, two₂]
  have htaggedOutputOne :
      taggedState.1.2 =
        (package.literalRightSeamTaggedNoRecvOne A strategy hwin one₁
          (env (n + 1)).inputOne).2 := by
    simp [taggedState, taggedStart, kernel, TaggedKernel,
      FiniteGlobalRoundMachine.globalStateTrace_succ,
      FiniteGlobalRoundMachine.reroot,
      ProfiledRawJointLeaderFreeKernel.globalMachine,
      FinitePairedPhysicalController.advanceControls, OmegaWord.drop, hleft,
      hright, literalRightSeamTaggedRecvOne,
      literalRightSeamTaggedNoRecvOne, one₁]
  have htaggedOutputTwo :
      taggedState.2.2 =
        (package.literalRightSeamTaggedRecvTwo A strategy hwin two₁
          (env (n + 1)).inputTwo one₁ (env (n + 1)).inputOne).2 := by
    simp [taggedState, taggedStart, kernel, TaggedKernel,
      FiniteGlobalRoundMachine.globalStateTrace_succ,
      FiniteGlobalRoundMachine.reroot,
      ProfiledRawJointLeaderFreeKernel.globalMachine,
      FinitePairedPhysicalController.advanceControls, OmegaWord.drop, hleft,
      hright, literalRightSeamTaggedRecvOne,
      literalRightSeamTaggedNoRecvTwo,
      literalRightSeamTaggedRecvTwo, one₁, two₁]
  have honeOutput₂ :
      state₂.1.2 =
        (package.literalRightSeamTaggedNoRecvOne A strategy hwin one₁
          (env (n + 1)).inputOne).2 := by
    dsimp only [state₂]
    rw [show n + 2 = Nat.succ (n + 1) by omega,
      FiniteGlobalRoundMachine.globalStateTrace_succ]
    simpa [state₁, actual, ActivatedPhysical,
      literalCombinedFreshPhaseActivatedPhysicalController,
      FinitePairedPhysicalController.advanceControls, hright,
      literalCombinedFreshPhaseActivatedNoRecvOne] using hone₂Raw.2
  have htwoOutput₂ :
      state₂.2.2 =
        (package.literalRightSeamTaggedRecvTwo A strategy hwin two₁
          (env (n + 1)).inputTwo one₁ (env (n + 1)).inputOne).2 := by
    dsimp only [state₂]
    rw [show n + 2 = Nat.succ (n + 1) by omega,
      FiniteGlobalRoundMachine.globalStateTrace_succ]
    simpa [state₁, actual, ActivatedPhysical,
      literalCombinedFreshPhaseActivatedPhysicalController,
      FinitePairedPhysicalController.advanceControls, hright] using
      htwo₂Raw.2
  refine ⟨⟨hleft, hright, taggedState, ⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · simpa [htaggedOne] using hone₂
  · simpa [htaggedTwo] using htwo₂
  · exact honeOutput₂.trans htaggedOutputOne.symm
  · exact htwoOutput₂.trans htaggedOutputTwo.symm
  · rfl

/-- Existential projection of the exact flush witness, retained as the small
interface used by the generic duplicate-suffix simulation. -/
theorem
    exists_literalCombinedFreshPhaseActivatedDuplicateRecurrentAt_after_left_right
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (hleft : (env n).graph = .left)
    (hright : (env (n + 1)).graph = .right) :
    ∃ tagged : (TaggedKernel A strategy hwin package).globalMachine.State,
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
        strategy hwin
        ((ActivatedPhysical A strategy hwin package).globalMachine.globalStateTrace
          env (n + 2))
        tagged := by
  obtain ⟨flush⟩ :=
    package.nonempty_literalCombinedFreshPhaseActivatedLeftRightFlushWitness A
      strategy hwin env n one two hsemantic hleft hright
  exact ⟨flush.tagged, flush.duplicate⟩

/-- Persistent strict reversal eventually supplies the full two-receive flush
witness, not merely its duplicate-relay projection.  In particular the
tagged state retained by this theorem is definitionally the two-round
descendant of the recurrent state before the adjacent left/right pair. -/
theorem
    exists_literalCombinedFreshPhaseActivatedLeftRightFlushWitness_of_persistentReversal
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ n : Nat,
      ∃ one : OneRecurrent A strategy hwin package,
        ∃ two : TwoRecurrent A strategy hwin package,
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
                hwin env n = (.inr one, .inr two) ∧
            Nonempty
              (package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness
                A strategy hwin env n one two) := by
  rcases
      package.exists_literalCombinedFreshPhaseActivatedRecurrentAt_of_persistentReversal
        A strategy hwin env hreversal with
    ⟨recurrentStart, one, two, hstart⟩
  rcases hreversal.exists_adjacent_left_right_after recurrentStart with
    ⟨n, hn, hleft, hright⟩
  let oneAt :=
    (package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one two
      (OmegaWord.drop env recurrentStart) (n - recurrentStart)).1
  let twoAt :=
    (package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one two
      (OmegaWord.drop env recurrentStart) (n - recurrentStart)).2
  have hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr oneAt, .inr twoAt) := by
    have hreroot :=
      package.literalCombinedFreshPhaseActivatedSemanticTrace_recurrent_reroot
        A strategy hwin env recurrentStart one two hstart
          (n - recurrentStart)
    have hsum : recurrentStart + (n - recurrentStart) = n := by omega
    rw [hsum] at hreroot
    simpa [oneAt, twoAt] using hreroot
  exact ⟨n, oneAt, twoAt, hsemantic,
    package.nonempty_literalCombinedFreshPhaseActivatedLeftRightFlushWitness A
      strategy hwin env n oneAt twoAt hsemantic hleft hright⟩

/-- The recurrent flush can be chosen beyond the last simultaneous round.
Consequently the complete fixed-child suffix after the two-round relay flush
is all-strict.  This is the form consumed by the persistent Unit carrier: its
`no .both` premise no longer has to be supplied independently at the handoff. -/
theorem
    exists_literalCombinedFreshPhaseActivatedLeftRightFlushWitness_with_noBothSuffix_of_persistentReversal
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ n : Nat,
      ∃ one : OneRecurrent A strategy hwin package,
        ∃ two : TwoRecurrent A strategy hwin package,
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
                hwin env n = (.inr one, .inr two) ∧
            Nonempty
              (package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness
                A strategy hwin env n one two) ∧
            ∀ j : Nat, (env (n + 2 + j)).graph ≠ .both := by
  rcases hreversal.1 with ⟨noBothFrom, hnoBoth⟩
  rcases
      package.exists_literalCombinedFreshPhaseActivatedRecurrentAt_of_persistentReversal
        A strategy hwin env hreversal with
    ⟨recurrentStart, one, two, hstart⟩
  rcases hreversal.exists_adjacent_left_right_after
      (max recurrentStart noBothFrom) with
    ⟨n, hn, hleft, hright⟩
  let oneAt :=
    (package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one two
      (OmegaWord.drop env recurrentStart) (n - recurrentStart)).1
  let twoAt :=
    (package.literalRightSeamTaggedSemanticTraceFrom A strategy hwin one two
      (OmegaWord.drop env recurrentStart) (n - recurrentStart)).2
  have hrecurrentLe : recurrentStart ≤ n := by omega
  have hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr oneAt, .inr twoAt) := by
    have hreroot :=
      package.literalCombinedFreshPhaseActivatedSemanticTrace_recurrent_reroot
        A strategy hwin env recurrentStart one two hstart
          (n - recurrentStart)
    have hsum : recurrentStart + (n - recurrentStart) = n := by omega
    rw [hsum] at hreroot
    simpa [oneAt, twoAt] using hreroot
  refine ⟨n, oneAt, twoAt, hsemantic,
    package.nonempty_literalCombinedFreshPhaseActivatedLeftRightFlushWitness A
      strategy hwin env n oneAt twoAt hsemantic hleft hright, ?_⟩
  intro j
  apply hnoBoth
  omega

/-- Persistent strict reversal supplies both ingredients of the physical
flush: a semantic recurrent cut and, after that cut, an adjacent left/right
receive pair.  Hence the actual acknowledged controller eventually reaches
the exact duplicate-recurrent simulation relation. -/
theorem
    exists_literalCombinedFreshPhaseActivatedDuplicateRecurrentAt_of_persistentReversal
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ start : Nat,
      ∃ tagged : (TaggedKernel A strategy hwin package).globalMachine.State,
        package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
          strategy hwin
          ((ActivatedPhysical A strategy hwin package).globalMachine.globalStateTrace
            env start)
          tagged := by
  rcases
      package.exists_literalCombinedFreshPhaseActivatedLeftRightFlushWitness_of_persistentReversal
        A strategy hwin env hreversal with
    ⟨n, one, two, _hsemantic, ⟨flush⟩⟩
  exact ⟨n + 2, flush.tagged, flush.duplicate⟩

/-- A blind process-one step preserves a duplicate recurrent relay and is
exactly the tagged-kernel no-receive step, including its output. -/
theorem literalCombinedFreshPhaseActivatedNoRecvOne_duplicate
    (package : Package A strategy hwin (initial := initial))
    (relay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).OneControl)
    (one : OneRecurrent A strategy hwin package) (input : In₁)
    (hduplicate : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate relay
      (.inr one)) :
    let next := package.literalRightSeamTaggedNoRecvOne A strategy hwin one
      input
    FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
        ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
          ).noRecvOne relay input).1 (.inr next.1) ∧
      ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).noRecvOne relay input).2 = next.2 := by
  let hstep :=
    FiniteAcknowledgedDelayedCarrier.carriesDuplicate_noRecvMealy
      (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin)
      relay (.inr one) input hduplicate
  simpa [literalCombinedFreshPhaseActivatedController,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController,
    literalCombinedFreshPhaseActivatedNoRecvOne] using hstep

/-- Process-two no-receive mirror. -/
theorem literalCombinedFreshPhaseActivatedNoRecvTwo_duplicate
    (package : Package A strategy hwin (initial := initial))
    (relay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).TwoControl)
    (two : TwoRecurrent A strategy hwin package) (input : In₂)
    (hduplicate : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate relay
      (.inr two)) :
    let next := package.literalRightSeamTaggedNoRecvTwo A strategy hwin two
      input
    FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
        ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
          ).noRecvTwo relay input).1 (.inr next.1) ∧
      ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).noRecvTwo relay input).2 = next.2 := by
  let hstep :=
    FiniteAcknowledgedDelayedCarrier.carriesDuplicate_noRecvMealy
      (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin)
      relay (.inr two) input hduplicate
  simpa [literalCombinedFreshPhaseActivatedController,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController,
    literalCombinedFreshPhaseActivatedNoRecvTwo] using hstep

/-- A receive by process one flushes all old relay metadata and installs a
diagonal recurrent fork.  Resolution is harmless because both old carriers
already duplicate their tagged controls. -/
theorem literalCombinedFreshPhaseActivatedRecvOne_duplicate
    (package : Package A strategy hwin (initial := initial))
    (oneRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).OneControl)
    (twoRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).TwoControl)
    (one : OneRecurrent A strategy hwin package) (own : In₁)
    (two : TwoRecurrent A strategy hwin package) (delivered : In₂)
    (hone : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate oneRelay
      (.inr one))
    (htwo : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate twoRelay
      (.inr two)) :
    let next := package.literalRightSeamTaggedRecvOne A strategy hwin one own
      two delivered
    FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
        ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
          ).recvOne oneRelay own twoRelay delivered).1 (.inr next.1) ∧
      ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).recvOne oneRelay own twoRelay delivered).2 = next.2 := by
  have hresolveOne :=
    FiniteAcknowledgedDelayedCarrier.resolvedControl_eq_of_carriesDuplicate
      oneRelay twoRelay (.inr one) hone
  have hresolveTwo :=
    FiniteAcknowledgedDelayedCarrier.resolvedControl_eq_of_carriesDuplicate
      twoRelay oneRelay (.inr two) htwo
  let transition :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
  let next := package.literalRightSeamTaggedRecvOne A strategy hwin one own
    two delivered
  have htransition :
      transition
          (FiniteAcknowledgedDelayedCarrier.resolvedControl oneRelay twoRelay)
          own
          (FiniteAcknowledgedDelayedCarrier.resolvedControl twoRelay oneRelay)
          delivered =
        (⟨.inr next.1, .inr next.1⟩, next.2) := by
    rw [hresolveOne, hresolveTwo]
    exact package.literalCombinedFreshPhaseActivatedRecvForkOne_recurrent A
      strategy hwin one own two delivered
  have hduplicate :=
    FiniteAcknowledgedDelayedCarrier.carriesDuplicate_recvReforkMealy
      transition oneRelay own twoRelay delivered (.inr next.1)
        (congrArg Prod.fst htransition)
  have houtput :
      (FiniteAcknowledgedDelayedCarrier.recvReforkMealy transition oneRelay own
        twoRelay delivered).2 = next.2 := by
    simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
    exact congrArg Prod.snd htransition
  exact ⟨hduplicate, houtput⟩

/-- Process-two receive mirror. -/
theorem literalCombinedFreshPhaseActivatedRecvTwo_duplicate
    (package : Package A strategy hwin (initial := initial))
    (twoRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).TwoControl)
    (oneRelay :
      (package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).OneControl)
    (two : TwoRecurrent A strategy hwin package) (own : In₂)
    (one : OneRecurrent A strategy hwin package) (delivered : In₁)
    (htwo : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate twoRelay
      (.inr two))
    (hone : FiniteAcknowledgedDelayedCarrier.CarriesDuplicate oneRelay
      (.inr one)) :
    let next := package.literalRightSeamTaggedRecvTwo A strategy hwin two own
      one delivered
    FiniteAcknowledgedDelayedCarrier.CarriesDuplicate
        ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
          ).recvTwo twoRelay own oneRelay delivered).1 (.inr next.1) ∧
      ((package.literalCombinedFreshPhaseActivatedController A strategy hwin
        ).recvTwo twoRelay own oneRelay delivered).2 = next.2 := by
  have hresolveTwo :=
    FiniteAcknowledgedDelayedCarrier.resolvedControl_eq_of_carriesDuplicate
      twoRelay oneRelay (.inr two) htwo
  have hresolveOne :=
    FiniteAcknowledgedDelayedCarrier.resolvedControl_eq_of_carriesDuplicate
      oneRelay twoRelay (.inr one) hone
  let transition :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin)
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin)
  let next := package.literalRightSeamTaggedRecvTwo A strategy hwin two own
    one delivered
  have htransition :
      transition
          (FiniteAcknowledgedDelayedCarrier.resolvedControl twoRelay oneRelay)
          own
          (FiniteAcknowledgedDelayedCarrier.resolvedControl oneRelay twoRelay)
          delivered =
        (⟨.inr next.1, .inr next.1⟩, next.2) := by
    rw [hresolveTwo, hresolveOne]
    exact package.literalCombinedFreshPhaseActivatedRecvForkTwo_recurrent A
      strategy hwin two own one delivered
  have hduplicate :=
    FiniteAcknowledgedDelayedCarrier.carriesDuplicate_recvReforkMealy
      transition twoRelay own oneRelay delivered (.inr next.1)
        (congrArg Prod.fst htransition)
  have houtput :
      (FiniteAcknowledgedDelayedCarrier.recvReforkMealy transition twoRelay own
        oneRelay delivered).2 = next.2 := by
    simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
    exact congrArg Prod.snd htransition
  exact ⟨hduplicate, houtput⟩

/-- The duplicate-recurrent relation is an exact one-round simulation of the
actual acknowledged physical controller by the tagged recurrent kernel. -/
theorem LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.advanceControls
    (package : Package A strategy hwin (initial := initial))
    {activated :
      (ActivatedPhysical A strategy hwin package).globalMachine.State}
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (hrel :
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
        strategy hwin activated tagged)
    (round : EnvironmentRound In₁ In₂) :
    package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A strategy
      hwin
      ((ActivatedPhysical A strategy hwin package).advanceControls activated
        round)
      ((TaggedKernel A strategy hwin package).physicalController.advanceControls
        tagged round) := by
  rcases activated with ⟨⟨oneRelay, oneOutput⟩, ⟨twoRelay, twoOutput⟩⟩
  rcases tagged with ⟨⟨one, taggedOneOutput⟩, ⟨two, taggedTwoOutput⟩⟩
  rcases hrel with ⟨hone, htwo, honeOutput, htwoOutput⟩
  cases round with
  | mk inputOne inputTwo graph =>
      cases graph with
      | left =>
          have honeNext :=
            package.literalCombinedFreshPhaseActivatedRecvOne_duplicate A
              strategy hwin oneRelay twoRelay one inputOne two inputTwo hone
                htwo
          have htwoNext :=
            package.literalCombinedFreshPhaseActivatedNoRecvTwo_duplicate A
              strategy hwin twoRelay two inputTwo htwo
          simpa [FinitePairedPhysicalController.advanceControls,
            literalCombinedFreshPhaseActivatedPhysicalController,
            FinitePairedMealyController.mooreize,
            ProfiledRawJointLeaderFreeKernel.physicalController,
            literalRightSeamTaggedNoRecvTwo,
            literalRightSeamTaggedRecvOne] using
            (LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.mk
              honeNext.1 htwoNext.1 honeNext.2 htwoNext.2)
      | right =>
          have honeNext :=
            package.literalCombinedFreshPhaseActivatedNoRecvOne_duplicate A
              strategy hwin oneRelay one inputOne hone
          have htwoNext :=
            package.literalCombinedFreshPhaseActivatedRecvTwo_duplicate A
              strategy hwin twoRelay oneRelay two inputTwo one inputOne htwo
                hone
          simpa [FinitePairedPhysicalController.advanceControls,
            literalCombinedFreshPhaseActivatedPhysicalController,
            FinitePairedMealyController.mooreize,
            ProfiledRawJointLeaderFreeKernel.physicalController,
            literalRightSeamTaggedNoRecvOne,
            literalRightSeamTaggedRecvTwo] using
            (LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.mk
              honeNext.1 htwoNext.1 honeNext.2 htwoNext.2)
      | both =>
          have honeNext :=
            package.literalCombinedFreshPhaseActivatedRecvOne_duplicate A
              strategy hwin oneRelay twoRelay one inputOne two inputTwo hone
                htwo
          have htwoNext :=
            package.literalCombinedFreshPhaseActivatedRecvTwo_duplicate A
              strategy hwin twoRelay oneRelay two inputTwo one inputOne htwo
                hone
          simpa [FinitePairedPhysicalController.advanceControls,
            literalCombinedFreshPhaseActivatedPhysicalController,
            FinitePairedMealyController.mooreize,
            ProfiledRawJointLeaderFreeKernel.physicalController,
            literalRightSeamTaggedRecvOne,
            literalRightSeamTaggedRecvTwo] using
            (LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.mk
              honeNext.1 htwoNext.1 honeNext.2 htwoNext.2)

/-- The one-round simulation iterates on every graph sequence. -/
theorem
    LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.globalStateTrace
    (package : Package A strategy hwin (initial := initial))
    (activated :
      (ActivatedPhysical A strategy hwin package).globalMachine.State)
    (tagged : (TaggedKernel A strategy hwin package).globalMachine.State)
    (hrel :
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
        strategy hwin activated tagged)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A strategy
      hwin
      (((ActivatedPhysical A strategy hwin package).globalMachine.reroot
        activated).globalStateTrace env n)
      (((TaggedKernel A strategy hwin package).globalMachine.reroot tagged
        ).globalStateTrace env n) := by
  intro n
  induction n with
  | zero =>
      simpa [FiniteGlobalRoundMachine.reroot] using hrel
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
        FiniteGlobalRoundMachine.globalStateTrace_succ]
      simpa [FinitePairedPhysicalController.globalMachine,
        FiniteGlobalRoundMachine.reroot,
        ProfiledRawJointLeaderFreeKernel.globalMachine] using
        ih.advanceControls A strategy hwin package (env n)

/-- Re-rooting at duplicate recurrent relay states produces literally the
same physical word as re-rooting the exact tagged recurrent kernel. -/
theorem LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.traceWord_eq
    (package : Package A strategy hwin (initial := initial))
    (activated :
      (ActivatedPhysical A strategy hwin package).globalMachine.State)
    (tagged : (TaggedKernel A strategy hwin package).globalMachine.State)
    (hrel :
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
        strategy hwin activated tagged)
    (env : EnvironmentSequence In₁ In₂) :
    ((ActivatedPhysical A strategy hwin package).globalMachine.reroot activated
      ).globalMachineTraceWord
        (ActivatedPhysical A strategy hwin package).globalOutputOne
        (ActivatedPhysical A strategy hwin package).globalOutputTwo env =
      ((TaggedKernel A strategy hwin package).globalMachine.reroot tagged
        ).globalMachineTraceWord
          (TaggedKernel A strategy hwin package).globalOutputOne
          (TaggedKernel A strategy hwin package).globalOutputTwo env := by
  funext n
  have hstate := hrel.globalStateTrace A strategy hwin package activated tagged
    env (n + 1)
  have houtputs := hstate.outputs_eq A strategy hwin package
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
  injection houtputs with hone htwo
  rw [hone, htwo]

/-- Any DPA suffix property, in particular `AcceptsFrom` at the actual
post-prefix state, transfers through the duplicate-relay quotient. -/
theorem
    LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt.acceptsFrom_iff
    (package : Package A strategy hwin (initial := initial))
    (activated :
      (ActivatedPhysical A strategy hwin package).globalMachine.State)
    (tagged : (TaggedKernel A strategy hwin package).globalMachine.State)
    (hrel :
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
        strategy hwin activated tagged)
    (env : EnvironmentSequence In₁ In₂) (state : A.State) :
    A.AcceptsFrom state
        (((ActivatedPhysical A strategy hwin package).globalMachine.reroot
          activated).globalMachineTraceWord
            (ActivatedPhysical A strategy hwin package).globalOutputOne
            (ActivatedPhysical A strategy hwin package).globalOutputTwo env) ↔
      A.AcceptsFrom state
        (((TaggedKernel A strategy hwin package).globalMachine.reroot tagged
          ).globalMachineTraceWord
            (TaggedKernel A strategy hwin package).globalOutputOne
            (TaggedKernel A strategy hwin package).globalOutputTwo env) := by
  rw [hrel.traceWord_eq A strategy hwin package activated tagged env]

/-- Finite-prefix handoff for the actual activated physical word.  Once a
duplicate recurrent cut is supplied, the only remaining suffix obligation is
the ordinary tagged-kernel acceptance theorem at the actual DPA state. -/
theorem literalCombinedFreshPhaseActivated_accepts_of_duplicateRecurrentAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (tagged : (TaggedKernel A strategy hwin package).globalMachine.State)
    (hrel :
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A
        strategy hwin
        ((ActivatedPhysical A strategy hwin package).globalMachine.globalStateTrace
          env start)
        tagged)
    (haccepts :
      let actual := ActivatedPhysical A strategy hwin package
      let kernel := TaggedKernel A strategy hwin package
      A.AcceptsFrom
        (A.run
          (actual.globalMachine.globalMachineTraceWord actual.globalOutputOne
            actual.globalOutputTwo env) start)
        ((kernel.globalMachine.reroot tagged).globalMachineTraceWord
          kernel.globalOutputOne kernel.globalOutputTwo
          (OmegaWord.drop env start))) :
    A.Accepts
      ((ActivatedPhysical A strategy hwin package).globalMachine.globalMachineTraceWord
        (ActivatedPhysical A strategy hwin package).globalOutputOne
        (ActivatedPhysical A strategy hwin package).globalOutputTwo env) := by
  let actual := ActivatedPhysical A strategy hwin package
  let kernel := TaggedKernel A strategy hwin package
  apply A.accepts_of_rerootedGlobalMachine_acceptsFrom actual.globalMachine
    actual.globalOutputOne actual.globalOutputTwo env start
  exact
    (hrel.acceptsFrom_iff A strategy hwin package
      (actual.globalMachine.globalStateTrace env start) tagged
      (OmegaWord.drop env start)
      (A.run
        (actual.globalMachine.globalMachineTraceWord actual.globalOutputOne
          actual.globalOutputTwo env) start)).mpr haccepts

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
