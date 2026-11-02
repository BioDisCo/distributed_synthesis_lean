/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedFirstPersistentCut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartCutPhysicalPacket
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootFirstCut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootFirstCutRight

/-!
# Acceptance at the mega-linked persistent-tail handoff

The mega front delivers one concrete strict tag.  Its marked retained child is
exactly the first child required by `FullRestart`, and the first opposite
strict graph exposes exactly its live root.  This file instantiates the
general physical cut theorem at those two concrete right/left handoffs.

The source state below is not a new choice: it is the executable sender source
stored by the finite linked controller at the first persistent cut.  A later
finite-prefix splice theorem may identify the DPA state reached by the mega
front with this source and transport the resulting `AcceptsFrom` proof to the
complete controller word.
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

private abbrev FullRestartSemanticOne :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
      A strategy hwin)
    (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload
      A strategy hwin) PUnit.{1}

private abbrev FullRestartSemanticTwo :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
      A strategy hwin)
    (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload
      A strategy hwin) PUnit.{1}

private abbrev FullRestartRelayOne :=
  DistributedSynthesis.FiniteAcknowledgedDelayedCarrier (Fin 5)
    (FullRestartSemanticOne A strategy hwin)

private abbrev FullRestartRelayTwo :=
  DistributedSynthesis.FiniteAcknowledgedDelayedCarrier (Fin 5)
    (FullRestartSemanticTwo A strategy hwin)

private abbrev FullRestartPhysicalPair :=
  (FullRestartRelayOne A strategy hwin × Out₁) ×
    (FullRestartRelayTwo A strategy hwin × Out₂)

private abbrev MegaOldExceptionalOne
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointHybridMegaExceptionalOne A strategy hwin controllers
    initialBank

private abbrev MegaOldExceptionalTwo
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin controllers
    initialBank

private abbrev MegaOldOne
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointHybridMegaOneControl A strategy hwin initialBank Unit
    (MegaOldExceptionalOne A strategy hwin controllers initialBank)

private abbrev MegaOldTwo
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointHybridMegaTwoControl A strategy hwin initialBank Unit
    (MegaOldExceptionalTwo A strategy hwin controllers initialBank)

private abbrev MegaPhysicalController
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin) :=
  (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
    hwin controllers initialBank kernelTag).physicalController

private abbrev LinkedPhysicalController
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
    A strategy hwin tag

private def FullRestartPhysicalPairAllPending
    (controls : FullRestartPhysicalPair A strategy hwin) : Prop :=
  FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending controls.1.1 ∧
    FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending controls.2.1

/-! ## Runtime fallback-tag irrelevance

This explicit presentation avoids normalizing the complete dependent
controller record.  It is definitionally the physical `FullRestart` update,
but exposes only the acknowledged relay operations needed for the dynamic-tag
splice. -/

private noncomputable def profiledRawJointHybridFullRestartPhysicalAdvance
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂) :
    FullRestartPhysicalPair A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin
  let recvOne :=
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback))
  let recvTwo :=
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback))
  match round.graph with
  | .left =>
      (recvOne controls.1.1 round.inputOne controls.2.1 round.inputTwo,
        FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvTwo controls.2.1
          round.inputTwo)
  | .right =>
      (FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvOne controls.1.1
          round.inputOne,
        recvTwo controls.2.1 round.inputTwo controls.1.1 round.inputOne)
  | .both =>
      (recvOne controls.1.1 round.inputOne controls.2.1 round.inputTwo,
        recvTwo controls.2.1 round.inputTwo controls.1.1 round.inputOne)

/- The explicit update is exactly the public `FullRestart` physical
controller transition. -/
set_option maxHeartbeats 1000000 in
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag).advanceControls controls round =
      profiledRawJointHybridFullRestartPhysicalAdvance A strategy hwin tag
        controls round := by
  rcases controls with ⟨⟨one, oldOutputOne⟩, ⟨two, oldOutputTwo⟩⟩
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> rfl

/-- The explicit physical transition is independent of the fallback tag on
the complete reachable pending region. -/
theorem profiledRawJointHybridFullRestartPhysicalAdvance_tag_irrel_pending
    (left right :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hpending : FullRestartPhysicalPairAllPending A strategy hwin controls) :
    profiledRawJointHybridFullRestartPhysicalAdvance A strategy hwin left
        controls round =
      profiledRawJointHybridFullRestartPhysicalAdvance A strategy hwin right
        controls round := by
  rcases controls with ⟨⟨one, oldOutputOne⟩, ⟨two, oldOutputTwo⟩⟩
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph with
  | left =>
      apply Prod.ext
      · exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_recvReforkOne_tag_irrel_pending
            A strategy hwin left right one two inputOne inputTwo hpending.1
              hpending.2
      · rfl
  | right =>
      apply Prod.ext
      · rfl
      · exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_recvReforkTwo_tag_irrel_pending
            A strategy hwin left right two one inputTwo inputOne hpending.2
              hpending.1
  | both =>
      apply Prod.ext
      · exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_recvReforkOne_tag_irrel_pending
            A strategy hwin left right one two inputOne inputTwo hpending.1
              hpending.2
      · exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_recvReforkTwo_tag_irrel_pending
            A strategy hwin left right two one inputTwo inputOne hpending.2
              hpending.1

/-- The explicit update preserves the pending-only runtime region. -/
theorem profiledRawJointHybridFullRestartPhysicalAdvance_allPending
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hpending : FullRestartPhysicalPairAllPending A strategy hwin controls) :
    FullRestartPhysicalPairAllPending A strategy hwin
      (profiledRawJointHybridFullRestartPhysicalAdvance A strategy hwin tag
        controls round) := by
  rcases controls with ⟨⟨one, oldOutputOne⟩, ⟨two, oldOutputTwo⟩⟩
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph with
  | left =>
      exact
        FiniteAcknowledgedDelayedCarrier.deferredRelayPairAllPending_strictLeft
          (pendingStepTwo :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
              A strategy hwin)
          (recurrentStepTwo :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
              (Out₂ := Out₂))
          (freshOne :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          (freshTwo :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          (outputOne :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          one inputOne two inputTwo hpending
  | right =>
      exact
        FiniteAcknowledgedDelayedCarrier.deferredRelayPairAllPending_strictRight
          (pendingStepOne :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
              A strategy hwin)
          (recurrentStepOne :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
              (Out₁ := Out₁))
          (freshOne :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          (freshTwo :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          (outputTwo :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          one inputOne two inputTwo hpending
  | both =>
      exact
        FiniteAcknowledgedDelayedCarrier.deferredRelayPairAllPending_both
          (freshOne :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          (freshTwo :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          (outputOne :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          (outputTwo :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag))
          one inputOne two inputTwo

/- The public controller transition preserves the same all-pending region. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hpending : FullRestartPhysicalPairAllPending A strategy hwin controls) :
    FullRestartPhysicalPairAllPending A strategy hwin
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag).advanceControls controls round) := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  exact
    profiledRawJointHybridFullRestartPhysicalAdvance_allPending
      A strategy hwin tag controls round hpending

set_option maxHeartbeats 400000 in
private theorem profiledRawJointHybridFullRestart_initial_allPending
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin) :
    let controller :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag
    FullRestartPhysicalPairAllPending A strategy hwin
      (controller.initialOne, controller.initialTwo) := by
  dsimp only
  change
    FiniteAcknowledgedDelayedCarrier.DeferredRelayPairAllPending
      (⟨.known
        (.inl
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
            A strategy hwin tag)), none⟩)
      (⟨.known
        (.inl
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
            A strategy hwin tag)), none⟩)
  exact
    FiniteAcknowledgedDelayedCarrier.deferredRelayPairAllPending_initial
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin tag)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin tag)

/- Every state on a canonical `FullRestart` run is in the pending region. -/
set_option maxHeartbeats 400000 in
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_globalStateTrace_allPending
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let controller :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag
    FullRestartPhysicalPairAllPending A strategy hwin
      (controller.globalMachine.globalStateTrace env n) := by
  dsimp only
  induction n with
  | zero =>
      exact profiledRawJointHybridFullRestart_initial_allPending
        A strategy hwin tag
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change FullRestartPhysicalPairAllPending A strategy hwin
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
          A strategy hwin tag).advanceControls
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
              A strategy hwin tag).globalMachine.globalStateTrace env n)
            (env n))
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
          A strategy hwin tag _ _ ih

/-! ## Dynamic fallback-tag transport

Once both acknowledged relays are in the pending region, the fallback tag is
operationally dead: every future transition is independent of it, and the
pending region is invariant.  The simultaneous induction below records both
facts, so that a suffix entered with a stale mega-front tag can be rerooted at
the child tag actually delivered by the closing receive. -/

private noncomputable def profiledRawJointHybridFullRestartPhysicalTrace
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : Nat →
    FullRestartPhysicalPair A strategy hwin
  | 0 => controls
  | n + 1 =>
      profiledRawJointHybridFullRestartPhysicalAdvance A strategy hwin tag
        (profiledRawJointHybridFullRestartPhysicalTrace tag controls env n)
          (env n)

private theorem profiledRawJointHybridFullRestartPhysicalTrace_allPending
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hpending : FullRestartPhysicalPairAllPending A strategy hwin controls) :
    ∀ n : Nat,
      FullRestartPhysicalPairAllPending A strategy hwin
        (profiledRawJointHybridFullRestartPhysicalTrace A strategy hwin tag
          controls env n) := by
  intro n
  induction n with
  | zero => exact hpending
  | succ n ih =>
      exact
        profiledRawJointHybridFullRestartPhysicalAdvance_allPending
          A strategy hwin tag _ _ ih

private theorem profiledRawJointHybridFullRestartPhysicalTrace_tag_irrel_pending
    (left right :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hpending : FullRestartPhysicalPairAllPending A strategy hwin controls) :
    ∀ n : Nat,
      profiledRawJointHybridFullRestartPhysicalTrace A strategy hwin left
          controls env n =
        profiledRawJointHybridFullRestartPhysicalTrace A strategy hwin right
          controls env n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointHybridFullRestartPhysicalTrace,
        profiledRawJointHybridFullRestartPhysicalTrace, ih]
      exact
        profiledRawJointHybridFullRestartPhysicalAdvance_tag_irrel_pending
          A strategy hwin left right _ _
            (profiledRawJointHybridFullRestartPhysicalTrace_allPending
              A strategy hwin right controls env hpending n)

set_option maxHeartbeats 400000 in
private theorem profiledRawJointHybridFullRestart_globalStateTrace_eq_physicalTrace
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag).globalMachine.reroot controls
      ).globalStateTrace env n) =
      profiledRawJointHybridFullRestartPhysicalTrace A strategy hwin tag
        controls env n := by
  intro n
  induction n with
  | zero =>
      change controls = controls
      rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
          A strategy hwin tag).advanceControls
            (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
              A strategy hwin tag).globalMachine.reroot controls
            ).globalStateTrace env n) (env n) = _
      rw [ih, profiledRawJointHybridFullRestartPhysicalTrace,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]

private theorem profiledRawJointHybridFullRestart_globalOutputOne_eq_snd
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin tag).globalOutputOne controls = controls.1.2 := by
  rfl

private theorem profiledRawJointHybridFullRestart_globalOutputTwo_eq_snd
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin tag).globalOutputTwo controls = controls.2.2 := by
  rfl

/- The complete Moore suffix word is independent of the fallback tag from
any common all-pending physical reroot. -/
set_option maxHeartbeats 400000 in
theorem profiledRawJointHybridFullRestart_reroot_traceWord_tag_irrel_pending
    (left right :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (controls : FullRestartPhysicalPair A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hpending : FullRestartPhysicalPairAllPending A strategy hwin controls) :
    let leftController :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin left
    let rightController :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin right
    (leftController.globalMachine.reroot controls).globalMachineTraceWord
        leftController.globalOutputOne leftController.globalOutputTwo env =
      (rightController.globalMachine.reroot controls).globalMachineTraceWord
        rightController.globalOutputOne rightController.globalOutputTwo env := by
  dsimp only
  funext n
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
  rw [profiledRawJointHybridFullRestart_globalOutputOne_eq_snd,
    profiledRawJointHybridFullRestart_globalOutputTwo_eq_snd,
    profiledRawJointHybridFullRestart_globalOutputOne_eq_snd,
    profiledRawJointHybridFullRestart_globalOutputTwo_eq_snd]
  rw [profiledRawJointHybridFullRestart_globalStateTrace_eq_physicalTrace
      A strategy hwin left controls env (n + 1),
    profiledRawJointHybridFullRestart_globalStateTrace_eq_physicalTrace
      A strategy hwin right controls env (n + 1),
    profiledRawJointHybridFullRestartPhysicalTrace_tag_irrel_pending
      A strategy hwin left right controls env hpending (n + 1)]

/-! ## Mixed-close pending packets

The tagged endpoint of a reachable mixed state remains pending throughout its
same-direction prefix.  The two compact packets below show that the first
opposite receive therefore enters the all-pending region consumed by the
dynamic fallback-tag theorem above. -/

/- A no-receive step cannot move an old process-one front control into the
linked tail.  The existential form keeps the sizeable old-front transition
table opaque to the mixed-prefix induction. -/
private theorem profiledRawJointHybridMegaLinked_noRecvOne_oldFront_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (front : MegaOldOne A strategy hwin controllers initialBank)
    (oldOutput : Out₁) (input : In₁) :
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank kernelTag).physicalController
    ∃ (nextFront : MegaOldOne A strategy hwin controllers initialBank)
        (nextOutput : Out₁),
      mega.noRecvOne
          (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank front, oldOutput) input =
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
          controllers initialBank nextFront, nextOutput) := by
  dsimp only
  cases front with
  | initial state =>
      let next := stepProfiledRawJointRootRightOwner A strategy controllers
        (profiledRawJointInitialRightOwnerInitial A strategy controllers) input
      exact ⟨.exceptional
        (profiledRawJointHybridMegaExceptionalOneOfOld A strategy hwin
          controllers initialBank (.inl next.2)), next.1, rfl⟩
  | exceptional state =>
      let next := profiledRawJointHybridMegaExceptionalNoRecvOne A strategy
        hwin controllers initialBank state input
      exact ⟨next.2, next.1, rfl⟩
  | rightOwner key state =>
      let kernel :=
        profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag
      let next := kernel.rightOwnerNoRecvOne key state input
      exact ⟨.rightOwner key next.2, next.1, rfl⟩
  | leftReceiver key state =>
      let kernel :=
        profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag
      let next := kernel.leftReceiverNoRecvOne key state input
      exact ⟨.rightOwner next.2.1 next.2.2, next.1, rfl⟩

/- Process-two mirror. -/
private theorem profiledRawJointHybridMegaLinked_noRecvTwo_oldFront_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (front : MegaOldTwo A strategy hwin controllers initialBank)
    (oldOutput : Out₂) (input : In₂) :
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank kernelTag).physicalController
    ∃ (nextFront : MegaOldTwo A strategy hwin controllers initialBank)
        (nextOutput : Out₂),
      mega.noRecvTwo
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank front, oldOutput) input =
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
          controllers initialBank nextFront, nextOutput) := by
  dsimp only
  cases front with
  | initial state =>
      let next := stepProfiledRawJointRootLeftOwner A strategy controllers
        (profiledRawJointInitialLeftOwnerInitial A strategy controllers) input
      exact ⟨.exceptional
        (profiledRawJointHybridMegaExceptionalTwoOfOld A strategy hwin
          controllers initialBank (.inr (.inl next.2))), next.1, rfl⟩
  | exceptional state =>
      let next := profiledRawJointHybridMegaExceptionalNoRecvTwo A strategy
        hwin controllers initialBank state input
      exact ⟨next.2, next.1, rfl⟩
  | rightReceiver key state =>
      let kernel :=
        profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag
      let next := kernel.rightReceiverNoRecvTwo key state input
      exact ⟨.leftOwner next.2.1 next.2.2, next.1, rfl⟩
  | leftOwner key state =>
      let kernel :=
        profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag
      let next := kernel.leftOwnerNoRecvTwo key state input
      exact ⟨.leftOwner key next.2, next.1, rfl⟩

/- A left-created mixed state remains mixed on another strict-left round.
Its tagged endpoint performs exactly the corresponding virtual FullRestart
step against the canonical still-blind process-two control. -/
theorem profiledRawJointHybridMegaLinked_leftMixed_strictLeft_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag).OneControl)
    (hone : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one.1)
    (frontTwo : MegaOldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂) (inputOne : In₁) (inputTwo : In₂) :
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank kernelTag).physicalController
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, .left⟩
    ∃ (nextOne : linked.OneControl)
        (nextFrontTwo : MegaOldTwo A strategy hwin controllers initialBank)
        (nextOutputTwo : Out₂),
      mega.advanceControls
          ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
              controllers initialBank (entryTag, one.1), one.2),
            (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
              controllers initialBank frontTwo, frontOutputTwo)) round =
        ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
            controllers initialBank (entryTag, nextOne.1), nextOne.2),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank nextFrontTwo, nextOutputTwo)) ∧
      nextOne = (linked.advanceControls (one, linked.initialTwo) round).1 ∧
      FiniteAcknowledgedDelayedCarrier.CarrierAll
        FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending
          nextOne.1 := by
  dsimp only
  obtain ⟨nextFrontTwo, nextOutputTwo, hfront⟩ :=
    profiledRawJointHybridMegaLinked_noRecvTwo_oldFront_exists A strategy hwin
      controllers initialBank kernelTag frontTwo frontOutputTwo inputTwo
  let linked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin entryTag
  let round : EnvironmentRound In₁ In₂ := ⟨inputOne, inputTwo, .left⟩
  let nextOne := (linked.advanceControls (one, linked.initialTwo) round).1
  refine ⟨nextOne, nextFrontTwo, nextOutputTwo, ?_, rfl, ?_⟩
  · change
      ( _ ,
        ((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag).physicalController
            ).noRecvTwo
              (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
                  controllers initialBank frontTwo, frontOutputTwo)
              inputTwo) = _
    rw [hfront]
    apply Prod.ext
    · cases frontTwo <;> rfl
    · rfl
  · have hall :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
        A strategy hwin entryTag (one, linked.initialTwo) round
          ⟨hone,
            (profiledRawJointHybridFullRestart_initial_allPending A strategy
              hwin entryTag).2⟩
    exact hall.1

/- Right-created mirror: another strict-right round preserves the mixed
state and advances only the tagged process-two FullRestart endpoint. -/
theorem profiledRawJointHybridMegaLinked_rightMixed_strictRight_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (two :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag).TwoControl)
    (htwo : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two.1)
    (frontOne : MegaOldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁) (inputOne : In₁) (inputTwo : In₂) :
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank kernelTag).physicalController
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, .right⟩
    ∃ (nextTwo : linked.TwoControl)
        (nextFrontOne : MegaOldOne A strategy hwin controllers initialBank)
        (nextOutputOne : Out₁),
      mega.advanceControls
          ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
              controllers initialBank frontOne, frontOutputOne),
            (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
              controllers initialBank (entryTag, two.1), two.2)) round =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank nextFrontOne, nextOutputOne),
          (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
            controllers initialBank (entryTag, nextTwo.1), nextTwo.2)) ∧
      nextTwo = (linked.advanceControls (linked.initialOne, two) round).2 ∧
      FiniteAcknowledgedDelayedCarrier.CarrierAll
        FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending
          nextTwo.1 := by
  dsimp only
  obtain ⟨nextFrontOne, nextOutputOne, hfront⟩ :=
    profiledRawJointHybridMegaLinked_noRecvOne_oldFront_exists A strategy hwin
      controllers initialBank kernelTag frontOne frontOutputOne inputOne
  let linked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin entryTag
  let round : EnvironmentRound In₁ In₂ := ⟨inputOne, inputTwo, .right⟩
  let nextTwo := (linked.advanceControls (linked.initialOne, two) round).2
  refine ⟨nextTwo, nextFrontOne, nextOutputOne, ?_, rfl, ?_⟩
  · change
      (((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag).physicalController
            ).noRecvOne
              (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
                  controllers initialBank frontOne, frontOutputOne)
              inputOne,
        _) = _
    rw [hfront]
    apply Prod.ext
    · rfl
    · cases frontOne <;> rfl
  · have hall :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
        A strategy hwin entryTag (linked.initialOne, two) round
          ⟨(profiledRawJointHybridFullRestart_initial_allPending A strategy hwin
              entryTag).1,
            htwo⟩
    exact hall.2

/- A left-created reachable mixed state: process one carries one pending
FullRestart relay at a concrete tag, while process two is still entirely in
the old finite front. -/
def ProfiledRawJointHybridMegaLinkedLeftMixedPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl) : Prop :=
  ∃ (entryTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin)
      (one : (LinkedPhysicalController A strategy hwin entryTag).OneControl)
      (frontTwo : MegaOldTwo A strategy hwin controllers initialBank)
      (frontOutputTwo : Out₂),
    state =
      ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (entryTag, one.1), one.2),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank frontTwo, frontOutputTwo)) ∧
    FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one.1

/- Right-created mirror. -/
def ProfiledRawJointHybridMegaLinkedRightMixedPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl) : Prop :=
  ∃ (entryTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin)
      (two : (LinkedPhysicalController A strategy hwin entryTag).TwoControl)
      (frontOne : MegaOldOne A strategy hwin controllers initialBank)
      (frontOutputOne : Out₁),
    state =
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank frontOne, frontOutputOne),
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (entryTag, two.1), two.2)) ∧
    FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two.1

/- Both endpoints have installed one common linked tag and the complete
FullRestart physical pair is in its invariant pending region. -/
def ProfiledRawJointHybridMegaLinkedTailPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl) : Prop :=
  ∃ (entryTag :
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
          strategy hwin)
      (controls : FullRestartPhysicalPair A strategy hwin),
    state =
      ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (entryTag, controls.1.1), controls.1.2),
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (entryTag, controls.2.1), controls.2.2)) ∧
    FullRestartPhysicalPairAllPending A strategy hwin controls

theorem ProfiledRawJointHybridMegaLinkedLeftMixedPending.advance_strictLeft
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).advanceControls state ⟨inputOne, inputTwo, .left⟩) := by
  rcases mixed with ⟨entryTag, one, frontTwo, frontOutputTwo, rfl, hpending⟩
  obtain ⟨nextOne, nextFrontTwo, nextOutputTwo, hnext, _, hnextPending⟩ :=
    profiledRawJointHybridMegaLinked_leftMixed_strictLeft_exists A strategy hwin
      controllers initialBank kernelTag entryTag one hpending frontTwo
        frontOutputTwo inputOne inputTwo
  exact ⟨entryTag, nextOne, nextFrontTwo, nextOutputTwo, hnext,
    hnextPending⟩

theorem ProfiledRawJointHybridMegaLinkedRightMixedPending.advance_strictRight
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).advanceControls state ⟨inputOne, inputTwo, .right⟩) := by
  rcases mixed with ⟨entryTag, two, frontOne, frontOutputOne, rfl, hpending⟩
  obtain ⟨nextTwo, nextFrontOne, nextOutputOne, hnext, _, hnextPending⟩ :=
    profiledRawJointHybridMegaLinked_rightMixed_strictRight_exists A strategy
      hwin controllers initialBank kernelTag entryTag two hpending frontOne
        frontOutputOne inputOne inputTwo
  exact ⟨entryTag, nextTwo, nextFrontOne, nextOutputOne, hnext,
    hnextPending⟩

theorem ProfiledRawJointHybridMegaLinkedLeftMixedPending.advance_of_receivesTwo
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (inputOne : In₁) (inputTwo : In₂) (graph : Graph)
    (hreceives : graph ≠ .left) :
    ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
      initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).advanceControls state ⟨inputOne, inputTwo, graph⟩) := by
  rcases mixed with ⟨entryTag, one, frontTwo, frontOutputTwo, rfl, hpending⟩
  let maps :=
    profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy hwin
      controllers initialBank
        (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
          hwin controllers initialBank)
  let linked := LinkedPhysicalController A strategy hwin entryTag
  let round : EnvironmentRound In₁ In₂ := ⟨inputOne, inputTwo, graph⟩
  let controls := linked.advanceControls (one, linked.initialTwo) round
  have hpending' : FullRestartPhysicalPairAllPending A strategy hwin controls :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
      A strategy hwin entryTag (one, linked.initialTwo) round
        ⟨hpending,
          (profiledRawJointHybridFullRestart_initial_allPending A strategy hwin
            entryTag).2⟩
  refine ⟨entryTag, controls, ?_, hpending'⟩
  cases graph with
  | left => exact (hreceives rfl).elim
  | right =>
      simpa [MegaPhysicalController, maps, linked, round, controls] using
        (profiledRawJointHybridMegaLinkedCloseLeftMixed_strictRight A strategy
          hwin controllers initialBank entryTag maps one frontTwo
            frontOutputTwo inputOne inputTwo)
  | both =>
      simpa [MegaPhysicalController, maps, linked, round, controls] using
        (profiledRawJointHybridMegaLinkedCloseLeftMixed_both A strategy hwin
          controllers initialBank entryTag maps one frontTwo frontOutputTwo
            inputOne inputTwo)

theorem ProfiledRawJointHybridMegaLinkedRightMixedPending.advance_of_receivesOne
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (inputOne : In₁) (inputTwo : In₂) (graph : Graph)
    (hreceives : graph ≠ .right) :
    ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
      initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).advanceControls state ⟨inputOne, inputTwo, graph⟩) := by
  rcases mixed with ⟨entryTag, two, frontOne, frontOutputOne, rfl, hpending⟩
  let maps :=
    profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy hwin
      controllers initialBank
        (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
          hwin controllers initialBank)
  let linked := LinkedPhysicalController A strategy hwin entryTag
  let round : EnvironmentRound In₁ In₂ := ⟨inputOne, inputTwo, graph⟩
  let controls := linked.advanceControls (linked.initialOne, two) round
  have hpending' : FullRestartPhysicalPairAllPending A strategy hwin controls :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
      A strategy hwin entryTag (linked.initialOne, two) round
        ⟨(profiledRawJointHybridFullRestart_initial_allPending A strategy hwin
            entryTag).1,
          hpending⟩
  refine ⟨entryTag, controls, ?_, hpending'⟩
  cases graph with
  | left =>
      simpa [MegaPhysicalController, maps, linked, round, controls] using
        (profiledRawJointHybridMegaLinkedCloseRightMixed_strictLeft A strategy
          hwin controllers initialBank entryTag maps two frontOne
            frontOutputOne inputOne inputTwo)
  | right => exact (hreceives rfl).elim
  | both =>
      simpa [MegaPhysicalController, maps, linked, round, controls] using
        (profiledRawJointHybridMegaLinkedCloseRightMixed_both A strategy hwin
          controllers initialBank entryTag maps two frontOne frontOutputOne
            inputOne inputTwo)

theorem ProfiledRawJointHybridMegaLinkedTailPending.advance
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (tail : ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin
      controllers initialBank kernelTag state)
    (round : EnvironmentRound In₁ In₂) :
    ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
      initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).advanceControls state round) := by
  rcases tail with ⟨entryTag, controls, rfl, hpending⟩
  let maps :=
    profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy hwin
      controllers initialBank
        (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
          hwin controllers initialBank)
  let linked := LinkedPhysicalController A strategy hwin entryTag
  let next := linked.advanceControls controls round
  have hnextPending : FullRestartPhysicalPairAllPending A strategy hwin next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
      A strategy hwin entryTag controls round hpending
  refine ⟨entryTag, next, ?_, hnextPending⟩
  simpa [MegaPhysicalController, maps, linked, next] using
    (profiledRawJointHybridMegaLinkedEmbedTail_advanceControls A strategy hwin
      controllers initialBank entryTag maps controls round)

theorem ProfiledRawJointHybridMegaLinkedTailPending.reroot_globalStateTrace
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl)
    (tail : ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
        initialBank kernelTag
          (((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.reroot state).globalStateTrace env n) := by
  intro n
  induction n with
  | zero => exact tail
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      exact ih.advance A strategy hwin controllers initialBank kernelTag
        (env n)

/- A closed mega-tail suffix is literally the corresponding rerooted linked
`FullRestart` word.  This extraction keeps the dynamically installed tag and
physical state visible for the acceptance argument. -/
theorem
    ProfiledRawJointHybridMegaLinkedTailPending.reroot_traceWord_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl)
    (tail : ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂) :
    ∃ (entryTag :
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
            strategy hwin)
        (controls : FullRestartPhysicalPair A strategy hwin),
      FullRestartPhysicalPairAllPending A strategy hwin controls ∧
        (((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).globalMachine.reroot state).globalMachineTraceWord
            (MegaPhysicalController A strategy hwin controllers initialBank
              kernelTag).globalOutputOne
            (MegaPhysicalController A strategy hwin controllers initialBank
              kernelTag).globalOutputTwo env) =
          (((LinkedPhysicalController A strategy hwin entryTag).globalMachine
            ).reroot controls).globalMachineTraceWord
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputOne
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputTwo env := by
  rcases tail with ⟨entryTag, controls, rfl, hpending⟩
  refine ⟨entryTag, controls, hpending, ?_⟩
  let maps :=
    profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy hwin
      controllers initialBank
        (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
          hwin controllers initialBank)
  simpa [MegaPhysicalController, LinkedPhysicalController, maps] using
    (profiledRawJointHybridMegaLinkedEmbedTail_globalMachineTraceWord A
      strategy hwin controllers initialBank entryTag maps controls env)

/- Actual-prefix form: once an original mega run is tail-pending, dropping
that prefix exposes exactly one dynamically rerooted `FullRestart` word. -/
theorem
    profiledRawJointHybridMegaLinkedTailPending_drop_traceWord_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (tail : ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin
      controllers initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).globalMachine.globalStateTrace env start)) :
    ∃ (entryTag :
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
            strategy hwin)
        (controls : FullRestartPhysicalPair A strategy hwin),
      FullRestartPhysicalPairAllPending A strategy hwin controls ∧
        OmegaWord.drop
            ((MegaPhysicalController A strategy hwin controllers initialBank
              kernelTag).globalMachine.globalMachineTraceWord
                (MegaPhysicalController A strategy hwin controllers initialBank
                  kernelTag).globalOutputOne
                (MegaPhysicalController A strategy hwin controllers initialBank
                  kernelTag).globalOutputTwo env) start =
          (((LinkedPhysicalController A strategy hwin entryTag).globalMachine
            ).reroot controls).globalMachineTraceWord
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputOne
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputTwo (OmegaWord.drop env start) := by
  let mega := MegaPhysicalController A strategy hwin controllers initialBank
    kernelTag
  rcases
      ProfiledRawJointHybridMegaLinkedTailPending.reroot_traceWord_exists
        A strategy hwin controllers initialBank kernelTag
          (mega.globalMachine.globalStateTrace env start) tail
            (OmegaWord.drop env start) with
    ⟨entryTag, controls, hpending, hword⟩
  refine ⟨entryTag, controls, hpending, ?_⟩
  rw [← hword]
  exact (mega.globalMachine.reroot_globalMachineTraceWord_drop
    mega.globalOutputOne mega.globalOutputTwo env start).symm

theorem
    ProfiledRawJointHybridMegaLinkedLeftMixedPending.reroot_globalStateTrace
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl)
    (mixed : ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂)
    (hall : ∀ n : Nat, (env n).graph = .left) :
    ∀ n : Nat,
      ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
        controllers initialBank kernelTag
          (((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.reroot state).globalStateTrace env n) := by
  intro n
  induction n with
  | zero => exact mixed
  | succ n ih =>
      have hgraph := hall n
      rcases hround : env n with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hround]
      exact ih.advance_strictLeft A strategy hwin controllers initialBank
        kernelTag inputOne inputTwo

theorem
    ProfiledRawJointHybridMegaLinkedRightMixedPending.reroot_globalStateTrace
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl)
    (mixed : ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂)
    (hall : ∀ n : Nat, (env n).graph = .right) :
    ∀ n : Nat,
      ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
        controllers initialBank kernelTag
          (((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.reroot state).globalStateTrace env n) := by
  intro n
  induction n with
  | zero => exact mixed
  | succ n ih =>
      have hgraph := hall n
      rcases hround : env n with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hround]
      exact ih.advance_strictRight A strategy hwin controllers initialBank
        kernelTag inputOne inputTwo

theorem
    ProfiledRawJointHybridMegaLinkedLeftMixedPending.reroot_globalStateTrace_of_forall_lt
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl)
    (mixed : ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hall : ∀ k : Nat, k < n → (env k).graph = .left) :
    ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag
        (((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).globalMachine.reroot state).globalStateTrace env n) := by
  induction n with
  | zero => exact mixed
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      have hgraph := hall n (Nat.lt_succ_self n)
      rcases hround : env n with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      apply ProfiledRawJointHybridMegaLinkedLeftMixedPending.advance_strictLeft
        A strategy hwin controllers initialBank kernelTag
      · exact ih (fun k hk ↦ hall k (Nat.lt_trans hk (Nat.lt_succ_self n)))

theorem
    ProfiledRawJointHybridMegaLinkedRightMixedPending.reroot_globalStateTrace_of_forall_lt
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl)
    (mixed : ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hall : ∀ k : Nat, k < n → (env k).graph = .right) :
    ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag
        (((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).globalMachine.reroot state).globalStateTrace env n) := by
  induction n with
  | zero => exact mixed
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      have hgraph := hall n (Nat.lt_succ_self n)
      rcases hround : env n with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      apply
        ProfiledRawJointHybridMegaLinkedRightMixedPending.advance_strictRight
          A strategy hwin controllers initialBank kernelTag
      · exact ih (fun k hk ↦ hall k (Nat.lt_trans hk (Nat.lt_succ_self n)))

/- Persistent strict reversal is stable under dropping any finite prefix. -/
theorem PersistentStrictReversalTail.drop
    {graphs : Nat → Graph} (h : PersistentStrictReversalTail graphs)
    (start : Nat) :
    PersistentStrictReversalTail (fun n ↦ graphs (start + n)) := by
  constructor
  · rcases h.1 with ⟨noBothAt, hnoBoth⟩
    refine ⟨noBothAt, ?_⟩
    intro n hn
    exact hnoBoth (start + n) (by omega)
  · constructor
    · intro after
      rcases h.2.1 (start + after) with ⟨n, hn, hleft⟩
      refine ⟨n - start, ?_, ?_⟩
      · omega
      · simpa [Nat.add_sub_of_le (Nat.le_trans (Nat.le_add_right start after)
          hn)] using hleft
    · intro after
      rcases h.2.2 (start + after) with ⟨n, hn, hright⟩
      refine ⟨n - start, ?_, ?_⟩
      · omega
      · simpa [Nat.add_sub_of_le (Nat.le_trans (Nat.le_add_right start after)
          hn)] using hright

/- The first round at which process two receives closes a left-created mixed
front into a shared `FullRestart` tail.  Minimality of `close` is exactly what
is needed to propagate the mixed invariant over the preceding strict-left
block. -/
theorem
    ProfiledRawJointHybridMegaLinkedLeftMixedPending.exists_tail_of_exists_receivesTwo
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂)
    (hexists : ∃ k : Nat, (env k).graph ≠ .left) :
    ∃ close : Nat,
      ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
        initialBank kernelTag
          (((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.reroot state).globalStateTrace env
              (close + 1)) := by
  let close := Nat.find hexists
  have hclose : (env close).graph ≠ .left := Nat.find_spec hexists
  have hbefore : ∀ k : Nat, k < close → (env k).graph = .left := by
    intro k hk
    by_contra hne
    exact (Nat.find_min hexists hk) hne
  have hmixed :=
    ProfiledRawJointHybridMegaLinkedLeftMixedPending.reroot_globalStateTrace_of_forall_lt
      A strategy hwin controllers initialBank kernelTag state mixed env close
        hbefore
  rcases hround : env close with ⟨inputOne, inputTwo, graph⟩
  simp only [hround] at hclose
  refine ⟨close, ?_⟩
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hround]
  exact hmixed.advance_of_receivesTwo A strategy hwin controllers initialBank
    kernelTag inputOne inputTwo graph hclose

/- Mirror closure at the first round received by process one. -/
theorem
    ProfiledRawJointHybridMegaLinkedRightMixedPending.exists_tail_of_exists_receivesOne
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂)
    (hexists : ∃ k : Nat, (env k).graph ≠ .right) :
    ∃ close : Nat,
      ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
        initialBank kernelTag
          (((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.reroot state).globalStateTrace env
              (close + 1)) := by
  let close := Nat.find hexists
  have hclose : (env close).graph ≠ .right := Nat.find_spec hexists
  have hbefore : ∀ k : Nat, k < close → (env k).graph = .right := by
    intro k hk
    by_contra hne
    exact (Nat.find_min hexists hk) hne
  have hmixed :=
    ProfiledRawJointHybridMegaLinkedRightMixedPending.reroot_globalStateTrace_of_forall_lt
      A strategy hwin controllers initialBank kernelTag state mixed env close
        hbefore
  rcases hround : env close with ⟨inputOne, inputTwo, graph⟩
  simp only [hround] at hclose
  refine ⟨close, ?_⟩
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hround]
  exact hmixed.advance_of_receivesOne A strategy hwin controllers initialBank
    kernelTag inputOne inputTwo graph hclose

/- Under persistent strict reversal, the opposite receive needed by a mixed
state is unavoidable. -/
theorem
    ProfiledRawJointHybridMegaLinkedLeftMixedPending.exists_tail_of_persistentStrictReversal
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ close : Nat,
      ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
        initialBank kernelTag
          (((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.reroot state).globalStateTrace env
              (close + 1)) := by
  apply mixed.exists_tail_of_exists_receivesTwo A strategy hwin controllers
    initialBank kernelTag env
  rcases hreversal.2.2 0 with ⟨k, _, hright⟩
  exact ⟨k, by simp [hright]⟩

/- Mirror persistent-reversal closure. -/
theorem
    ProfiledRawJointHybridMegaLinkedRightMixedPending.exists_tail_of_persistentStrictReversal
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    {state :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).TwoControl}
    (mixed : ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag state)
    (env : EnvironmentSequence In₁ In₂)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ close : Nat,
      ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
        initialBank kernelTag
          (((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.reroot state).globalStateTrace env
              (close + 1)) := by
  apply mixed.exists_tail_of_exists_receivesOne A strategy hwin controllers
    initialBank kernelTag env
  rcases hreversal.2.1 0 with ⟨k, _, hleft⟩
  exact ⟨k, by simp [hleft]⟩

/- A genuine strict-left front handoff installs the exact left-created tag at
process one and leaves process two in the old front.  This is the mixed-state
base case used before the first opposite receive. -/
theorem profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank kernelTag).physicalController
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag
    ∃ (entryOne : linked.OneControl)
        (nextFrontTwo : MegaOldTwo A strategy hwin controllers initialBank)
        (nextOutputTwo : Out₂),
      mega.advanceControls
          ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
              controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy
                hwin controllers initialBank shadow), oldOutputOne),
            (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
              controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A
                strategy hwin controllers initialBank owner), oldOutputTwo))
          ⟨inputOne, inputTwo, .left⟩ =
        ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
            controllers initialBank (entryTag, entryOne.1), entryOne.2),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank nextFrontTwo, nextOutputTwo)) ∧
      FiniteAcknowledgedDelayedCarrier.CarrierAll
        FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending entryOne.1 := by
  dsimp only
  let frontTwo :=
    profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy hwin
      controllers initialBank owner
  obtain ⟨nextFrontTwo, nextOutputTwo, hfront⟩ :=
    profiledRawJointHybridMegaLinked_noRecvTwo_oldFront_exists A strategy hwin
      controllers initialBank kernelTag frontTwo oldOutputTwo inputTwo
  let entryTag :=
    profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin shadow
      owner inputOne inputTwo
  let linked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin entryTag
  let fork :=
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
      entryTag
  let entryOne : linked.OneControl :=
    (fork.1,
      (profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
        initialBank shadow owner inputOne inputTwo).1)
  refine ⟨entryOne, nextFrontTwo, nextOutputTwo, ?_, ?_⟩
  · change
      (_, ((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
          ).noRecvTwo
            (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
                controllers initialBank frontTwo, oldOutputTwo) inputTwo) = _
    rw [hfront]
    apply Prod.ext
    · rfl
    · rfl
  · change True ∧ True
    exact ⟨trivial, trivial⟩

/- Strict-right creation mirror. -/
theorem profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_exists
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank kernelTag).physicalController
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag
    ∃ (entryTwo : linked.TwoControl)
        (nextFrontOne : MegaOldOne A strategy hwin controllers initialBank)
        (nextOutputOne : Out₁),
      mega.advanceControls
          ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
              controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
                strategy hwin controllers initialBank owner), oldOutputOne),
            (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
              controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy
                hwin controllers initialBank shadow), oldOutputTwo))
          ⟨inputOne, inputTwo, .right⟩ =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank nextFrontOne, nextOutputOne),
          (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
            controllers initialBank (entryTag, entryTwo.1), entryTwo.2)) ∧
      FiniteAcknowledgedDelayedCarrier.CarrierAll
        FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending entryTwo.1 := by
  dsimp only
  let frontOne :=
    profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy hwin
      controllers initialBank owner
  obtain ⟨nextFrontOne, nextOutputOne, hfront⟩ :=
    profiledRawJointHybridMegaLinked_noRecvOne_oldFront_exists A strategy hwin
      controllers initialBank kernelTag frontOne oldOutputOne inputOne
  let entryTag :=
    profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin shadow
      owner inputOne inputTwo
  let linked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin entryTag
  let fork :=
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
      entryTag
  let entryTwo : linked.TwoControl :=
    (fork.2,
      (profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
        initialBank shadow owner inputTwo inputOne).1)
  refine ⟨entryTwo, nextFrontOne, nextOutputOne, ?_, ?_⟩
  · change
      (((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
          ).noRecvOne
            (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
                controllers initialBank frontOne, oldOutputOne) inputOne, _) = _
    rw [hfront]
    apply Prod.ext
    · rfl
    · rfl
  · change True ∧ True
    exact ⟨trivial, trivial⟩

theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_mixedPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let frontState :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
            controllers initialBank shadow), oldOutputOne),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
            hwin controllers initialBank owner), oldOutputTwo))
    ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag
        (mega.advanceControls frontState ⟨inputOne, inputTwo, .left⟩) := by
  dsimp only
  obtain ⟨entryOne, nextFrontTwo, nextOutputTwo, hnext, hpending⟩ :=
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_exists
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo inputOne inputTwo
  exact
    ⟨profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo,
      entryOne, nextFrontTwo, nextOutputTwo, hnext, hpending⟩

theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_mixedPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let frontState :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
            hwin controllers initialBank owner), oldOutputOne),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
            controllers initialBank shadow), oldOutputTwo))
    ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag
        (mega.advanceControls frontState ⟨inputOne, inputTwo, .right⟩) := by
  dsimp only
  obtain ⟨entryTwo, nextFrontOne, nextOutputOne, hnext, hpending⟩ :=
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_exists
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo inputOne inputTwo
  exact
    ⟨profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo,
      entryTwo, nextFrontOne, nextOutputOne, hnext, hpending⟩

/- Actual-trace form of the strict-left mixed entry. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_globalStateTrace_mixedPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputTwo)))
    (hleft : (env start).graph = .left) :
    ProfiledRawJointHybridMegaLinkedLeftMixedPending A strategy hwin
      controllers initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).globalMachine.globalStateTrace env (start + 1)) := by
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hfront]
  rcases hround : env start with ⟨inputOne, inputTwo, graph⟩
  simp only [hround] at hleft
  subst graph
  exact
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_mixedPending
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo inputOne inputTwo

/- Actual-trace strict-right mirror. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_globalStateTrace_mixedPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputTwo)))
    (hright : (env start).graph = .right) :
    ProfiledRawJointHybridMegaLinkedRightMixedPending A strategy hwin
      controllers initialBank kernelTag
        ((MegaPhysicalController A strategy hwin controllers initialBank
          kernelTag).globalMachine.globalStateTrace env (start + 1)) := by
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hfront]
  rcases hround : env start with ⟨inputOne, inputTwo, graph⟩
  simp only [hround] at hright
  subst graph
  exact
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_mixedPending
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo inputOne inputTwo

/- In a persistent-reversal environment, a genuine strict-left front entry
reaches the common linked tail after finitely many actual rounds. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_eventually_tailPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputTwo)))
    (hleft : (env start).graph = .left)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ tailAt : Nat, start < tailAt ∧
      ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
        initialBank kernelTag
          ((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.globalStateTrace env tailAt) := by
  let mega := MegaPhysicalController A strategy hwin controllers initialBank
    kernelTag
  have hmixed :=
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_globalStateTrace_mixedPending
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo env start hfront hleft
  have hrevDrop : PersistentStrictReversalTail
      (fun n ↦ ((OmegaWord.drop env (start + 1)) n).graph) := by
    simpa [OmegaWord.drop] using
      (PersistentStrictReversalTail.drop hreversal (start + 1))
  rcases hmixed.exists_tail_of_persistentStrictReversal A strategy hwin
      controllers initialBank kernelTag (OmegaWord.drop env (start + 1))
        hrevDrop with ⟨close, htail⟩
  refine ⟨start + 1 + (close + 1), by omega, ?_⟩
  rw [← mega.globalMachine.reroot_globalStateTrace_drop env (start + 1)
    (close + 1)]
  exact htail

/- Persistent-reversal strict-right mirror. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_eventually_tailPending
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputTwo)))
    (hright : (env start).graph = .right)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ tailAt : Nat, start < tailAt ∧
      ProfiledRawJointHybridMegaLinkedTailPending A strategy hwin controllers
        initialBank kernelTag
          ((MegaPhysicalController A strategy hwin controllers initialBank
            kernelTag).globalMachine.globalStateTrace env tailAt) := by
  let mega := MegaPhysicalController A strategy hwin controllers initialBank
    kernelTag
  have hmixed :=
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_globalStateTrace_mixedPending
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo env start hfront hright
  have hrevDrop : PersistentStrictReversalTail
      (fun n ↦ ((OmegaWord.drop env (start + 1)) n).graph) := by
    simpa [OmegaWord.drop] using
      (PersistentStrictReversalTail.drop hreversal (start + 1))
  rcases hmixed.exists_tail_of_persistentStrictReversal A strategy hwin
      controllers initialBank kernelTag (OmegaWord.drop env (start + 1))
        hrevDrop with ⟨close, htail⟩
  refine ⟨start + 1 + (close + 1), by omega, ?_⟩
  rw [← mega.globalMachine.reroot_globalStateTrace_drop env (start + 1)
    (close + 1)]
  exact htail

/- Complete operational splice for a strict-left entry in the persistent
reversal regime. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_eventually_fullRestartReroot
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputTwo)))
    (hleft : (env start).graph = .left)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ (tailAt : Nat)
        (entryTag :
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
            strategy hwin)
        (controls : FullRestartPhysicalPair A strategy hwin),
      start < tailAt ∧
        FullRestartPhysicalPairAllPending A strategy hwin controls ∧
        OmegaWord.drop
            ((MegaPhysicalController A strategy hwin controllers initialBank
              kernelTag).globalMachine.globalMachineTraceWord
                (MegaPhysicalController A strategy hwin controllers initialBank
                  kernelTag).globalOutputOne
                (MegaPhysicalController A strategy hwin controllers initialBank
                  kernelTag).globalOutputTwo env) tailAt =
          (((LinkedPhysicalController A strategy hwin entryTag).globalMachine
            ).reroot controls).globalMachineTraceWord
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputOne
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputTwo (OmegaWord.drop env tailAt) := by
  rcases
      profiledRawJointHybridMegaLinkedUnconditional_leftEntry_strictLeft_eventually_tailPending
        A strategy hwin controllers initialBank kernelTag shadow owner
          oldOutputOne oldOutputTwo env start hfront hleft hreversal with
    ⟨tailAt, hstart, htail⟩
  rcases
      profiledRawJointHybridMegaLinkedTailPending_drop_traceWord_exists
        A strategy hwin controllers initialBank kernelTag env tailAt htail with
    ⟨entryTag, controls, hpending, hword⟩
  exact ⟨tailAt, entryTag, controls, hstart, hpending, hword⟩

/- Complete strict-right mirror. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_eventually_fullRestartReroot
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      (MegaPhysicalController A strategy hwin controllers initialBank
        kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputTwo)))
    (hright : (env start).graph = .right)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ (tailAt : Nat)
        (entryTag :
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
            strategy hwin)
        (controls : FullRestartPhysicalPair A strategy hwin),
      start < tailAt ∧
        FullRestartPhysicalPairAllPending A strategy hwin controls ∧
        OmegaWord.drop
            ((MegaPhysicalController A strategy hwin controllers initialBank
              kernelTag).globalMachine.globalMachineTraceWord
                (MegaPhysicalController A strategy hwin controllers initialBank
                  kernelTag).globalOutputOne
                (MegaPhysicalController A strategy hwin controllers initialBank
                  kernelTag).globalOutputTwo env) tailAt =
          (((LinkedPhysicalController A strategy hwin entryTag).globalMachine
            ).reroot controls).globalMachineTraceWord
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputOne
              (LinkedPhysicalController A strategy hwin entryTag
                ).globalOutputTwo (OmegaWord.drop env tailAt) := by
  rcases
      profiledRawJointHybridMegaLinkedUnconditional_rightEntry_strictRight_eventually_tailPending
        A strategy hwin controllers initialBank kernelTag shadow owner
          oldOutputOne oldOutputTwo env start hfront hright hreversal with
    ⟨tailAt, hstart, htail⟩
  rcases
      profiledRawJointHybridMegaLinkedTailPending_drop_traceWord_exists
        A strategy hwin controllers initialBank kernelTag env tailAt htail with
    ⟨entryTag, controls, hpending, hword⟩
  exact ⟨tailAt, entryTag, controls, hstart, hpending, hword⟩

theorem profiledRawJointHybridFullRestart_closeLeftMixed_allPending
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag).OneControl)
    (hone : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one.1)
    (round : EnvironmentRound In₁ In₂) :
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag
    FullRestartPhysicalPairAllPending A strategy hwin
      (linked.advanceControls (one, linked.initialTwo) round) := by
  dsimp only
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
  exact ⟨hone,
    (profiledRawJointHybridFullRestart_initial_allPending A strategy hwin
      tag).2⟩

/- Right-created mirror. -/
theorem profiledRawJointHybridFullRestart_closeRightMixed_allPending
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (two :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag).TwoControl)
    (htwo : FiniteAcknowledgedDelayedCarrier.CarrierAll
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two.1)
    (round : EnvironmentRound In₁ In₂) :
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin tag
    FullRestartPhysicalPairAllPending A strategy hwin
      (linked.advanceControls (linked.initialOne, two) round) := by
  dsimp only
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_allPending
  exact ⟨
    (profiledRawJointHybridFullRestart_initial_allPending A strategy hwin
      tag).1, htwo⟩

/- During a continuing left block, process one's selected local state has
`lastRecv = true`.  Both its open continuation and its exact closed candidate
therefore use process one's own authoritative child, so the complete fresh
receive packet is independent of the blind semantic process-two control. -/
theorem profiledRawJointHybridFullRestart_freshOne_two_irrel_of_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : FullRestartSemanticOne A strategy hwin)
    (leftTwo rightTwo : FullRestartSemanticTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (hrecv :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 one).2.1 = true) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          one inputOne leftTwo inputTwo =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          one inputOne rightTwo inputTwo := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    hrecv, if_pos]

/- The whole open/closed semantic receive fork inherits the same
independence, including its emitted output. -/
theorem profiledRawJointHybridFullRestart_recvForkOne_two_irrel_of_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : FullRestartSemanticOne A strategy hwin)
    (leftTwo rightTwo : FullRestartSemanticTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (hrecv :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 one).2.1 = true) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        one inputOne leftTwo inputTwo =
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        one inputOne rightTwo inputTwo := by
  dsimp only
  have hfresh :=
    profiledRawJointHybridFullRestart_freshOne_two_irrel_of_lastRecv
      A strategy hwin tag one leftTwo rightTwo inputOne inputTwo hrecv
  simp only [
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne]
  have hout := congrArg (fun fresh ↦ fresh.1.1) hfresh
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne]
    at hout
  rw [hfresh, hout]

/- Lifting through the finite acknowledgement shell: two resolved blind
partners with empty acknowledgement metadata are indistinguishable once the
informed semantic control is continuing its receive block. -/
theorem profiledRawJointHybridFullRestart_recvOne_knownTwo_irrel_of_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : FullRestartRelayOne A strategy hwin)
    (leftTwo rightTwo : FullRestartSemanticTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (hrecv :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one
            (⟨.known leftTwo, none⟩ : FullRestartRelayTwo A strategy hwin))
        ).2.1 = true) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let recvOne :=
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne one inputOne
        (⟨.known leftTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
        inputTwo =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne one inputOne
        (⟨.known rightTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
        inputTwo := by
  dsimp only
  let left : FullRestartRelayTwo A strategy hwin :=
    ⟨.known leftTwo, none⟩
  let right : FullRestartRelayTwo A strategy hwin :=
    ⟨.known rightTwo, none⟩
  have hresolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl one left =
        FiniteAcknowledgedDelayedCarrier.resolvedControl one right := by
    rcases one with ⟨current, ack⟩
    cases current <;>
      simp [left, right, FiniteAcknowledgedDelayedCarrier.resolvedControl,
        FiniteAcknowledgedDelayedCarrier.resolutionBit,
        FiniteAcknowledgedDelayedCarrier.currentId?]
  have htransition :=
    profiledRawJointHybridFullRestart_recvForkOne_two_irrel_of_lastRecv
      A strategy hwin tag
        (FiniteAcknowledgedDelayedCarrier.resolvedControl one left)
        leftTwo rightTwo inputOne inputTwo hrecv
  dsimp only at htransition
  have hleft :
      FiniteAcknowledgedDelayedCarrier.resolvedControl left one = leftTwo :=
    rfl
  have hright :
      FiniteAcknowledgedDelayedCarrier.resolvedControl right one = rightTwo :=
    rfl
  change
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ one inputOne left
        inputTwo =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ one inputOne right
        inputTwo
  simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
  rw [← hresolved, hleft, hright, htransition]
  rfl

/- At a left-to-right switch, process two has `lastRecv = false`.  Its fresh
right packet restarts entirely from the delivered process-one child, so it is
independent of which blind semantic process-two control carried the prefix. -/
theorem profiledRawJointHybridFullRestart_freshTwo_two_irrel_of_noRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftTwo rightTwo : FullRestartSemanticTwo A strategy hwin)
    (one : FullRestartSemanticOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁)
    (hleft :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 leftTwo).2.1 = false)
    (hright :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 rightTwo).2.1 = false) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          leftTwo inputTwo one inputOne =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          rightTwo inputTwo one inputOne := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
    hleft, hright, Bool.false_eq_true, ↓reduceIte]

/- Complete semantic process-two receive-fork version. -/
theorem profiledRawJointHybridFullRestart_recvForkTwo_two_irrel_of_noRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftTwo rightTwo : FullRestartSemanticTwo A strategy hwin)
    (one : FullRestartSemanticOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁)
    (hleft :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 leftTwo).2.1 = false)
    (hright :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 rightTwo).2.1 = false) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        leftTwo inputTwo one inputOne =
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        rightTwo inputTwo one inputOne := by
  dsimp only
  have hfresh :=
    profiledRawJointHybridFullRestart_freshTwo_two_irrel_of_noRecv
      A strategy hwin tag leftTwo rightTwo one inputTwo inputOne hleft hright
  simp only [
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo]
  have hout := congrArg (fun fresh ↦ fresh.1.1) hfresh
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo]
    at hout
  rw [hfresh, hout]

/- Outer acknowledged process-two receive version used by the first
left-to-right closing round. -/
theorem profiledRawJointHybridFullRestart_recvTwo_knownTwo_irrel_of_noRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftTwo rightTwo : FullRestartSemanticTwo A strategy hwin)
    (one : FullRestartRelayOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁)
    (hleft :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 leftTwo).2.1 = false)
    (hright :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 rightTwo).2.1 = false) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let recvTwo :=
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo
        (⟨.known leftTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
        inputTwo one inputOne =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo
        (⟨.known rightTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
        inputTwo one inputOne := by
  dsimp only
  let left : FullRestartRelayTwo A strategy hwin :=
    ⟨.known leftTwo, none⟩
  let right : FullRestartRelayTwo A strategy hwin :=
    ⟨.known rightTwo, none⟩
  have hresolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl one left =
        FiniteAcknowledgedDelayedCarrier.resolvedControl one right := by
    rcases one with ⟨current, ack⟩
    cases current <;>
      simp [left, right, FiniteAcknowledgedDelayedCarrier.resolvedControl,
        FiniteAcknowledgedDelayedCarrier.resolutionBit,
        FiniteAcknowledgedDelayedCarrier.currentId?]
  have htransition :=
    profiledRawJointHybridFullRestart_recvForkTwo_two_irrel_of_noRecv
      A strategy hwin tag leftTwo rightTwo
        (FiniteAcknowledgedDelayedCarrier.resolvedControl one right)
        inputTwo inputOne hleft hright
  dsimp only at htransition
  have hleftResolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl left one = leftTwo :=
    rfl
  have hrightResolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl right one = rightTwo :=
    rfl
  change
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ left inputTwo one
        inputOne =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ right inputTwo one
        inputOne
  simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
  rw [hresolved, hleftResolved, hrightResolved, htransition]
  rfl

/- A strict-left receive against one resolved blind relay installs an open
semantic control whose selected local receive bit is definitionally true. -/
theorem profiledRawJointHybridFullRestart_recvOne_knownTwo_next_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : FullRestartRelayOne A strategy hwin)
    (two : FullRestartSemanticTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let partner : FullRestartRelayTwo A strategy hwin :=
      ⟨.known two, none⟩
    let recvOne :=
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1
        (FiniteAcknowledgedDelayedCarrier.resolvedControl
          (FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne one
            inputOne partner inputTwo).1 partner)).2.1 = true := by
  dsimp only
  simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
  rw [FiniteAcknowledgedDelayedCarrier.resolvedControl_refork_old_open]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOne_openRecv_lastRecv
      A strategy hwin _ _ _ _ _

/- Right-block mirror: once process two is continuing a receive block, its
fresh packet is independent of the still-blind semantic process-one control. -/
theorem profiledRawJointHybridFullRestart_freshTwo_one_irrel_of_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (two : FullRestartSemanticTwo A strategy hwin)
    (leftOne rightOne : FullRestartSemanticOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁)
    (hrecv :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 two).2.1 = true) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          two inputTwo leftOne inputOne =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          two inputTwo rightOne inputOne := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
    hrecv, if_pos]

/- At a right-to-left switch, process one's fresh packet is independent of
which blind semantic process-one control carried the prefix. -/
theorem profiledRawJointHybridFullRestart_freshOne_one_irrel_of_noRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftOne rightOne : FullRestartSemanticOne A strategy hwin)
    (two : FullRestartSemanticTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (hleft :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 leftOne).2.1 = false)
    (hright :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 rightOne).2.1 = false) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          leftOne inputOne two inputTwo =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag)
          rightOne inputOne two inputTwo := by
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    hleft, hright, Bool.false_eq_true, ↓reduceIte]

theorem profiledRawJointHybridFullRestart_recvForkTwo_one_irrel_of_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (two : FullRestartSemanticTwo A strategy hwin)
    (leftOne rightOne : FullRestartSemanticOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁)
    (hrecv :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 two).2.1 = true) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        two inputTwo leftOne inputOne =
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        two inputTwo rightOne inputOne := by
  dsimp only
  have hfresh :=
    profiledRawJointHybridFullRestart_freshTwo_one_irrel_of_lastRecv
      A strategy hwin tag two leftOne rightOne inputTwo inputOne hrecv
  simp only [
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo]
  have hout := congrArg (fun fresh ↦ fresh.1.1) hfresh
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo]
    at hout
  rw [hfresh, hout]

theorem profiledRawJointHybridFullRestart_recvForkOne_one_irrel_of_noRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftOne rightOne : FullRestartSemanticOne A strategy hwin)
    (two : FullRestartSemanticTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (hleft :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 leftOne).2.1 = false)
    (hright :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 rightOne).2.1 = false) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        leftOne inputOne two inputTwo =
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
        rightOne inputOne two inputTwo := by
  dsimp only
  have hfresh :=
    profiledRawJointHybridFullRestart_freshOne_one_irrel_of_noRecv
      A strategy hwin tag leftOne rightOne two inputOne inputTwo hleft hright
  simp only [
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne]
  have hout := congrArg (fun fresh ↦ fresh.1.1) hfresh
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne]
    at hout
  rw [hfresh, hout]

theorem profiledRawJointHybridFullRestart_recvTwo_knownOne_irrel_of_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (two : FullRestartRelayTwo A strategy hwin)
    (leftOne rightOne : FullRestartSemanticOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁)
    (hrecv :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two
            (⟨.known leftOne, none⟩ : FullRestartRelayOne A strategy hwin))
        ).2.1 = true) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let recvTwo :=
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo two inputTwo
        (⟨.known leftOne, none⟩ : FullRestartRelayOne A strategy hwin)
        inputOne =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo two inputTwo
        (⟨.known rightOne, none⟩ : FullRestartRelayOne A strategy hwin)
        inputOne := by
  dsimp only
  let left : FullRestartRelayOne A strategy hwin := ⟨.known leftOne, none⟩
  let right : FullRestartRelayOne A strategy hwin := ⟨.known rightOne, none⟩
  have hresolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl two left =
        FiniteAcknowledgedDelayedCarrier.resolvedControl two right := by
    rcases two with ⟨current, ack⟩
    cases current <;>
      simp [left, right, FiniteAcknowledgedDelayedCarrier.resolvedControl,
        FiniteAcknowledgedDelayedCarrier.resolutionBit,
        FiniteAcknowledgedDelayedCarrier.currentId?]
  have htransition :=
    profiledRawJointHybridFullRestart_recvForkTwo_one_irrel_of_lastRecv
      A strategy hwin tag
        (FiniteAcknowledgedDelayedCarrier.resolvedControl two left)
        leftOne rightOne inputTwo inputOne hrecv
  dsimp only at htransition
  have hleft :
      FiniteAcknowledgedDelayedCarrier.resolvedControl left two = leftOne := rfl
  have hright :
      FiniteAcknowledgedDelayedCarrier.resolvedControl right two = rightOne :=
    rfl
  change
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ two inputTwo left
        inputOne =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ two inputTwo right
        inputOne
  simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
  rw [← hresolved, hleft, hright, htransition]
  rfl

theorem profiledRawJointHybridFullRestart_recvOne_knownOne_irrel_of_noRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (leftOne rightOne : FullRestartSemanticOne A strategy hwin)
    (two : FullRestartRelayTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (hleft :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 leftOne).2.1 = false)
    (hright :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 rightOne).2.1 = false) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let recvOne :=
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne
        (⟨.known leftOne, none⟩ : FullRestartRelayOne A strategy hwin)
        inputOne two inputTwo =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne
        (⟨.known rightOne, none⟩ : FullRestartRelayOne A strategy hwin)
        inputOne two inputTwo := by
  dsimp only
  let left : FullRestartRelayOne A strategy hwin := ⟨.known leftOne, none⟩
  let right : FullRestartRelayOne A strategy hwin := ⟨.known rightOne, none⟩
  have hresolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl two left =
        FiniteAcknowledgedDelayedCarrier.resolvedControl two right := by
    rcases two with ⟨current, ack⟩
    cases current <;>
      simp [left, right, FiniteAcknowledgedDelayedCarrier.resolvedControl,
        FiniteAcknowledgedDelayedCarrier.resolutionBit,
        FiniteAcknowledgedDelayedCarrier.currentId?]
  have htransition :=
    profiledRawJointHybridFullRestart_recvForkOne_one_irrel_of_noRecv
      A strategy hwin tag leftOne rightOne
        (FiniteAcknowledgedDelayedCarrier.resolvedControl two right)
        inputOne inputTwo hleft hright
  dsimp only at htransition
  have hleftResolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl left two = leftOne := rfl
  have hrightResolved :
      FiniteAcknowledgedDelayedCarrier.resolvedControl right two = rightOne :=
    rfl
  change
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ left inputOne two
        inputTwo =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy _ right inputOne two
        inputTwo
  simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
  rw [hresolved, hleftResolved, hrightResolved, htransition]
  rfl

theorem profiledRawJointHybridFullRestart_recvTwo_knownOne_next_lastRecv
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (two : FullRestartRelayTwo A strategy hwin)
    (one : FullRestartSemanticOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin tag
    let partner : FullRestartRelayOne A strategy hwin :=
      ⟨.known one, none⟩
    let recvTwo :=
      FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
          A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2
        (FiniteAcknowledgedDelayedCarrier.resolvedControl
          (FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo two
            inputTwo partner inputOne).1 partner)).2.1 = true := by
  dsimp only
  simp only [FiniteAcknowledgedDelayedCarrier.recvReforkMealy]
  rw [FiniteAcknowledgedDelayedCarrier.resolvedControl_refork_old_open]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwo_openRecv_lastRecv
      A strategy hwin _ _ _ _ _

private noncomputable def profiledRawJointHybridFullRestartInitialSemanticTwo
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin) : FullRestartSemanticTwo A strategy hwin :=
  .inl
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
      A strategy hwin tag)

private noncomputable def profiledRawJointHybridFullRestartInitialSemanticOne
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin) : FullRestartSemanticOne A strategy hwin :=
  .inl
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
      A strategy hwin tag)

/- Symmetric lockstep invariant after at least one strict-right round. -/
def ProfiledRawJointHybridFullRestartRightBlockAligned
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedTwo : (LinkedPhysicalController A strategy hwin tag).TwoControl)
    (canonical : FullRestartPhysicalPair A strategy hwin) : Prop :=
  mixedTwo = canonical.2 ∧
    ∃ one : FullRestartSemanticOne A strategy hwin,
      canonical.1.1 = ⟨.known one, none⟩ ∧
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending one ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2
          (FiniteAcknowledgedDelayedCarrier.resolvedControl mixedTwo.1
            (LinkedPhysicalController A strategy hwin tag).initialOne.1)
        ).2.1 = true ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 one).2.1 = false

theorem ProfiledRawJointHybridFullRestartRightBlockAligned.advance_right
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedTwo : (LinkedPhysicalController A strategy hwin tag).TwoControl)
    (canonical : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .right)
    (aligned : ProfiledRawJointHybridFullRestartRightBlockAligned
      A strategy hwin tag mixedTwo canonical) :
    let linked := LinkedPhysicalController A strategy hwin tag
    ProfiledRawJointHybridFullRestartRightBlockAligned A strategy hwin tag
      (linked.advanceControls (linked.initialOne, mixedTwo) round).2
      (linked.advanceControls canonical round) := by
  dsimp only
  rcases aligned with ⟨hmixed, one, hshape, hpending, hrecv, hblind⟩
  subst mixedTwo
  rcases canonical with ⟨canonicalOne, two⟩
  rcases canonicalOne with ⟨canonicalOneRelay, oneOutput⟩
  rcases two with ⟨twoRelay, twoOutput⟩
  change canonicalOneRelay = ⟨.known one, none⟩ at hshape
  subst canonicalOneRelay
  let initialOne :=
    profiledRawJointHybridFullRestartInitialSemanticOne A strategy hwin tag
  let recvTwo :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  let nextTwo := FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo
    twoRelay round.inputTwo
      (⟨.known initialOne, none⟩ : FullRestartRelayOne A strategy hwin)
    round.inputOne
  let noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin
  let nextOne := noRecvOne one round.inputOne
  have htwo : nextTwo =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo twoRelay
        round.inputTwo
          (⟨.known one, none⟩ : FullRestartRelayOne A strategy hwin)
        round.inputOne := by
    exact
      profiledRawJointHybridFullRestart_recvTwo_knownOne_irrel_of_lastRecv
        A strategy hwin tag twoRelay initialOne one round.inputTwo
          round.inputOne hrecv
  have hpendingNext :
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending nextOne.1 := by
    exact
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv_isPending
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
          A strategy hwin)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
          (Out₁ := Out₁)) one round.inputOne hpending
  have hblindNext :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 nextOne.1).2.1 = false := by
    cases one with
    | inl pending =>
        exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv
            A strategy hwin _ pending round.inputOne
    | inr recurrent => exact False.elim hpending
  have hrecvNext :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2
          (FiniteAcknowledgedDelayedCarrier.resolvedControl nextTwo.1
            (LinkedPhysicalController A strategy hwin tag).initialOne.1)
        ).2.1 = true := by
    exact
      profiledRawJointHybridFullRestart_recvTwo_knownOne_next_lastRecv
        A strategy hwin tag twoRelay initialOne round.inputTwo round.inputOne
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  change ProfiledRawJointHybridFullRestartRightBlockAligned A strategy hwin tag
    nextTwo
    ((FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvOne
        (⟨.known one, none⟩ : FullRestartRelayOne A strategy hwin)
        round.inputOne),
      (FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo twoRelay
        round.inputTwo
          (⟨.known one, none⟩ : FullRestartRelayOne A strategy hwin)
        round.inputOne))
  refine ⟨htwo, nextOne.1, ?_, hpendingNext, hrecvNext, hblindNext⟩
  rfl

/- Lockstep invariant after at least one strict-left round of a block.  The
mixed run has forgotten process two's physical prefix, but its informed
process-one control is canonical; the canonical blind relay stays resolved
and acknowledgement-free. -/
def ProfiledRawJointHybridFullRestartLeftBlockAligned
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedOne : (LinkedPhysicalController A strategy hwin tag).OneControl)
    (canonical : FullRestartPhysicalPair A strategy hwin) : Prop :=
  mixedOne = canonical.1 ∧
    ∃ two : FullRestartSemanticTwo A strategy hwin,
      canonical.2.1 = ⟨.known two, none⟩ ∧
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending two ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1
          (FiniteAcknowledgedDelayedCarrier.resolvedControl mixedOne.1
            (LinkedPhysicalController A strategy hwin tag).initialTwo.1)
        ).2.1 = true ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 two).2.1 = false

/- One further strict-left round preserves the lockstep invariant. -/
theorem ProfiledRawJointHybridFullRestartLeftBlockAligned.advance_left
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedOne : (LinkedPhysicalController A strategy hwin tag).OneControl)
    (canonical : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .left)
    (aligned : ProfiledRawJointHybridFullRestartLeftBlockAligned
      A strategy hwin tag mixedOne canonical) :
    let linked := LinkedPhysicalController A strategy hwin tag
    ProfiledRawJointHybridFullRestartLeftBlockAligned A strategy hwin tag
      (linked.advanceControls (mixedOne, linked.initialTwo) round).1
      (linked.advanceControls canonical round) := by
  dsimp only
  rcases aligned with ⟨hmixed, two, hshape, hpending, hrecv, hblind⟩
  subst mixedOne
  rcases canonical with ⟨one, canonicalTwo⟩
  rcases one with ⟨oneRelay, oneOutput⟩
  rcases canonicalTwo with ⟨canonicalTwoRelay, twoOutput⟩
  change canonicalTwoRelay = ⟨.known two, none⟩ at hshape
  subst canonicalTwoRelay
  let initialTwo :=
    profiledRawJointHybridFullRestartInitialSemanticTwo A strategy hwin tag
  let recvOne :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  let nextOne := FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne
    oneRelay round.inputOne
      (⟨.known initialTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
    round.inputTwo
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin
  let nextTwo := noRecvTwo two round.inputTwo
  have hone : nextOne =
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne oneRelay
        round.inputOne
          (⟨.known two, none⟩ : FullRestartRelayTwo A strategy hwin)
        round.inputTwo := by
    exact
      profiledRawJointHybridFullRestart_recvOne_knownTwo_irrel_of_lastRecv
        A strategy hwin tag oneRelay initialTwo two round.inputOne
          round.inputTwo hrecv
  have hpendingNext :
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending nextTwo.1 := by
    exact
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv_isPending
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
          A strategy hwin)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
          (Out₂ := Out₂)) two round.inputTwo hpending
  have hblindNext :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 nextTwo.1).2.1 = false := by
    cases two with
    | inl pending =>
        exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwo_noRecv_lastRecv
            A strategy hwin _ pending round.inputTwo
    | inr recurrent => exact False.elim hpending
  have hrecvNext :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1
          (FiniteAcknowledgedDelayedCarrier.resolvedControl nextOne.1
            (LinkedPhysicalController A strategy hwin tag).initialTwo.1)
        ).2.1 = true := by
    exact
      profiledRawJointHybridFullRestart_recvOne_knownTwo_next_lastRecv
        A strategy hwin tag oneRelay initialTwo round.inputOne round.inputTwo
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  change ProfiledRawJointHybridFullRestartLeftBlockAligned A strategy hwin tag
    nextOne
    ((FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne oneRelay
        round.inputOne
          (⟨.known two, none⟩ : FullRestartRelayTwo A strategy hwin)
        round.inputTwo),
      (FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvTwo
        (⟨.known two, none⟩ : FullRestartRelayTwo A strategy hwin)
        round.inputTwo))
  refine ⟨hone, nextTwo.1, ?_, hpendingNext, hrecvNext, hblindNext⟩
  rfl

/- The first strict-left round establishes the lockstep invariant from the
canonical initial pair. -/
theorem profiledRawJointHybridFullRestart_initial_advance_left_aligned
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .left) :
    let linked := LinkedPhysicalController A strategy hwin tag
    let initial := (linked.initialOne, linked.initialTwo)
    ProfiledRawJointHybridFullRestartLeftBlockAligned A strategy hwin tag
      (linked.advanceControls initial round).1
      (linked.advanceControls initial round) := by
  dsimp only
  let linked := LinkedPhysicalController A strategy hwin tag
  let initialTwo :=
    profiledRawJointHybridFullRestartInitialSemanticTwo A strategy hwin tag
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin
  let nextTwo := noRecvTwo initialTwo round.inputTwo
  have hpendingInitial :
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending initialTwo :=
    trivial
  have hpendingNext :
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending nextTwo.1 := by
    exact
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv_isPending
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
          A strategy hwin)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
          (Out₂ := Out₂)) initialTwo round.inputTwo hpendingInitial
  have hrecvNext :=
    profiledRawJointHybridFullRestart_recvOne_knownTwo_next_lastRecv
      A strategy hwin tag linked.initialOne.1 initialTwo round.inputOne
        round.inputTwo
  have hblindNext :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 nextTwo.1).2.1 = false := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwo_noRecv_lastRecv
        A strategy hwin _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
            A strategy hwin tag) round.inputTwo
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  refine ⟨rfl, nextTwo.1, rfl, hpendingNext, ?_, hblindNext⟩
  exact hrecvNext

/- At the first opposite receive, a left-block mixed pair and its canonical
lockstep state become literally the same complete FullRestart pair. -/
theorem ProfiledRawJointHybridFullRestartLeftBlockAligned.close_right
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedOne : (LinkedPhysicalController A strategy hwin tag).OneControl)
    (canonical : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .right)
    (aligned : ProfiledRawJointHybridFullRestartLeftBlockAligned
      A strategy hwin tag mixedOne canonical) :
    let linked := LinkedPhysicalController A strategy hwin tag
    linked.advanceControls (mixedOne, linked.initialTwo) round =
      linked.advanceControls canonical round := by
  dsimp only
  rcases aligned with ⟨hmixed, two, hshape, _hpending, _hrecv, hblind⟩
  subst mixedOne
  rcases canonical with ⟨one, canonicalTwo⟩
  rcases one with ⟨oneRelay, oneOutput⟩
  rcases canonicalTwo with ⟨canonicalTwoRelay, twoOutput⟩
  change canonicalTwoRelay = ⟨.known two, none⟩ at hshape
  subst canonicalTwoRelay
  let initialTwo :=
    profiledRawJointHybridFullRestartInitialSemanticTwo A strategy hwin tag
  let recvTwo :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  have hinitialBlind :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 initialTwo).2.1 = false :=
    rfl
  have htwo :
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo
          (⟨.known initialTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
          round.inputTwo oneRelay round.inputOne =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo
          (⟨.known two, none⟩ : FullRestartRelayTwo A strategy hwin)
          round.inputTwo oneRelay round.inputOne := by
    exact
      profiledRawJointHybridFullRestart_recvTwo_knownTwo_irrel_of_noRecv
        A strategy hwin tag initialTwo two oneRelay round.inputTwo
          round.inputOne hinitialBlind hblind
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  apply Prod.ext
  · rfl
  · exact htwo

/- At a simultaneous close, the continuing process-one receive is
independent of the blind process-two prefix, while the newly receiving
process-two packet is independent of its own blind prefix.  Thus the mixed
and canonical pairs again take exactly the same physical step. -/
theorem ProfiledRawJointHybridFullRestartLeftBlockAligned.close_both
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedOne : (LinkedPhysicalController A strategy hwin tag).OneControl)
    (canonical : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .both)
    (aligned : ProfiledRawJointHybridFullRestartLeftBlockAligned
      A strategy hwin tag mixedOne canonical) :
    let linked := LinkedPhysicalController A strategy hwin tag
    linked.advanceControls (mixedOne, linked.initialTwo) round =
      linked.advanceControls canonical round := by
  dsimp only
  rcases aligned with ⟨hmixed, two, hshape, _hpending, hrecv, hblind⟩
  subst mixedOne
  rcases canonical with ⟨one, canonicalTwo⟩
  rcases one with ⟨oneRelay, oneOutput⟩
  rcases canonicalTwo with ⟨canonicalTwoRelay, twoOutput⟩
  change canonicalTwoRelay = ⟨.known two, none⟩ at hshape
  subst canonicalTwoRelay
  let initialTwo :=
    profiledRawJointHybridFullRestartInitialSemanticTwo A strategy hwin tag
  let recvOne :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  let recvTwo :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  have hone :
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne oneRelay
          round.inputOne
          (⟨.known initialTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
          round.inputTwo =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne oneRelay
          round.inputOne
          (⟨.known two, none⟩ : FullRestartRelayTwo A strategy hwin)
          round.inputTwo := by
    exact
      profiledRawJointHybridFullRestart_recvOne_knownTwo_irrel_of_lastRecv
        A strategy hwin tag oneRelay initialTwo two round.inputOne
          round.inputTwo hrecv
  have hinitialBlind :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).2 initialTwo).2.1 = false :=
    rfl
  have htwo :
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo
          (⟨.known initialTwo, none⟩ : FullRestartRelayTwo A strategy hwin)
          round.inputTwo oneRelay round.inputOne =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo
          (⟨.known two, none⟩ : FullRestartRelayTwo A strategy hwin)
          round.inputTwo oneRelay round.inputOne := by
    exact
      profiledRawJointHybridFullRestart_recvTwo_knownTwo_irrel_of_noRecv
        A strategy hwin tag initialTwo two oneRelay round.inputTwo
          round.inputOne hinitialBlind hblind
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  apply Prod.ext
  · exact hone
  · exact htwo

/- The first strict-right round establishes the mirror lockstep invariant. -/
theorem profiledRawJointHybridFullRestart_initial_advance_right_aligned
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .right) :
    let linked := LinkedPhysicalController A strategy hwin tag
    let initial := (linked.initialOne, linked.initialTwo)
    ProfiledRawJointHybridFullRestartRightBlockAligned A strategy hwin tag
      (linked.advanceControls initial round).2
      (linked.advanceControls initial round) := by
  dsimp only
  let linked := LinkedPhysicalController A strategy hwin tag
  let initialOne :=
    profiledRawJointHybridFullRestartInitialSemanticOne A strategy hwin tag
  let noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin
  let nextOne := noRecvOne initialOne round.inputOne
  have hpendingInitial :
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending initialOne :=
    trivial
  have hpendingNext :
      FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending nextOne.1 := by
    exact
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv_isPending
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
          A strategy hwin)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
          (Out₁ := Out₁)) initialOne round.inputOne hpendingInitial
  have hrecvNext :=
    profiledRawJointHybridFullRestart_recvTwo_knownOne_next_lastRecv
      A strategy hwin tag linked.initialTwo.1 initialOne round.inputTwo
        round.inputOne
  have hblindNext :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 nextOne.1).2.1 = false := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv
        A strategy hwin _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
            A strategy hwin tag) round.inputOne
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  refine ⟨rfl, nextOne.1, rfl, hpendingNext, ?_, hblindNext⟩
  exact hrecvNext

/- At the first strict-left round, a right-block mixed pair and its canonical
lockstep state become the same complete FullRestart pair. -/
theorem ProfiledRawJointHybridFullRestartRightBlockAligned.close_left
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedTwo : (LinkedPhysicalController A strategy hwin tag).TwoControl)
    (canonical : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .left)
    (aligned : ProfiledRawJointHybridFullRestartRightBlockAligned
      A strategy hwin tag mixedTwo canonical) :
    let linked := LinkedPhysicalController A strategy hwin tag
    linked.advanceControls (linked.initialOne, mixedTwo) round =
      linked.advanceControls canonical round := by
  dsimp only
  rcases aligned with ⟨hmixed, one, hshape, _hpending, _hrecv, hblind⟩
  subst mixedTwo
  rcases canonical with ⟨canonicalOne, two⟩
  rcases canonicalOne with ⟨canonicalOneRelay, oneOutput⟩
  rcases two with ⟨twoRelay, twoOutput⟩
  change canonicalOneRelay = ⟨.known one, none⟩ at hshape
  subst canonicalOneRelay
  let initialOne :=
    profiledRawJointHybridFullRestartInitialSemanticOne A strategy hwin tag
  let recvOne :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  have hinitialBlind :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 initialOne).2.1 = false :=
    rfl
  have hone :
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne
          (⟨.known initialOne, none⟩ : FullRestartRelayOne A strategy hwin)
          round.inputOne twoRelay round.inputTwo =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne
          (⟨.known one, none⟩ : FullRestartRelayOne A strategy hwin)
          round.inputOne twoRelay round.inputTwo := by
    exact
      profiledRawJointHybridFullRestart_recvOne_knownOne_irrel_of_noRecv
        A strategy hwin tag initialOne one twoRelay round.inputOne
          round.inputTwo hinitialBlind hblind
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  apply Prod.ext
  · exact hone
  · rfl

/- Simultaneous mirror of `LeftBlockAligned.close_both`. -/
theorem ProfiledRawJointHybridFullRestartRightBlockAligned.close_both
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (mixedTwo : (LinkedPhysicalController A strategy hwin tag).TwoControl)
    (canonical : FullRestartPhysicalPair A strategy hwin)
    (round : EnvironmentRound In₁ In₂)
    (hgraph : round.graph = .both)
    (aligned : ProfiledRawJointHybridFullRestartRightBlockAligned
      A strategy hwin tag mixedTwo canonical) :
    let linked := LinkedPhysicalController A strategy hwin tag
    linked.advanceControls (linked.initialOne, mixedTwo) round =
      linked.advanceControls canonical round := by
  dsimp only
  rcases aligned with ⟨hmixed, one, hshape, _hpending, hrecv, hblind⟩
  subst mixedTwo
  rcases canonical with ⟨canonicalOne, two⟩
  rcases canonicalOne with ⟨canonicalOneRelay, oneOutput⟩
  rcases two with ⟨twoRelay, twoOutput⟩
  change canonicalOneRelay = ⟨.known one, none⟩ at hshape
  subst canonicalOneRelay
  let initialOne :=
    profiledRawJointHybridFullRestartInitialSemanticOne A strategy hwin tag
  let recvOne :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  let recvTwo :=
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag))
  have hinitialBlind :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
            A strategy hwin tag).1 initialOne).2.1 = false :=
    rfl
  have hone :
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne
          (⟨.known initialOne, none⟩ : FullRestartRelayOne A strategy hwin)
          round.inputOne twoRelay round.inputTwo =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne
          (⟨.known one, none⟩ : FullRestartRelayOne A strategy hwin)
          round.inputOne twoRelay round.inputTwo := by
    exact
      profiledRawJointHybridFullRestart_recvOne_knownOne_irrel_of_noRecv
        A strategy hwin tag initialOne one twoRelay round.inputOne
          round.inputTwo hinitialBlind hblind
  have htwo :
      FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo twoRelay
          round.inputTwo
          (⟨.known initialOne, none⟩ : FullRestartRelayOne A strategy hwin)
          round.inputOne =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo twoRelay
          round.inputTwo
          (⟨.known one, none⟩ : FullRestartRelayOne A strategy hwin)
          round.inputOne := by
    exact
      profiledRawJointHybridFullRestart_recvTwo_knownOne_irrel_of_lastRecv
        A strategy hwin tag twoRelay initialOne one round.inputTwo
          round.inputOne hrecv
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  simp only [profiledRawJointHybridFullRestartPhysicalAdvance, hgraph]
  apply Prod.ext
  · exact hone
  · exact htwo

private noncomputable def profiledRawJointHybridFullRestartLeftMixedOneTrace
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : Nat →
    (LinkedPhysicalController A strategy hwin tag).OneControl
  | 0 => (LinkedPhysicalController A strategy hwin tag).initialOne
  | n + 1 =>
      let linked := LinkedPhysicalController A strategy hwin tag
      (linked.advanceControls
        (profiledRawJointHybridFullRestartLeftMixedOneTrace tag env n,
          linked.initialTwo) (env n)).1

/- Arbitrarily many strict-left rounds keep the mixed informed control in
lockstep with the canonical FullRestart trace. -/
theorem profiledRawJointHybridFullRestart_leftMixedTrace_aligned
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hleft : ∀ k < n, (env k).graph = .left) :
    let linked := LinkedPhysicalController A strategy hwin tag
    ProfiledRawJointHybridFullRestartLeftBlockAligned A strategy hwin tag
      (profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin tag
        env n)
      (linked.globalMachine.globalStateTrace env n) := by
  dsimp only
  induction n with
  | zero => simp at hpos
  | succ n ih =>
      cases n with
      | zero =>
          rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
          simpa [profiledRawJointHybridFullRestartLeftMixedOneTrace] using
            (profiledRawJointHybridFullRestart_initial_advance_left_aligned
              A strategy hwin tag (env 0) (hleft 0 (by omega)))
      | succ n =>
          have hprefix : ∀ k < n + 1, (env k).graph = .left := by
            intro k hk
            exact hleft k (by omega)
          have haligned := ih (by omega) hprefix
          have hstep :=
            ProfiledRawJointHybridFullRestartLeftBlockAligned.advance_left
              A strategy hwin tag
                (profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy
                  hwin tag env (n + 1))
                ((LinkedPhysicalController A strategy hwin tag).globalMachine.globalStateTrace
                  env (n + 1))
                (env (n + 1)) (hleft (n + 1) (by omega)) haligned
          rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
          simpa [profiledRawJointHybridFullRestartLeftMixedOneTrace] using hstep

/- Exact arbitrary-depth convergence at the first strict-right round. -/
theorem profiledRawJointHybridFullRestart_leftMixedTrace_close_right
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hleft : ∀ k < n, (env k).graph = .left)
    (hright : (env n).graph = .right) :
    let linked := LinkedPhysicalController A strategy hwin tag
    linked.advanceControls
        (profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin tag
          env n, linked.initialTwo) (env n) =
      linked.globalMachine.globalStateTrace env (n + 1) := by
  dsimp only
  have haligned :=
    profiledRawJointHybridFullRestart_leftMixedTrace_aligned A strategy hwin
      tag env n hpos hleft
  have hclose :=
    ProfiledRawJointHybridFullRestartLeftBlockAligned.close_right A strategy
      hwin tag
        (profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin tag
          env n)
        ((LinkedPhysicalController A strategy hwin tag).globalMachine.globalStateTrace
          env n)
        (env n) hright haligned
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
  exact hclose

private noncomputable def profiledRawJointHybridFullRestartRightMixedTwoTrace
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : Nat →
    (LinkedPhysicalController A strategy hwin tag).TwoControl
  | 0 => (LinkedPhysicalController A strategy hwin tag).initialTwo
  | n + 1 =>
      let linked := LinkedPhysicalController A strategy hwin tag
      (linked.advanceControls
        (linked.initialOne,
          profiledRawJointHybridFullRestartRightMixedTwoTrace tag env n)
        (env n)).2

/- Arbitrarily many strict-right rounds keep the mirror mixed control in
lockstep with the canonical FullRestart trace. -/
theorem profiledRawJointHybridFullRestart_rightMixedTrace_aligned
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hright : ∀ k < n, (env k).graph = .right) :
    let linked := LinkedPhysicalController A strategy hwin tag
    ProfiledRawJointHybridFullRestartRightBlockAligned A strategy hwin tag
      (profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin tag
        env n)
      (linked.globalMachine.globalStateTrace env n) := by
  dsimp only
  induction n with
  | zero => simp at hpos
  | succ n ih =>
      cases n with
      | zero =>
          rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
          simpa [profiledRawJointHybridFullRestartRightMixedTwoTrace] using
            (profiledRawJointHybridFullRestart_initial_advance_right_aligned
              A strategy hwin tag (env 0) (hright 0 (by omega)))
      | succ n =>
          have hprefix : ∀ k < n + 1, (env k).graph = .right := by
            intro k hk
            exact hright k (by omega)
          have haligned := ih (by omega) hprefix
          have hstep :=
            ProfiledRawJointHybridFullRestartRightBlockAligned.advance_right
              A strategy hwin tag
                (profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy
                  hwin tag env (n + 1))
                ((LinkedPhysicalController A strategy hwin tag).globalMachine.globalStateTrace
                  env (n + 1))
                (env (n + 1)) (hright (n + 1) (by omega)) haligned
          rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
          simpa [profiledRawJointHybridFullRestartRightMixedTwoTrace] using hstep

/- Exact arbitrary-depth mirror convergence at the first strict-left round. -/
theorem profiledRawJointHybridFullRestart_rightMixedTrace_close_left
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hright : ∀ k < n, (env k).graph = .right)
    (hleft : (env n).graph = .left) :
    let linked := LinkedPhysicalController A strategy hwin tag
    linked.advanceControls
        (linked.initialOne,
          profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin
            tag env n) (env n) =
      linked.globalMachine.globalStateTrace env (n + 1) := by
  dsimp only
  have haligned :=
    profiledRawJointHybridFullRestart_rightMixedTrace_aligned A strategy hwin
      tag env n hpos hright
  have hclose :=
    ProfiledRawJointHybridFullRestartRightBlockAligned.close_left A strategy
      hwin tag
        (profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin tag
          env n)
        ((LinkedPhysicalController A strategy hwin tag).globalMachine.globalStateTrace
          env n)
        (env n) hleft haligned
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
  exact hclose

/- Stored Moore outputs are not transition inputs.  Replacing either old
output while keeping both acknowledged relays fixed leaves the next physical
FullRestart pair unchanged. -/
theorem profiledRawJointHybridFullRestart_advanceControls_output_irrel
    (tag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (one : FullRestartRelayOne A strategy hwin)
    (two : FullRestartRelayTwo A strategy hwin)
    (leftOutputOne rightOutputOne : Out₁)
    (leftOutputTwo rightOutputTwo : Out₂)
    (round : EnvironmentRound In₁ In₂) :
    let linked := LinkedPhysicalController A strategy hwin tag
    linked.advanceControls
        ((one, leftOutputOne), (two, leftOutputTwo)) round =
      linked.advanceControls
        ((one, rightOutputOne), (two, rightOutputTwo)) round := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_advanceControls_eq_explicit]
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> rfl

/- Exact simulation of a nonempty strict-left mixed mega prefix by the pure
mixed FullRestart trace. -/
theorem profiledRawJointHybridMegaLinked_leftMixed_initial_exactTrace_succ
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (entryOutputOne : Out₁)
    (frontTwo : MegaOldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hleft : ∀ k < n + 1, (env k).graph = .left) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let linked := LinkedPhysicalController A strategy hwin entryTag
    let initialState :=
      ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (entryTag, linked.initialOne.1),
          entryOutputOne),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank frontTwo, frontOutputTwo))
    ∃ (nextFrontTwo : MegaOldTwo A strategy hwin controllers initialBank)
        (nextOutputTwo : Out₂),
      ((mega.globalMachine.reroot initialState).globalStateTrace env (n + 1)) =
        ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
            controllers initialBank
              (entryTag,
                (profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy
                  hwin entryTag env (n + 1)).1),
            (profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin
              entryTag env (n + 1)).2),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank nextFrontTwo, nextOutputTwo)) ∧
      FiniteAcknowledgedDelayedCarrier.CarrierAll
        FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending
          (profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin
            entryTag env (n + 1)).1 := by
  dsimp only
  let mega := MegaPhysicalController A strategy hwin controllers initialBank
    kernelTag
  let linked := LinkedPhysicalController A strategy hwin entryTag
  induction n with
  | zero =>
      have hgraph := hleft 0 (by omega)
      rcases hround : env 0 with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      let entryOne : linked.OneControl :=
        (linked.initialOne.1, entryOutputOne)
      obtain ⟨nextOne, nextFrontTwo, nextOutputTwo, hstep, hnext,
          hpending⟩ :=
        profiledRawJointHybridMegaLinked_leftMixed_strictLeft_exists A strategy
          hwin controllers initialBank kernelTag entryTag entryOne
          (profiledRawJointHybridFullRestart_initial_allPending A strategy hwin
            entryTag).1 frontTwo frontOutputTwo inputOne inputTwo
      have hout :=
        profiledRawJointHybridFullRestart_advanceControls_output_irrel A
          strategy hwin entryTag linked.initialOne.1 linked.initialTwo.1
          linked.initialOne.2 entryOutputOne linked.initialTwo.2
          linked.initialTwo.2 ⟨inputOne, inputTwo, .left⟩
      have hnextCanonical : nextOne =
          profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin
            entryTag env 1 := by
        rw [hnext]
        change
          (linked.advanceControls (entryOne, linked.initialTwo)
              ⟨inputOne, inputTwo, .left⟩).1 = _
        simpa [profiledRawJointHybridFullRestartLeftMixedOneTrace, hround] using
          congrArg Prod.fst hout.symm
      rw [hnextCanonical] at hstep hpending
      refine ⟨nextFrontTwo, nextOutputTwo, ?_, hpending⟩
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
        FiniteGlobalRoundMachine.globalStateTrace_zero, hround]
      change mega.advanceControls
        ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
            controllers initialBank (entryTag, linked.initialOne.1),
            entryOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank frontTwo, frontOutputTwo))
          ⟨inputOne, inputTwo, .left⟩ = _
      exact hstep
  | succ n ih =>
      have hprefix : ∀ k < n + 1, (env k).graph = .left := by
        intro k hk
        exact hleft k (by omega)
      obtain ⟨frontAt, outputAt, hstate, hpending⟩ := ih hprefix
      have hgraph := hleft (n + 1) (by omega)
      rcases hround : env (n + 1) with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      let one :=
        profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin
          entryTag env (n + 1)
      obtain ⟨nextOne, nextFrontTwo, nextOutputTwo, hstep, hnext,
          hpendingNext⟩ :=
        profiledRawJointHybridMegaLinked_leftMixed_strictLeft_exists A strategy
          hwin controllers initialBank kernelTag entryTag one hpending frontAt
            outputAt inputOne inputTwo
      have hnextTrace : nextOne =
          profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin
            entryTag env (n + 2) := by
        rw [hnext]
        simp [profiledRawJointHybridFullRestartLeftMixedOneTrace, one, hround]
      rw [hnextTrace] at hstep hpendingNext
      refine ⟨nextFrontTwo, nextOutputTwo, ?_, hpendingNext⟩
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hstate, hround]
      change mega.advanceControls
        ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
            controllers initialBank (entryTag, one.1), one.2),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank frontAt, outputAt))
          ⟨inputOne, inputTwo, .left⟩ = _
      exact hstep

/- At the first strict-right round after a nonempty strict-left mixed block,
the concrete mega run reaches exactly the canonical `FullRestart` state. -/
theorem profiledRawJointHybridMegaLinked_leftMixed_initial_exactTrace_close_right
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (entryOutputOne : Out₁)
    (frontTwo : MegaOldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hleft : ∀ k < n, (env k).graph = .left)
    (hright : (env n).graph = .right) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let linked := LinkedPhysicalController A strategy hwin entryTag
    let initialState :=
      ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (entryTag, linked.initialOne.1),
          entryOutputOne),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank frontTwo, frontOutputTwo))
    let canonical := linked.globalMachine.globalStateTrace env (n + 1)
    ((mega.globalMachine.reroot initialState).globalStateTrace env (n + 1)) =
      ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (entryTag, canonical.1.1), canonical.1.2),
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (entryTag, canonical.2.1), canonical.2.2)) := by
  dsimp only
  cases n with
  | zero => omega
  | succ n =>
      obtain ⟨frontAt, outputAt, hstate, _⟩ :=
        profiledRawJointHybridMegaLinked_leftMixed_initial_exactTrace_succ A
          strategy hwin controllers initialBank kernelTag entryTag
            entryOutputOne frontTwo frontOutputTwo env n hleft
      have hgraph := hright
      rcases hround : env (n + 1) with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      let one :=
        profiledRawJointHybridFullRestartLeftMixedOneTrace A strategy hwin
          entryTag env (n + 1)
      let maps :=
        profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy
          hwin controllers initialBank
            (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A
              strategy hwin controllers initialBank)
      have hclose :=
        profiledRawJointHybridMegaLinkedCloseLeftMixed_strictRight A strategy
          hwin controllers initialBank entryTag maps one frontAt outputAt
            inputOne inputTwo
      have hcanonical :=
        profiledRawJointHybridFullRestart_leftMixedTrace_close_right A strategy
          hwin entryTag env (n + 1) (by omega) hleft hright
      rw [hround] at hcanonical
      rw [hcanonical] at hclose
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hstate, hround]
      simpa [MegaPhysicalController, maps, one] using hclose

/- Consequently, after that closing round the complete concrete mega suffix is
literally the corresponding suffix of the canonical `FullRestart` word. -/
theorem profiledRawJointHybridMegaLinked_leftMixed_initial_drop_eq_fullRestart_drop
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (entryOutputOne : Out₁)
    (frontTwo : MegaOldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hleft : ∀ k < n, (env k).graph = .left)
    (hright : (env n).graph = .right) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let linked := LinkedPhysicalController A strategy hwin entryTag
    let initialState :=
      ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (entryTag, linked.initialOne.1),
          entryOutputOne),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank frontTwo, frontOutputTwo))
    let actualWord :=
      (mega.globalMachine.reroot initialState).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env
    OmegaWord.drop actualWord (n + 1) =
      OmegaWord.drop
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin entryTag env) (n + 1) := by
  dsimp only
  let mega := MegaPhysicalController A strategy hwin controllers initialBank
    kernelTag
  let linked := LinkedPhysicalController A strategy hwin entryTag
  let initialState :=
    ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin controllers
        initialBank (entryTag, linked.initialOne.1), entryOutputOne),
      (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
        initialBank frontTwo, frontOutputTwo))
  let canonical := linked.globalMachine.globalStateTrace env (n + 1)
  let embedded :=
    ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin controllers
        initialBank (entryTag, canonical.1.1), canonical.1.2),
      (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin controllers
        initialBank (entryTag, canonical.2.1), canonical.2.2))
  let tailEnv := OmegaWord.drop env (n + 1)
  have hstate :
      (mega.globalMachine.reroot initialState).globalStateTrace env (n + 1) =
        embedded := by
    simpa [mega, linked, initialState, canonical, embedded] using
      (profiledRawJointHybridMegaLinked_leftMixed_initial_exactTrace_close_right
        A strategy hwin controllers initialBank kernelTag entryTag
          entryOutputOne frontTwo frontOutputTwo env n hpos hleft hright)
  let maps :=
    profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy hwin
      controllers initialBank
        (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
          hwin controllers initialBank)
  have hembed :
      (mega.globalMachine.reroot embedded).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo tailEnv =
        (linked.globalMachine.reroot canonical).globalMachineTraceWord
          linked.globalOutputOne linked.globalOutputTwo tailEnv := by
    simpa [mega, linked, embedded, maps] using
      (profiledRawJointHybridMegaLinkedEmbedTail_globalMachineTraceWord A
        strategy hwin controllers initialBank entryTag maps canonical tailEnv)
  calc
    OmegaWord.drop
          ((mega.globalMachine.reroot initialState).globalMachineTraceWord
            mega.globalOutputOne mega.globalOutputTwo env) (n + 1) =
        (((mega.globalMachine.reroot initialState).reroot
            ((mega.globalMachine.reroot initialState).globalStateTrace env
              (n + 1))).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo tailEnv) :=
      ((mega.globalMachine.reroot initialState
        ).reroot_globalMachineTraceWord_drop mega.globalOutputOne
          mega.globalOutputTwo env (n + 1)).symm
    _ = (mega.globalMachine.reroot embedded).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo tailEnv := by
      rw [hstate]
      rfl
    _ = (linked.globalMachine.reroot canonical).globalMachineTraceWord
          linked.globalOutputOne linked.globalOutputTwo tailEnv := hembed
    _ = OmegaWord.drop
          (linked.globalMachine.globalMachineTraceWord linked.globalOutputOne
            linked.globalOutputTwo env) (n + 1) :=
      linked.globalMachine.reroot_globalMachineTraceWord_drop
        linked.globalOutputOne linked.globalOutputTwo env (n + 1)
    _ = OmegaWord.drop
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin entryTag env) (n + 1) := by
      rfl

/- Exact mirror simulation of a nonempty strict-right mixed mega prefix. -/
theorem profiledRawJointHybridMegaLinked_rightMixed_initial_exactTrace_succ
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (frontOne : MegaOldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁)
    (entryOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hright : ∀ k < n + 1, (env k).graph = .right) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let linked := LinkedPhysicalController A strategy hwin entryTag
    let initialState :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank frontOne, frontOutputOne),
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (entryTag, linked.initialTwo.1),
          entryOutputTwo))
    ∃ (nextFrontOne : MegaOldOne A strategy hwin controllers initialBank)
        (nextOutputOne : Out₁),
      ((mega.globalMachine.reroot initialState).globalStateTrace env (n + 1)) =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank nextFrontOne, nextOutputOne),
          (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
            controllers initialBank
              (entryTag,
                (profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy
                  hwin entryTag env (n + 1)).1),
            (profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin
              entryTag env (n + 1)).2)) ∧
      FiniteAcknowledgedDelayedCarrier.CarrierAll
        FiniteAcknowledgedDelayedCarrier.DeferredControlIsPending
          (profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin
            entryTag env (n + 1)).1 := by
  dsimp only
  let mega := MegaPhysicalController A strategy hwin controllers initialBank
    kernelTag
  let linked := LinkedPhysicalController A strategy hwin entryTag
  induction n with
  | zero =>
      have hgraph := hright 0 (by omega)
      rcases hround : env 0 with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      let entryTwo : linked.TwoControl :=
        (linked.initialTwo.1, entryOutputTwo)
      obtain ⟨nextTwo, nextFrontOne, nextOutputOne, hstep, hnext,
          hpending⟩ :=
        profiledRawJointHybridMegaLinked_rightMixed_strictRight_exists A strategy
          hwin controllers initialBank kernelTag entryTag entryTwo
          (profiledRawJointHybridFullRestart_initial_allPending A strategy hwin
            entryTag).2 frontOne frontOutputOne inputOne inputTwo
      have hout :=
        profiledRawJointHybridFullRestart_advanceControls_output_irrel A
          strategy hwin entryTag linked.initialOne.1 linked.initialTwo.1
          linked.initialOne.2 linked.initialOne.2 linked.initialTwo.2
          entryOutputTwo ⟨inputOne, inputTwo, .right⟩
      have hnextCanonical : nextTwo =
          profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin
            entryTag env 1 := by
        rw [hnext]
        change
          (linked.advanceControls (linked.initialOne, entryTwo)
              ⟨inputOne, inputTwo, .right⟩).2 = _
        simpa [profiledRawJointHybridFullRestartRightMixedTwoTrace, hround] using
          congrArg Prod.snd hout.symm
      rw [hnextCanonical] at hstep hpending
      refine ⟨nextFrontOne, nextOutputOne, ?_, hpending⟩
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
        FiniteGlobalRoundMachine.globalStateTrace_zero, hround]
      change mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank frontOne, frontOutputOne),
          (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
            controllers initialBank (entryTag, linked.initialTwo.1),
            entryOutputTwo))
          ⟨inputOne, inputTwo, .right⟩ = _
      exact hstep
  | succ n ih =>
      have hprefix : ∀ k < n + 1, (env k).graph = .right := by
        intro k hk
        exact hright k (by omega)
      obtain ⟨frontAt, outputAt, hstate, hpending⟩ := ih hprefix
      have hgraph := hright (n + 1) (by omega)
      rcases hround : env (n + 1) with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      let two :=
        profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin
          entryTag env (n + 1)
      obtain ⟨nextTwo, nextFrontOne, nextOutputOne, hstep, hnext,
          hpendingNext⟩ :=
        profiledRawJointHybridMegaLinked_rightMixed_strictRight_exists A strategy
          hwin controllers initialBank kernelTag entryTag two hpending frontAt
            outputAt inputOne inputTwo
      have hnextTrace : nextTwo =
          profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin
            entryTag env (n + 2) := by
        rw [hnext]
        simp [profiledRawJointHybridFullRestartRightMixedTwoTrace, two, hround]
      rw [hnextTrace] at hstep hpendingNext
      refine ⟨nextFrontOne, nextOutputOne, ?_, hpendingNext⟩
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hstate, hround]
      change mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank frontAt, outputAt),
          (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
            controllers initialBank (entryTag, two.1), two.2))
          ⟨inputOne, inputTwo, .right⟩ = _
      exact hstep

/- The first strict-left round after a nonempty strict-right mixed block reaches
the exact canonical FullRestart state. -/
theorem profiledRawJointHybridMegaLinked_rightMixed_initial_exactTrace_close_left
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (frontOne : MegaOldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁)
    (entryOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hright : ∀ k < n, (env k).graph = .right)
    (hleft : (env n).graph = .left) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let linked := LinkedPhysicalController A strategy hwin entryTag
    let initialState :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank frontOne, frontOutputOne),
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (entryTag, linked.initialTwo.1),
          entryOutputTwo))
    let canonical := linked.globalMachine.globalStateTrace env (n + 1)
    ((mega.globalMachine.reroot initialState).globalStateTrace env (n + 1)) =
      ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (entryTag, canonical.1.1), canonical.1.2),
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (entryTag, canonical.2.1), canonical.2.2)) := by
  dsimp only
  cases n with
  | zero => omega
  | succ n =>
      obtain ⟨frontAt, outputAt, hstate, _⟩ :=
        profiledRawJointHybridMegaLinked_rightMixed_initial_exactTrace_succ A
          strategy hwin controllers initialBank kernelTag entryTag frontOne
            frontOutputOne entryOutputTwo env n hright
      have hgraph := hleft
      rcases hround : env (n + 1) with ⟨inputOne, inputTwo, graph⟩
      simp only [hround] at hgraph
      subst graph
      let two :=
        profiledRawJointHybridFullRestartRightMixedTwoTrace A strategy hwin
          entryTag env (n + 1)
      let maps :=
        profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy
          hwin controllers initialBank
            (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A
              strategy hwin controllers initialBank)
      have hclose :=
        profiledRawJointHybridMegaLinkedCloseRightMixed_strictLeft A strategy
          hwin controllers initialBank entryTag maps two frontAt outputAt
            inputOne inputTwo
      have hcanonical :=
        profiledRawJointHybridFullRestart_rightMixedTrace_close_left A strategy
          hwin entryTag env (n + 1) (by omega) hright hleft
      rw [hround] at hcanonical
      rw [hcanonical] at hclose
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hstate, hround]
      simpa [MegaPhysicalController, maps, two] using hclose

/- The concrete right-created suffix is therefore the canonical dropped
FullRestart word after its first closing round. -/
theorem profiledRawJointHybridMegaLinked_rightMixed_initial_drop_eq_fullRestart_drop
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag entryTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (frontOne : MegaOldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁)
    (entryOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hpos : 0 < n)
    (hright : ∀ k < n, (env k).graph = .right)
    (hleft : (env n).graph = .left) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    let linked := LinkedPhysicalController A strategy hwin entryTag
    let initialState :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank frontOne, frontOutputOne),
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (entryTag, linked.initialTwo.1),
          entryOutputTwo))
    let actualWord :=
      (mega.globalMachine.reroot initialState).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env
    OmegaWord.drop actualWord (n + 1) =
      OmegaWord.drop
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin entryTag env) (n + 1) := by
  dsimp only
  let mega := MegaPhysicalController A strategy hwin controllers initialBank
    kernelTag
  let linked := LinkedPhysicalController A strategy hwin entryTag
  let initialState :=
    ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
        initialBank frontOne, frontOutputOne),
      (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin controllers
        initialBank (entryTag, linked.initialTwo.1), entryOutputTwo))
  let canonical := linked.globalMachine.globalStateTrace env (n + 1)
  let embedded :=
    ((profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin controllers
        initialBank (entryTag, canonical.1.1), canonical.1.2),
      (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin controllers
        initialBank (entryTag, canonical.2.1), canonical.2.2))
  let tailEnv := OmegaWord.drop env (n + 1)
  have hstate :
      (mega.globalMachine.reroot initialState).globalStateTrace env (n + 1) =
        embedded := by
    simpa [mega, linked, initialState, canonical, embedded] using
      (profiledRawJointHybridMegaLinked_rightMixed_initial_exactTrace_close_left
        A strategy hwin controllers initialBank kernelTag entryTag frontOne
          frontOutputOne entryOutputTwo env n hpos hright hleft)
  let maps :=
    profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy hwin
      controllers initialBank
        (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
          hwin controllers initialBank)
  have hembed :
      (mega.globalMachine.reroot embedded).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo tailEnv =
        (linked.globalMachine.reroot canonical).globalMachineTraceWord
          linked.globalOutputOne linked.globalOutputTwo tailEnv := by
    simpa [mega, linked, embedded, maps] using
      (profiledRawJointHybridMegaLinkedEmbedTail_globalMachineTraceWord A
        strategy hwin controllers initialBank entryTag maps canonical tailEnv)
  calc
    OmegaWord.drop
          ((mega.globalMachine.reroot initialState).globalMachineTraceWord
            mega.globalOutputOne mega.globalOutputTwo env) (n + 1) =
        (((mega.globalMachine.reroot initialState).reroot
            ((mega.globalMachine.reroot initialState).globalStateTrace env
              (n + 1))).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo tailEnv) :=
      ((mega.globalMachine.reroot initialState
        ).reroot_globalMachineTraceWord_drop mega.globalOutputOne
          mega.globalOutputTwo env (n + 1)).symm
    _ = (mega.globalMachine.reroot embedded).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo tailEnv := by
      rw [hstate]
      rfl
    _ = (linked.globalMachine.reroot canonical).globalMachineTraceWord
          linked.globalOutputOne linked.globalOutputTwo tailEnv := hembed
    _ = OmegaWord.drop
          (linked.globalMachine.globalMachineTraceWord linked.globalOutputOne
            linked.globalOutputTwo env) (n + 1) :=
      linked.globalMachine.reroot_globalMachineTraceWord_drop
        linked.globalOutputOne linked.globalOutputTwo env (n + 1)
    _ = OmegaWord.drop
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin entryTag env) (n + 1) := by
      rfl

/-- A strict-right creation tag, viewed from its first persistent strict-left
cut, starts an accepted repaired suffix at the exact executable sender source.
-/
theorem
    profiledRawJointHybridMegaLinkedRightTag_fullRestartWord_acceptsFrom_firstPersistentLeft
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .left) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    let retained := tag.markedRetainedChildTag A strategy hwin
    let source :=
      pairedCodeStateForRow A .first
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
              A strategy hwin retained env 0).2.1 false).1.1
    A.AcceptsFrom source
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin retained env) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  let source :=
    pairedCodeStateForRow A .first
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
            A strategy hwin retained env 0).2.1 false).1.1
  have hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin retained env := by
    simpa [retained, tag, OmegaWord.drop] using
      (profiledRawJointHybridMegaLinkedRightTag_firstStrictRootReady_drop A
        strategy hwin origin input env 0 hgraph)
  have hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin retained env cuts source 0 := by
    simp [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
      cuts.cuts_zero, hgraph, source, DetParityAutomaton.runFrom]
  have hfirstChild : retained.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin origin)
          (.strict (tag.strictActual (A := A))) := by
    simp [retained, tag,
      profiledRawJointHybridShadowPhaseLiveRightTag,
      ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild,
      ProfiledRawJointHybridShadowPhaseLiveTag.direction_eq_strict]
  have hfirstGraph : (env 0).graph =
      profiledRawJointStrictGraphOfSide
        (tag.strictActual (A := A)).side.other := by
    simpa [tag, ProfiledRawJointHybridShadowPhaseLiveTag.strictActual,
      profiledRawJointStrictGraphOfSide] using hgraph
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_acceptsFrom_of_exactFirstChild
      A strategy hwin retained env cuts hnoBoth hfirst source hinitial origin
        (tag.strictActual (A := A)) hfirstChild hfirstGraph

/-- Strict-left creation / first persistent strict-right mirror. -/
theorem
    profiledRawJointHybridMegaLinkedLeftTag_fullRestartWord_acceptsFrom_firstPersistentRight
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .right) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    let retained := tag.markedRetainedChildTag A strategy hwin
    let source :=
      pairedCodeStateForRow A .first
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
              A strategy hwin retained env 0).1.1 false).1.1
    A.AcceptsFrom source
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin retained env) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  let source :=
    pairedCodeStateForRow A .first
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
            A strategy hwin retained env 0).1.1 false).1.1
  have hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin retained env := by
    simpa [retained, tag, OmegaWord.drop] using
      (profiledRawJointHybridMegaLinkedLeftTag_firstStrictRootReady_drop A
        strategy hwin origin input env 0 hgraph)
  have hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin retained env cuts source 0 := by
    simp [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
      cuts.cuts_zero, hgraph, source, DetParityAutomaton.runFrom]
  have hfirstChild : retained.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin origin)
          (.strict (tag.strictActual (A := A))) := by
    simp [retained, tag,
      profiledRawJointHybridShadowPhaseLiveLeftTag,
      ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild,
      ProfiledRawJointHybridShadowPhaseLiveTag.direction_eq_strict]
  have hfirstGraph : (env 0).graph =
      profiledRawJointStrictGraphOfSide
        (tag.strictActual (A := A)).side.other := by
    simpa [tag, ProfiledRawJointHybridShadowPhaseLiveTag.strictActual,
      profiledRawJointStrictGraphOfSide] using hgraph
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_acceptsFrom_of_exactFirstChild
      A strategy hwin retained env cuts hnoBoth hfirst source hinitial origin
        (tag.strictActual (A := A)) hfirstChild hfirstGraph

/-! ## Canonical physical entry words

A simultaneous front handoff stores the output emitted by that handoff next
to the canonical tail controls.  Those stored Moore outputs are stale at the
start of the suffix: every physical record reads the outputs produced by the
next transition.  Hence the rerooted entry state has exactly the canonical
`FullRestart` word. -/

/-- The strict-right simultaneous entry state generates the canonical
`FullRestart` word for the exact delivered tag. -/
theorem
    profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair_word_eq_commonRootReference
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (env : EnvironmentSequence In₁ In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag
    let entryState :=
      profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair A strategy
        hwin controllers initialBank shadow owner inputOne inputTwo
    (linked.globalMachine.reroot entryState).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo env =
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag env := by
  dsimp only
  exact
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair_word_eq_reference
      A strategy hwin _ _ _ env

/-- Strict-left simultaneous-entry mirror. -/
theorem
    profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair_word_eq_commonRootReference
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂)
    (env : EnvironmentSequence In₁ In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let linked :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
        A strategy hwin entryTag
    let entryState :=
      profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair A strategy hwin
        controllers initialBank shadow owner inputOne inputTwo
    (linked.globalMachine.reroot entryState).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo env =
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag env := by
  dsimp only
  exact
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair_word_eq_reference
      A strategy hwin _ _ _ env

/-! ## Simultaneous-entry finite-prefix splice -/

/-- Once the actual mega trace reaches a genuine strict-right front pair and
the next round is simultaneous, its dropped word is the canonical repaired
word.  No separate suffix equality remains to be proved. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both_drop_eq_commonRootReference
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hstate :
      ((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
          ).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputTwo)))
    (hgraph : (env start).graph = .both) :
    let inputOne := (env start).inputOne
    let inputTwo := (env start).inputTwo
    let entryTag :=
      profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
    OmegaWord.drop
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + 1) =
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag (OmegaWord.drop env (start + 1)) := by
  dsimp only
  rw [
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both_finitePrefix_traceSplice
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo env start hstate hgraph]
  exact
    profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair_word_eq_commonRootReference
      A strategy hwin controllers initialBank shadow owner
        (env start).inputOne (env start).inputTwo
          (OmegaWord.drop env (start + 1))

/-- Strict-left simultaneous-entry mirror. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both_drop_eq_commonRootReference
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hstate :
      ((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
          ).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputTwo)))
    (hgraph : (env start).graph = .both) :
    let inputOne := (env start).inputOne
    let inputTwo := (env start).inputTwo
    let entryTag :=
      profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
    OmegaWord.drop
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + 1) =
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag (OmegaWord.drop env (start + 1)) := by
  dsimp only
  rw [
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both_finitePrefix_traceSplice
      A strategy hwin controllers initialBank kernelTag shadow owner
        oldOutputOne oldOutputTwo env start hstate hgraph]
  exact
    profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair_word_eq_commonRootReference
      A strategy hwin controllers initialBank shadow owner
        (env start).inputOne (env start).inputTwo
          (OmegaWord.drop env (start + 1))

/-! ## Finite-prefix transport

These two statements are the final automata-level splice.  They deliberately
leave only finite operational equalities to the mega-front proof: equality of
the dropped physical word with `FullRestart`, and equality of the reached DPA
state with the first executable sender source. -/

/-- Any finite physical prefix ending at the concrete strict-right-tag /
strict-left-tail splice inherits acceptance from the repaired suffix. -/
theorem
    profiledRawJointHybridMegaLinked_accepts_of_rightTag_fullRestartSuffix
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (tailEnv : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (tailEnv n).graph))
    (hnoBoth : ∀ n : Nat, (tailEnv n).graph ≠ .both)
    (hgraph : (tailEnv 0).graph = .left)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hdrop :
      OmegaWord.drop word start =
        let tag :=
          profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin
            input
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin (tag.markedRetainedChildTag A strategy hwin)
            tailEnv)
    (hstate :
      A.run word start =
        let tag :=
          profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin
            input
        let retained := tag.markedRetainedChildTag A strategy hwin
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                A strategy hwin retained tailEnv 0).2.1 false).1.1) :
    A.Accepts word := by
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  let source :=
    pairedCodeStateForRow A .first
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
            A strategy hwin retained tailEnv 0).2.1 false).1.1
  have hsuffix : A.AcceptsFrom source
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin retained tailEnv) := by
    simpa [tag, retained, source] using
      (profiledRawJointHybridMegaLinkedRightTag_fullRestartWord_acceptsFrom_firstPersistentLeft
        A strategy hwin origin input tailEnv cuts hnoBoth hgraph)
  have htail :
      A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) := by
    rw [hstate, hdrop]
    exact hsuffix
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp htail

/-- Strict-left-tag / strict-right-tail finite-prefix mirror. -/
theorem
    profiledRawJointHybridMegaLinked_accepts_of_leftTag_fullRestartSuffix
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (tailEnv : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (tailEnv n).graph))
    (hnoBoth : ∀ n : Nat, (tailEnv n).graph ≠ .both)
    (hgraph : (tailEnv 0).graph = .right)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hdrop :
      OmegaWord.drop word start =
        let tag :=
          profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin
            input
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin (tag.markedRetainedChildTag A strategy hwin)
            tailEnv)
    (hstate :
      A.run word start =
        let tag :=
          profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin
            input
        let retained := tag.markedRetainedChildTag A strategy hwin
        pairedCodeStateForRow A .first
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                A strategy hwin retained tailEnv 0).1.1 false).1.1) :
    A.Accepts word := by
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let retained := tag.markedRetainedChildTag A strategy hwin
  let source :=
    pairedCodeStateForRow A .first
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
            A strategy hwin retained tailEnv 0).1.1 false).1.1
  have hsuffix : A.AcceptsFrom source
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin retained tailEnv) := by
    simpa [tag, retained, source] using
      (profiledRawJointHybridMegaLinkedLeftTag_fullRestartWord_acceptsFrom_firstPersistentRight
        A strategy hwin origin input tailEnv cuts hnoBoth hgraph)
  have htail :
      A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) := by
    rw [hstate, hdrop]
    exact hsuffix
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp htail

/-! ## Legacy `.first` simultaneous-entry interfaces

The word splice below is valid, but the old phase tag is not the row-exact
target selected at a later simultaneous close.  Consequently the `.first`
premises of the following two implications are deliberately retained only as
compatibility interfaces; they are not obligations of the concrete mega
front.  Nor may they be repaired merely by changing `.first` to the old tag's
`.both` coordinate: that coordinate is the counterfactual simultaneous
successor of an earlier occurrence.  The positive proof must retain a new
finite target computed at the actual close. -/

/-- Legacy conditional implication from a `.first` state equation.  Do not
use this theorem as evidence that the concrete simultaneous handoff satisfies
that equation. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both_accepts_of_dpaState
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      ((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
          ).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputTwo)))
    (hboth : (env start).graph = .both)
    (cuts : OperationalCloseCutPackage
      (fun n ↦ ((OmegaWord.drop env (start + 1)) n).graph))
    (hnoBoth : ∀ n : Nat,
      ((OmegaWord.drop env (start + 1)) n).graph ≠ .both)
    (hfirstGraph : ((OmegaWord.drop env (start + 1)) 0).graph = .left)
    (hdpa :
      let inputOne := (env start).inputOne
      let inputTwo := (env start).inputTwo
      let entryTag :=
        profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
          shadow owner inputOne inputTwo
      let mega :=
        (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag).physicalController
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) (start + 1) =
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                A strategy hwin entryTag (OmegaWord.drop env (start + 1))
                  0).2.1 false).1.1) :
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hdpa ⊢
  let mega :=
    (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
      hwin controllers initialBank kernelTag).physicalController
  let word := mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
    mega.globalOutputTwo env
  let tailEnv := OmegaWord.drop env (start + 1)
  let phaseTag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin shadow.origin
      shadow.input
  let entryTag := phaseTag.markedRetainedChildTag A strategy hwin
  have hdrop : OmegaWord.drop word (start + 1) =
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag tailEnv := by
    simpa [mega, word, tailEnv, phaseTag, entryTag,
      profiledRawJointHybridMegaLinkedRightEntryRetainedTag] using
      (profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both_drop_eq_commonRootReference
        A strategy hwin controllers initialBank kernelTag shadow owner
          oldOutputOne oldOutputTwo env start hfront hboth)
  have hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin entryTag.1 := by
    simpa [phaseTag, entryTag] using
      (profiledRawJointHybridMegaLinkedRightTag_markedChild_leftRootReady A
        strategy hwin shadow.origin shadow.input)
  have hfirstSide :
      (phaseTag.strictActual (A := A)).side = .right := by
    rfl
  have htagChild : entryTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
            hwin shadow.origin)
          (.strict (phaseTag.strictActual (A := A))) := by
    simp [phaseTag, entryTag,
      profiledRawJointHybridShadowPhaseLiveRightTag,
      ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild,
      ProfiledRawJointHybridShadowPhaseLiveTag.direction_eq_strict]
  have hstate :
      A.runFrom (A.run word (start + 1))
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin entryTag tailEnv) 0 =
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy
                hwin entryTag tailEnv 0).2.1 false).1.1 := by
    simpa [DetParityAutomaton.runFrom, word, mega, tailEnv, phaseTag, entryTag,
      profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt]
      using hdpa
  have hsuffix : A.AcceptsFrom (A.run word (start + 1))
      (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag tailEnv) :=
    profiledRawJointHybridMegaLinkedCommonRootReferenceWord_acceptsFrom_of_leftFirstExactChild
      A strategy hwin entryTag tailEnv cuts hnoBoth hfirstGraph hready
        (A.run word (start + 1)) hstate shadow.origin
          (phaseTag.strictActual (A := A)) hfirstSide htagChild
  have htail : A.AcceptsFrom (A.run word (start + 1))
      (OmegaWord.drop word (start + 1)) := by
    rw [hdrop]
    exact hsuffix
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word (start + 1)).mp htail

/-- Strict-left mirror of the legacy conditional `.first` interface. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both_accepts_of_dpaState
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (kernelTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hfront :
      ((profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
          ).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputTwo)))
    (hboth : (env start).graph = .both)
    (cuts : OperationalCloseCutPackage
      (fun n ↦ ((OmegaWord.drop env (start + 1)) n).graph))
    (hnoBoth : ∀ n : Nat,
      ((OmegaWord.drop env (start + 1)) n).graph ≠ .both)
    (hfirstGraph : ((OmegaWord.drop env (start + 1)) 0).graph = .right)
    (hdpa :
      let inputOne := (env start).inputOne
      let inputTwo := (env start).inputTwo
      let entryTag :=
        profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
          shadow owner inputOne inputTwo
      let mega :=
        (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
          strategy hwin controllers initialBank kernelTag).physicalController
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) (start + 1) =
        pairedCodeStateForRow A .first
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                A strategy hwin entryTag (OmegaWord.drop env (start + 1))
                  0).1.1 false).1.1) :
    let mega :=
      (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A
        strategy hwin controllers initialBank kernelTag).physicalController
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hdpa ⊢
  let mega :=
    (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
      hwin controllers initialBank kernelTag).physicalController
  let word := mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
    mega.globalOutputTwo env
  let tailEnv := OmegaWord.drop env (start + 1)
  let phaseTag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin shadow.origin
      shadow.input
  let entryTag := phaseTag.markedRetainedChildTag A strategy hwin
  have hdrop : OmegaWord.drop word (start + 1) =
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag tailEnv := by
    simpa [mega, word, tailEnv, phaseTag, entryTag,
      profiledRawJointHybridMegaLinkedLeftEntryRetainedTag] using
      (profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both_drop_eq_commonRootReference
        A strategy hwin controllers initialBank kernelTag shadow owner
          oldOutputOne oldOutputTwo env start hfront hboth)
  have hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin entryTag.1 := by
    simpa [phaseTag, entryTag] using
      (profiledRawJointHybridMegaLinkedLeftTag_markedChild_rightRootReady A
        strategy hwin shadow.origin shadow.input)
  have hfirstSide :
      (phaseTag.strictActual (A := A)).side = .left := by
    rfl
  have htagChild : entryTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
            hwin shadow.origin)
          (.strict (phaseTag.strictActual (A := A))) := by
    simp [phaseTag, entryTag,
      profiledRawJointHybridShadowPhaseLiveLeftTag,
      ProfiledRawJointHybridShadowPhaseLiveTag.markedBankChild,
      ProfiledRawJointHybridShadowPhaseLiveTag.direction_eq_strict]
  have hstate :
      A.runFrom (A.run word (start + 1))
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin entryTag tailEnv) 0 =
        pairedCodeStateForRow A .first
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridMegaLinkedCommonRootRightBaseAt A strategy
                hwin entryTag tailEnv 0).1.1 false).1.1 := by
    simpa [DetParityAutomaton.runFrom, word, mega, tailEnv, phaseTag, entryTag,
      profiledRawJointHybridMegaLinkedCommonRootRightBaseAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt]
      using hdpa
  have hsuffix : A.AcceptsFrom (A.run word (start + 1))
      (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        entryTag tailEnv) :=
    CommonRootRightMirror.profiledRawJointHybridMegaLinkedCommonRootReferenceWord_acceptsFrom_of_rightFirstExactChild
      A strategy hwin entryTag tailEnv cuts hnoBoth hfirstGraph hready
        (A.run word (start + 1)) hstate shadow.origin
          (phaseTag.strictActual (A := A)) hfirstSide htagChild
  have htail : A.AcceptsFrom (A.run word (start + 1))
      (OmegaWord.drop word (start + 1)) := by
    rw [hdrop]
    exact hsuffix
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word (start + 1)).mp htail

end

end DetParityAutomaton

end DistributedSynthesis
