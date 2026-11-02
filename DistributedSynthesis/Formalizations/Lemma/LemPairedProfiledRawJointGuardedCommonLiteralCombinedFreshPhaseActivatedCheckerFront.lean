/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedCheckerSeed
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedTwoRoundFront

/-!
# Actual-word checker synchronization at the activated front

The checker-seed equations identify the literal pending transition.  This
file connects those equations to the first letter emitted by the executable
Moore controller, so the conclusion is stated directly about `A.runFrom` on
the actual physical word.
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

/-- The actual Moore word's first strict-left letter is exactly the pending
record used by the checker-seed equation. -/
theorem literalCombinedFreshPhaseActivated_traceWord_zero_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hgraph : (env 0).graph = .left) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let word := controller.globalMachine.globalMachineTraceWord
      controller.globalOutputOne controller.globalOutputTwo env
    let one := package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
    let two := package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
    word 0 =
      leftRoundRecord ((env 0).inputOne, (env 0).inputTwo)
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env 0).inputOne two (env 0).inputTwo).2
        (package.literalCombinedFreshTwoPendingStep A strategy hwin two.1
          two.2.1 (env 0).inputTwo).2 := by
  dsimp only
  simp [FiniteGlobalRoundMachine.globalMachineTraceWord,
    FiniteGlobalRoundMachine.globalStateTrace,
    FinitePairedPhysicalController.globalMachine,
    FinitePairedPhysicalController.globalOutputOne,
    FinitePairedPhysicalController.globalOutputTwo,
    FinitePairedPhysicalController.advanceControls, hgraph,
    literalCombinedFreshPhaseActivatedPhysicalController,
    literalCombinedFreshPhaseActivatedController,
    FinitePairedMealyController.mooreize,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController,
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy,
    FiniteAcknowledgedDelayedCarrier.noRecvMealy,
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne,
    literalCombinedFreshPhaseActivatedOpenRecvOne,
    literalCombinedFreshPhaseActivatedNoRecvTwo, leftRoundRecord]

/-- Strict-right mirror of the actual first-letter equation. -/
theorem literalCombinedFreshPhaseActivated_traceWord_zero_strictRight
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hgraph : (env 0).graph = .right) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let word := controller.globalMachine.globalMachineTraceWord
      controller.globalOutputOne controller.globalOutputTwo env
    let one := package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
    let two := package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
    word 0 =
      rightRoundRecord ((env 0).inputTwo, (env 0).inputOne)
        (package.literalCombinedFreshOnePendingStep A strategy hwin one.1
          one.2.1 (env 0).inputOne).2
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env 0).inputTwo one (env 0).inputOne).2 := by
  dsimp only
  simp [FiniteGlobalRoundMachine.globalMachineTraceWord,
    FiniteGlobalRoundMachine.globalStateTrace,
    FinitePairedPhysicalController.globalMachine,
    FinitePairedPhysicalController.globalOutputOne,
    FinitePairedPhysicalController.globalOutputTwo,
    FinitePairedPhysicalController.advanceControls, hgraph,
    literalCombinedFreshPhaseActivatedPhysicalController,
    literalCombinedFreshPhaseActivatedController,
    FinitePairedMealyController.mooreize,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController,
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy,
    FiniteAcknowledgedDelayedCarrier.noRecvMealy,
    FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo,
    literalCombinedFreshPhaseActivatedNoRecvOne,
    literalCombinedFreshPhaseActivatedOpenRecvTwo, rightRoundRecord]

/-! ## Actual one-round checker equations -/

/-- From the retained common `.both` state, one actual strict-left controller
letter reaches the exact restarted stage stored by the receive. -/
theorem literalCombinedFreshPhaseActivated_runFrom_one_strictLeft_eq_exactStage
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hgraph : (env 0).graph = .left) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let word := controller.globalMachine.globalMachineTraceWord
      controller.globalOutputOne controller.globalOutputTwo env
    let key := package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
    let installed := package.literalRightSeamInstalled A strategy hwin key
    let source := installed.world.procTwoSlot A
    let input := ((env 0).inputOne, (env 0).inputTwo)
    let stage := package.literalRightSeamExactStageAt A strategy hwin key
      .both .first [] input
    A.runFrom (pairedCodeStateForRow A .both source.1.1) word 1 =
      pairedCodeStateForRow A .first stage.root.slot.1.1 := by
  dsimp only
  change A.step
      (pairedCodeStateForRow A .both
        ((package.literalRightSeamInstalled A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          ).world.procTwoSlot A).1.1) _ = _
  rw [package.literalCombinedFreshPhaseActivated_traceWord_zero_strictLeft A
    strategy hwin env hgraph]
  exact package.literalCombinedFresh_initial_strictLeft_step_eq_exactStage A
    strategy hwin ((env 0).inputOne, (env 0).inputTwo)

/-- Strict-right mirror of the actual one-round checker equation. -/
theorem
    literalCombinedFreshPhaseActivated_runFrom_one_strictRight_eq_exactStage
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hgraph : (env 0).graph = .right) :
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let word := controller.globalMachine.globalMachineTraceWord
      controller.globalOutputOne controller.globalOutputTwo env
    let key := package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    let source := installed.world.procOneSlot A
    let input := ((env 0).inputOne, (env 0).inputTwo)
    let stage := package.literalLeftSeamExactStageAt A strategy hwin key
      .both .first [] (input.2, input.1)
    A.runFrom (pairedCodeStateForRow A .both source.1.1) word 1 =
      pairedCodeStateForRow A .first stage.root.slot.1.1 := by
  dsimp only
  change A.step
      (pairedCodeStateForRow A .both
        ((package.literalLeftSeamInstalled A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          ).world.procOneSlot A).1.1) _ = _
  rw [package.literalCombinedFreshPhaseActivated_traceWord_zero_strictRight A
    strategy hwin env hgraph]
  exact package.literalCombinedFresh_initial_strictRight_step_eq_exactStage A
    strategy hwin ((env 0).inputOne, (env 0).inputTwo)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

/-! ## Honest two-common-round composition -/

/-- Two literal simultaneous seed rounds followed by the first actual
strict-right activated-controller round reach the exact restarted stage of
the honestly selected seed package. -/
theorem
    literalCombinedFreshPhaseActivated_honestFront_run_three_strictRight_of_source_eq
    (first current : In₁ × In₂)
    (env : EnvironmentSequence In₁ In₂)
    (hgraph : (env 0).graph = .right)
    (hsource :
      let seed := (first, current)
      let package :=
        literalCombinedFreshPhaseActivatedPackageOfSeed A strategy hwin seed
      let key :=
        package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
      pairedCodeStateForRow A .both
          (((literalCombinedFreshPhaseActivatedPointOfSeed A strategy seed
            ).world A strategy).procOneSlot A).1.1 =
        pairedCodeStateForRow A .both
          ((package.literalLeftSeamInstalled A strategy hwin key
            ).world.procOneSlot A).1.1) :
    let seed := (first, current)
    let package :=
      literalCombinedFreshPhaseActivatedPackageOfSeed A strategy hwin seed
    let controller :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let tailWord := controller.globalMachine.globalMachineTraceWord
      controller.globalOutputOne controller.globalOutputTwo env
    let firstRound := nextRound strategy []
      ⟨first.1, first.2, Graph.both⟩
    let secondRound := nextRound strategy [firstRound]
      ⟨current.1, current.2, Graph.both⟩
    let word := OmegaWord.prependList [firstRound, secondRound] tailWord
    let key := package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
    let stage := package.literalLeftSeamExactStageAt A strategy hwin key
      .both .first [] ((env 0).inputTwo, (env 0).inputOne)
    A.run word 3 = pairedCodeStateForRow A .first stage.root.slot.1.1 := by
  dsimp only at hsource ⊢
  let package := literalCombinedFreshPhaseActivatedPackageOfSeed A strategy
    hwin (first, current)
  let controller :=
    package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
      hwin
  let tailWord := controller.globalMachine.globalMachineTraceWord
    controller.globalOutputOne controller.globalOutputTwo env
  let firstRound := nextRound strategy []
    ⟨first.1, first.2, Graph.both⟩
  let secondRound := nextRound strategy [firstRound]
    ⟨current.1, current.2, Graph.both⟩
  let word := OmegaWord.prependList [firstRound, secondRound] tailWord
  have htwo : A.run word 2 =
      pairedCodeStateForRow A .both
        (((literalCombinedFreshPhaseActivatedPointOfSeed A strategy
          (first, current)).world A strategy).procOneSlot A).1.1 := by
    apply literalCombinedFreshPhaseActivatedTwoRound_run_two_eq_installedState
      A strategy first current word
    · rfl
    · rfl
  change A.runFrom A.initial word 2 = _ at htwo
  change A.runFrom A.initial word (2 + 1) = _
  rw [← A.runFrom_drop A.initial word 2 1, htwo]
  have hdrop : OmegaWord.drop word 2 = tailWord := by
    simpa [word] using
      (OmegaWord.drop_length_prependList [firstRound, secondRound] tailWord)
  rw [hdrop]
  rw [hsource]
  simpa [package, literalCombinedFreshPhaseActivatedPackageOfSeed,
    literalCombinedFreshPhaseActivatedPointOfSeed] using
    (package.literalCombinedFreshPhaseActivated_runFrom_one_strictRight_eq_exactStage
      A strategy hwin env hgraph)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
