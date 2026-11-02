/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRestartedBranchCheckerAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveTableSegment

/-!
# Checker synchronization at the first activated strict seam

The common package stores the old DPA coordinate in row `.both`.  Its first
strict-left receive reads the corresponding table target, emits the selected
physical record, and stores the chosen one-sided child in fresh row `.first`.
This file joins those three already verified facts into the state equation
needed by the later physical-prefix handoff.
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

/-- The false member's first selected physical record is the canonical first
left-block letter of the exact activation.  This is the physical-coordinate
form of the table's literal first-record pinning law. -/
theorem literalRightSeamExactFalseInitialSelectedPhysical_eq_blockLetter
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (input : In₁ × In₂) :
    let installed := package.literalRightSeamInstalled A strategy hwin key
    let activation := profiledRawJointHybridExactLeftActivation A hwin
      installed
    let receiver :=
      profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
        installed false
    let receiverStep :=
      profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
        installed receiver input.1 input.2
    let sender :=
      profiledRawJointLiteralRightBothExactSenderInitial A strategy hwin
        installed
    let senderStep :=
      profiledRawJointLiteralRightBothExactSenderNoRecv A strategy hwin
        installed sender input.2
    literalRightSeamSelectedProductPhysicalLetter A strategy hwin installed
        false (input, receiverStep.1, senderStep.1) =
      pairedLeftBlockLetterAt activation.lambda [] input := by
  classical
  dsimp only
  let installed := package.literalRightSeamInstalled A strategy hwin key
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  have hfirst := (table.memberController_records_allowed false input input).1
  change decide (_ = _) = true at hfirst
  have hrecord := of_decide_eq_true hfirst
  have hphysical := congrArg
    (profiledRawJointTargetLeftPhysicalLetter A) hrecord
  simpa [literalRightSeamSelectedProductPhysicalLetter,
    profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointTargetLeftReceiverStrategy, pairedLeftReceiverStrategy,
    pairedLeftSenderStrategy, pairedLeftBlockLetterAt,
    profiledRawJointHybridExactLeftUniformActivation] using hphysical

/-- Mirror first-record pinning: the false member's selected physical record
is the canonical first right-block letter of the exact activation. -/
theorem literalLeftSeamExactFalseInitialSelectedPhysical_eq_blockLetter
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (input : In₂ × In₁) :
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    let activation := profiledRawJointHybridExactRightActivation A hwin
      installed
    let receiver :=
      profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
        installed false
    let receiverStep :=
      profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
        installed receiver input.1 input.2
    let sender :=
      profiledRawJointLiteralLeftBothExactSenderInitial A strategy hwin
        installed
    let senderStep :=
      profiledRawJointLiteralLeftBothExactSenderNoRecv A strategy hwin
        installed sender input.2
    literalLeftSeamSelectedProductPhysicalLetter A strategy hwin installed
        false (input, receiverStep.1, senderStep.1) =
      pairedRightBlockLetterAt activation.lambda [] input := by
  classical
  dsimp only
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      installed
  have hfirst := (table.memberController_records_allowed false input input).1
  change decide (_ = _) = true at hfirst
  have hrecord := of_decide_eq_true hfirst
  have hphysical := congrArg
    (profiledRawJointTargetRightPhysicalLetter A) hrecord
  simpa [literalLeftSeamSelectedProductPhysicalLetter,
    profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointTargetRightReceiverStrategy, pairedRightReceiverStrategy,
    pairedRightSenderStrategy, pairedRightBlockLetterAt,
    profiledRawJointHybridExactRightUniformActivation] using hphysical

/-- The first strict-left record emitted from a common package moves the
actual checker from its retained `.both` coordinate to the exact fresh
right-seam stage stored by that receive. -/
theorem literalCombinedFresh_initial_strictLeft_step_eq_exactStage
    (package : Package A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    let one := package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
    let two := package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
    let key := package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
    let installed := package.literalRightSeamInstalled A strategy hwin key
    let source := installed.world.procTwoSlot A
    let stage := package.literalRightSeamExactStageAt A strategy hwin key
      .both .first [] input
    A.step (pairedCodeStateForRow A .both source.1.1)
        (leftRoundRecord input
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
            input.1 two input.2).2
          (package.literalCombinedFreshTwoPendingStep A strategy hwin two.1
            two.2.1 input.2).2) =
      pairedCodeStateForRow A .first stage.root.slot.1.1 := by
  dsimp only
  rw [package.literalCombinedFreshPhaseLive_strictLeft_pendingRecord_eq_selected
    A strategy hwin
    (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) input]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A strategy
    hwin (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
      (by rfl)]
  simp only [literalCombinedFreshPendingOnlyInitialOne,
    literalCombinedFreshPendingOnlyInitialTwo,
    literalCombinedFreshPendingOnlyInitialOneShared,
    literalCombinedFreshPendingOnlyInitialTwoShared,
    literalCombinedFreshOneReceiver,
    FiniteDelayedFork.candidate,
    literalRightSeamStagedReceiverInitial,
    literalRightSeamBranchStagedReceiverRecv,
    literalRightSeamStagedSenderNoRecv,
    literalRightSeamStagedSenderInitial,
    literalRightSeamFrontSenderNoRecv,
    literalRightSeamFrontSenderInitial]
  change A.step
      (pairedCodeStateForRow A .both
        ((package.literalRightSeamInstalled A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          ).world.procTwoSlot A).1.1)
      (pairedLeftRecordForRow .both
        (literalRightSeamSelectedProductPhysicalLetter A strategy hwin
          (package.literalRightSeamInstalled A strategy hwin
            (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin))
          false
          (input,
            (profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
              (package.literalRightSeamInstalled A strategy hwin
                (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                  hwin))
              (profiledRawJointLiteralRightBothExactReceiverInitial A strategy
                hwin
                (package.literalRightSeamInstalled A strategy hwin
                  (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                    hwin)) false)
              input.1 input.2).1,
            (profiledRawJointLiteralRightBothExactSenderNoRecv A strategy hwin
              (package.literalRightSeamInstalled A strategy hwin
                (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                  hwin))
              (profiledRawJointLiteralRightBothExactSenderInitial A strategy
                hwin
                (package.literalRightSeamInstalled A strategy hwin
                  (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                    hwin))) input.2).1))) =
    pairedCodeStateForRow A .first
      (package.literalRightSeamExactStageAt A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
        .both .first [] input).root.slot.1.1
  rw [package.literalRightSeamExactFalseInitialSelectedPhysical_eq_blockLetter
    A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
      input]
  rw [← package.literalRightSeamExactStageAt_first_eq_step_both A strategy
    hwin (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
      input]

/-- The first strict-right record is the exact mirror: it advances the
retained `.both` checker coordinate to the fresh `.first` left-seam stage. -/
theorem literalCombinedFresh_initial_strictRight_step_eq_exactStage
    (package : Package A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    let one := package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
    let two := package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
    let key := package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    let source := installed.world.procOneSlot A
    let stage := package.literalLeftSeamExactStageAt A strategy hwin key
      .both .first [] (input.2, input.1)
    A.step (pairedCodeStateForRow A .both source.1.1)
        (rightRoundRecord (input.2, input.1)
          (package.literalCombinedFreshOnePendingStep A strategy hwin one.1
            one.2.1 input.1).2
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            input.2 one input.1).2) =
      pairedCodeStateForRow A .first stage.root.slot.1.1 := by
  dsimp only
  rw [package.literalCombinedFreshPhaseLive_strictRight_pendingRecord_eq_selected
    A strategy hwin
    (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) input]
  rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_same A strategy
    hwin (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (by rfl)]
  simp only [literalCombinedFreshPendingOnlyInitialOne,
    literalCombinedFreshPendingOnlyInitialTwo,
    literalCombinedFreshPendingOnlyInitialOneShared,
    literalCombinedFreshPendingOnlyInitialTwoShared,
    literalCombinedFreshTwoReceiver,
    FiniteDelayedFork.candidate,
    literalLeftSeamStagedReceiverInitial,
    literalLeftSeamBranchStagedReceiverRecv,
    literalLeftSeamStagedSenderNoRecv,
    literalLeftSeamStagedSenderInitial,
    literalLeftSeamFrontSenderNoRecv,
    literalLeftSeamFrontSenderInitial]
  change A.step
      (pairedCodeStateForRow A .both
        ((package.literalLeftSeamInstalled A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          ).world.procOneSlot A).1.1)
      (pairedRightRecordForRow .both
        (literalLeftSeamSelectedProductPhysicalLetter A strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin
            (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin))
          false
          ((input.2, input.1),
            (profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin
                (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                  hwin))
              (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy
                hwin
                (package.literalLeftSeamInstalled A strategy hwin
                  (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                    hwin)) false)
              input.2 input.1).1,
            (profiledRawJointLiteralLeftBothExactSenderNoRecv A strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin
                (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                  hwin))
              (profiledRawJointLiteralLeftBothExactSenderInitial A strategy
                hwin
                (package.literalLeftSeamInstalled A strategy hwin
                  (package.literalCombinedFreshPendingOnlyInitialKey A strategy
                    hwin))) input.1).1))) =
    pairedCodeStateForRow A .first
      (package.literalLeftSeamExactStageAt A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
        .both .first [] (input.2, input.1)).root.slot.1.1
  rw [package.literalLeftSeamExactFalseInitialSelectedPhysical_eq_blockLetter
    A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
      (input.2, input.1)]
  rw [← package.literalLeftSeamExactStageAt_first_eq_step_both A strategy
    hwin (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
      (input.2, input.1)]

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
