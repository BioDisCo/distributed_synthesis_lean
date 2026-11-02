/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRestartedBranchStagedFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointAlignedCanonicalPhysicalSchedule

/-!
# Checker alignment for fresh-row restarted literal stages

The restarted seam front selects its child from the old `.both` checker row
and stores `.first` as the new one-sided entry row.  Here the latter state is
proved equal to the actual DPA successor under the strict physical record.
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

/-! ## Strict-left close / right-seam stage -/

/-- The restarted right-seam stage's fresh `.first` root is the actual
strict-left scan successor selected from the old `.both` row. -/
theorem literalRightSeamExactStageAt_first_eq_leftScanStep_both
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let installed := package.literalRightSeamInstalled A strategy hwin key
    let activation := profiledRawJointHybridExactLeftActivation A hwin
      installed
    let source := installed.world.procTwoSlot A
    let stage := package.literalRightSeamExactStageAt A strategy hwin key
      .both .first past input
    pairedCodeStateForRow A .first stage.root.slot.1.1 =
      (pairedLeftScanPairForRow A .both
        (pairedLeftScanStep A
          (pairedLeftScanAfter A source.1.1 activation.lambda past)
          (pairedLeftBlockLetterAt activation.lambda past input))).1 := by
  dsimp only
  let installed := package.literalRightSeamInstalled A strategy hwin key
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  let source := installed.world.procTwoSlot A
  let stage := package.literalRightSeamExactStageAt A strategy hwin key .both
    .first past input
  have hslot : stage.root.slot =
      profiledRawLeftChildSlot A source activation.lambda .both past input := by
    simp [stage, source, activation, installed]
  have hclose :
      erasePairedProfiledState A (.inr (.inl stage.root.slot)) =
        pairedLeftCloseTarget A
          (pairedLeftScanAfter A source.1.1 activation.lambda past) .both
          (pairedLeftBlockLetterAt activation.lambda past input) := by
    rw [hslot]
    rw [← pairedProfiledTwoChild_eq_profiledRawLeftChildSlot A source
      activation.lambda .both past input]
    rw [erase_pairedProfiledTwoChild]
    rw [← pairedLeftCloseTarget_scanAfter]
  exact
    pairedCodeStateForRow_first_eq_leftScanStep_selected_current_of_exactTarget
      A stage.root.slot
        (pairedLeftScanAfter A source.1.1 activation.lambda past) .both
        (pairedLeftBlockLetterAt activation.lambda past input) hclose

/-- At the first post-common strict-left round, the same equation is a direct
one-step equality from the old `.both` entry state. -/
theorem literalRightSeamExactStageAt_first_eq_step_both
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (input : In₁ × In₂) :
    let installed := package.literalRightSeamInstalled A strategy hwin key
    let activation := profiledRawJointHybridExactLeftActivation A hwin
      installed
    let source := installed.world.procTwoSlot A
    let stage := package.literalRightSeamExactStageAt A strategy hwin key
      .both .first [] input
    pairedCodeStateForRow A .first stage.root.slot.1.1 =
      A.step (pairedCodeStateForRow A .both source.1.1)
        (pairedLeftRecordForRow .both
          (pairedLeftBlockLetterAt activation.lambda [] input)) := by
  simpa [pairedLeftScanAfter_nil, pairedLeftScanInitial,
    pairedLeftScanPairForRow, pairedLeftScanStep, pairedCodeStateForRow] using
    package.literalRightSeamExactStageAt_first_eq_leftScanStep_both A strategy
      hwin key [] input

/-! ## Strict-right close / left-seam stage -/

/-- Mirror scan alignment for a strict-right close. -/
theorem literalLeftSeamExactStageAt_first_eq_rightScanStep_both
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    let activation := profiledRawJointHybridExactRightActivation A hwin
      installed
    let source := installed.world.procOneSlot A
    let stage := package.literalLeftSeamExactStageAt A strategy hwin key .both
      .first past input
    pairedCodeStateForRow A .first stage.root.slot.1.1 =
      (pairedRightScanPairForRow A .both
        (pairedRightScanStep A
          (pairedRightScanAfter A source.1.1 activation.lambda past)
          (pairedRightBlockLetterAt activation.lambda past input))).1 := by
  dsimp only
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  let activation := profiledRawJointHybridExactRightActivation A hwin
    installed
  let source := installed.world.procOneSlot A
  let stage := package.literalLeftSeamExactStageAt A strategy hwin key .both
    .first past input
  have hslot : stage.root.slot =
      profiledRawRightChildSlot A source activation.lambda .both past input := by
    simp [stage, source, activation, installed]
  have hclose :
      erasePairedProfiledState A (.inr (.inr stage.root.slot)) =
        pairedRightCloseTarget A
          (pairedRightScanAfter A source.1.1 activation.lambda past) .both
          (pairedRightBlockLetterAt activation.lambda past input) := by
    rw [hslot]
    rw [← pairedProfiledOneChild_eq_profiledRawRightChildSlot A source
      activation.lambda .both past input]
    rw [erase_pairedProfiledOneChild]
    rw [← pairedRightCloseTarget_scanAfter]
  exact
    pairedCodeStateForRow_first_eq_rightScanStep_selected_current_of_exactTarget
      A stage.root.slot
        (pairedRightScanAfter A source.1.1 activation.lambda past) .both
        (pairedRightBlockLetterAt activation.lambda past input) hclose

/-- Direct first post-common strict-right checker equation. -/
theorem literalLeftSeamExactStageAt_first_eq_step_both
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (input : In₂ × In₁) :
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    let activation := profiledRawJointHybridExactRightActivation A hwin
      installed
    let source := installed.world.procOneSlot A
    let stage := package.literalLeftSeamExactStageAt A strategy hwin key .both
      .first [] input
    pairedCodeStateForRow A .first stage.root.slot.1.1 =
      A.step (pairedCodeStateForRow A .both source.1.1)
        (pairedRightRecordForRow .both
          (pairedRightBlockLetterAt activation.lambda [] input)) := by
  simpa [pairedRightScanAfter_nil, pairedRightScanInitial,
    pairedRightScanPairForRow, pairedRightScanStep, pairedCodeStateForRow] using
    package.literalLeftSeamExactStageAt_first_eq_rightScanStep_both A strategy
      hwin key [] input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
