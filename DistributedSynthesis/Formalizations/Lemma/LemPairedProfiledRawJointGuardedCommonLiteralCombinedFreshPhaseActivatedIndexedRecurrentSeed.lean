/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointIndexedPolicyRecurrentSimulation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitDummyExceptionalAdapter

/-!
# Same-child recurrent seed at literal activation

The phase switch does not merely enter two arbitrary recurrent controls.  Its
retained literal stage reconstructs one matched-right owner/receiver pair at
one dependent child.  This file records that pair as the existing
`ProfiledRawJointIndexedPolicyRecurrentAt` relation and advances the relation
through the strict-right activation round.

The selected child is only a proof-side witness.  Neither executable endpoint
is told a graph, orientation, hierarchy side, leader bit, history, or view.
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

private abbrev TaggedChild (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy hwin
    package

private abbrev RightStage (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

private abbrev TaggedKernel (package : Package A strategy hwin
    (initial := initial)) :=
  package.literalRightSeamTaggedExecutableKernel A strategy hwin

/-! ## Exact matched-right seed -/

/-- The matched pair reconstructed from a live literal stage is exactly a
same-child recurrent seed for the indexed-to-fixed-policy simulation. -/
theorem literalRightSeamStageMatched_recurrentAt
    (package : Package A strategy hwin (initial := initial))
    (stage : RightStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (TaggedChild A strategy hwin package)
      (package.literalRightSeamTaggedChildSource A strategy hwin)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
      Unit Unit Unit Unit stage.child
      ((matched.1, outputOne), (matched.2, outputTwo))
      (((.rightOwner ()
          (package.literalRightSeamStageInitialRightOwner A strategy hwin
            stage)), outputOne),
        ((.rightReceiver ()
          (package.literalRightSeamStageInitialRightReceiver A strategy hwin
            stage)), outputTwo)) := by
  dsimp only
  exact .matchedRight
    (package.literalRightSeamStageInitialRightOwner A strategy hwin stage)
    (package.literalRightSeamStageInitialRightReceiver A strategy hwin stage)
    outputOne outputTwo

/-! ## Preservation across the activation round -/

/-- Advancing the exact stage seed through the strict-right activation round
preserves the same dependent child and is literally simulated by the fixed
`Unit`-indexed carrier at that child.  This is the adjacent
strict-left/strict-right seam: the preceding strict-left is represented by
`stage`, and `input` is the activating strict-right record. -/
theorem literalRightSeamStage_after_strictRight_recurrentAt
    (package : Package A strategy hwin (initial := initial))
    (stage : RightStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    let indexedKernel := TaggedKernel A strategy hwin package
    let unitAdapter :=
      profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
        (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildControllerBank A strategy hwin
          stage.child)
        (InitialOne := Unit) (InitialTwo := Unit)
        (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy
        (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildControllerBank A strategy hwin
          stage.child) unitAdapter
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (TaggedChild A strategy hwin package)
      (package.literalRightSeamTaggedChildSource A strategy hwin)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
      Unit Unit Unit Unit stage.child
      (indexedKernel.physicalController.advanceControls
        ((matched.1, outputOne), (matched.2, outputTwo))
        ⟨input.1, input.2, .right⟩)
      (unitKernel.physicalController.advanceControls
        (((.rightOwner ()
            (package.literalRightSeamStageInitialRightOwner A strategy hwin
              stage)), outputOne),
          ((.rightReceiver ()
            (package.literalRightSeamStageInitialRightReceiver A strategy hwin
              stage)), outputTwo))
        ⟨input.1, input.2, .right⟩) := by
  dsimp only
  let seed := package.literalRightSeamStageMatched_recurrentAt A strategy hwin
    stage outputOne outputTwo
  exact seed.advanceControls A strategy
    (TaggedChild A strategy hwin package)
    (package.literalRightSeamTaggedChildSource A strategy hwin)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
    (package.literalRightSeamTaggedUnitAdapter A strategy hwin)
    stage.child
    (profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin
        stage.child)
      (InitialOne := Unit) (InitialTwo := Unit)
      (ExceptionalOne := Unit) (ExceptionalTwo := Unit))
    ⟨input.1, input.2, .right⟩

/-! ## `AcceptsFrom` handoff -/

/-- Acceptance of the fixed-policy suffix after the activation round is
equivalent to acceptance of the actual tagged indexed suffix.  The DPA state
is explicit, so a finite pending prefix can supply the genuine current state
without restarting the checker. -/
theorem literalRightSeamStage_after_strictRight_acceptsFrom_iff
    (package : Package A strategy hwin (initial := initial))
    (stage : RightStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂)
    (env : EnvironmentSequence In₁ In₂) (state : A.State) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    let indexedKernel := TaggedKernel A strategy hwin package
    let unitAdapter :=
      profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
        (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildControllerBank A strategy hwin
          stage.child)
        (InitialOne := Unit) (InitialTwo := Unit)
        (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy
        (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
        (package.literalRightSeamTaggedChildControllerBank A strategy hwin
          stage.child) unitAdapter
    let indexedState := indexedKernel.physicalController.advanceControls
      ((matched.1, outputOne), (matched.2, outputTwo))
      ⟨input.1, input.2, .right⟩
    let unitState := unitKernel.physicalController.advanceControls
      (((.rightOwner ()
          (package.literalRightSeamStageInitialRightOwner A strategy hwin
            stage)), outputOne),
        ((.rightReceiver ()
          (package.literalRightSeamStageInitialRightReceiver A strategy hwin
            stage)), outputTwo))
      ⟨input.1, input.2, .right⟩
    A.AcceptsFrom state
        ((indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
          indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env) ↔
      A.AcceptsFrom state
        ((unitKernel.globalMachine.reroot unitState).globalMachineTraceWord
          unitKernel.globalOutputOne unitKernel.globalOutputTwo env) := by
  dsimp only
  apply profiledRawJointIndexedPolicyRecurrentAt_acceptsFrom_iff A strategy
    (TaggedChild A strategy hwin package)
    (package.literalRightSeamTaggedChildSource A strategy hwin)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
    (package.literalRightSeamTaggedUnitAdapter A strategy hwin)
    stage.child
    (profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin stage.child)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin
        stage.child)
      (InitialOne := Unit) (InitialTwo := Unit)
      (ExceptionalOne := Unit) (ExceptionalTwo := Unit))
  exact package.literalRightSeamStage_after_strictRight_recurrentAt A strategy
    hwin stage outputOne outputTwo input

/-- One-directional form used by the activated-controller handoff. -/
theorem literalRightSeamStage_after_strictRight_acceptsFrom
    (package : Package A strategy hwin (initial := initial))
    (stage : RightStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂)
    (env : EnvironmentSequence In₁ In₂) (state : A.State)
    (haccepts :
      let unitAdapter :=
        profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
          (package.literalRightSeamTaggedChildSource A strategy hwin
            stage.child)
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            stage.child)
          (package.literalRightSeamTaggedChildControllerBank A strategy hwin
            stage.child)
          (InitialOne := Unit) (InitialTwo := Unit)
          (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
      let unitKernel :=
        profiledRawJointUnitPolicyLeaderFreeKernel A strategy
          (package.literalRightSeamTaggedChildSource A strategy hwin
            stage.child)
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            stage.child)
          (package.literalRightSeamTaggedChildControllerBank A strategy hwin
            stage.child) unitAdapter
      let unitState := unitKernel.physicalController.advanceControls
        (((.rightOwner ()
            (package.literalRightSeamStageInitialRightOwner A strategy hwin
              stage)), outputOne),
          ((.rightReceiver ()
            (package.literalRightSeamStageInitialRightReceiver A strategy hwin
              stage)), outputTwo))
        ⟨input.1, input.2, .right⟩
      A.AcceptsFrom state
        ((unitKernel.globalMachine.reroot unitState).globalMachineTraceWord
          unitKernel.globalOutputOne unitKernel.globalOutputTwo env)) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    let indexedKernel := TaggedKernel A strategy hwin package
    let indexedState := indexedKernel.physicalController.advanceControls
      ((matched.1, outputOne), (matched.2, outputTwo))
      ⟨input.1, input.2, .right⟩
    A.AcceptsFrom state
      ((indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
        indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env) := by
  exact (package.literalRightSeamStage_after_strictRight_acceptsFrom_iff A
    strategy hwin stage outputOne outputTwo input env state).mpr haccepts

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
