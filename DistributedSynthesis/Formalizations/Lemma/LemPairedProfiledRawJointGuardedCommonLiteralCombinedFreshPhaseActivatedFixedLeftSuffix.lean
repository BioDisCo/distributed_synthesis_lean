/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedExecutableKernel
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralStagedFixedTailAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointIndexedPolicyRecurrentSimulation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitDummyExceptionalAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedTailOperational

/-!
# Fixed-left acceptance after literal mirror activation

This is the exact mirror of the fixed-right activation handoff.  A live left
stage reconstructs one matched-left pair at one dependent literal child.  The
existing indexed-to-`Unit` recurrent relation preserves that child through the
activating strict-left round.  The stage's certified fixed-left word, one-step
suffix transport, and finite-machine rerooting then prove acceptance from the
exact post-activation checker state.

The child and orientation are proof-side witnesses only.  Neither endpoint is
given a graph, hierarchy side, leader bit, history, or semantic view.
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
  ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy hwin
    package

private abbrev LeftStage (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

private abbrev TaggedKernel (package : Package A strategy hwin
    (initial := initial)) :=
  package.literalLeftSeamTaggedExecutableKernel A strategy hwin

/-! ## Same-child mirror seed -/

/-- The pair reconstructed from a live mirror stage is exactly the
matched-left constructor of the indexed recurrent relation. -/
theorem literalLeftSeamStageMatched_recurrentAt
    (package : Package A strategy hwin (initial := initial))
    (stage : LeftStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂) :
    let matched := package.literalLeftSeamStageMatched A strategy hwin stage
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (TaggedChild A strategy hwin package)
      (package.literalLeftSeamTaggedChildSource A strategy hwin)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin)
      (package.literalLeftSeamTaggedChildControllerBank A strategy hwin)
      Unit Unit Unit Unit stage.child
      ((matched.1, outputOne), (matched.2, outputTwo))
      (((.leftReceiver ()
          (package.literalLeftSeamStageInitialLeftReceiver A strategy hwin
            stage)), outputOne),
        ((.leftOwner ()
          (package.literalLeftSeamStageInitialLeftOwner A strategy hwin
            stage)), outputTwo)) := by
  dsimp only
  exact .matchedLeft
    (package.literalLeftSeamStageInitialLeftReceiver A strategy hwin stage)
    (package.literalLeftSeamStageInitialLeftOwner A strategy hwin stage)
    outputOne outputTwo

/-- The same child survives the activating strict-left transition. -/
theorem literalLeftSeamStage_after_strictLeft_recurrentAt
    (package : Package A strategy hwin (initial := initial))
    (stage : LeftStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂) :
    let matched := package.literalLeftSeamStageMatched A strategy hwin stage
    let indexedKernel := TaggedKernel A strategy hwin package
    let unitAdapter :=
      profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
        (package.literalLeftSeamTaggedChildSource A strategy hwin stage.child)
        (package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child)
        (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
          stage.child)
        (InitialOne := Unit) (InitialTwo := Unit)
        (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy
        (package.literalLeftSeamTaggedChildSource A strategy hwin stage.child)
        (package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child)
        (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
          stage.child) unitAdapter
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (TaggedChild A strategy hwin package)
      (package.literalLeftSeamTaggedChildSource A strategy hwin)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin)
      (package.literalLeftSeamTaggedChildControllerBank A strategy hwin)
      Unit Unit Unit Unit stage.child
      (indexedKernel.physicalController.advanceControls
        ((matched.1, outputOne), (matched.2, outputTwo))
        ⟨input.1, input.2, .left⟩)
      (unitKernel.physicalController.advanceControls
        (((.leftReceiver ()
            (package.literalLeftSeamStageInitialLeftReceiver A strategy hwin
              stage)), outputOne),
          ((.leftOwner ()
            (package.literalLeftSeamStageInitialLeftOwner A strategy hwin
              stage)), outputTwo))
        ⟨input.1, input.2, .left⟩) := by
  dsimp only
  let seed := package.literalLeftSeamStageMatched_recurrentAt A strategy hwin
    stage outputOne outputTwo
  exact seed.advanceControls A strategy
    (TaggedChild A strategy hwin package)
    (package.literalLeftSeamTaggedChildSource A strategy hwin)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin)
    (package.literalLeftSeamTaggedChildControllerBank A strategy hwin)
    (package.literalLeftSeamTaggedUnitAdapter A strategy hwin)
    stage.child
    (profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
      (package.literalLeftSeamTaggedChildSource A strategy hwin stage.child)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child)
      (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
        stage.child)
      (InitialOne := Unit) (InitialTwo := Unit)
      (ExceptionalOne := Unit) (ExceptionalTwo := Unit))
    ⟨input.1, input.2, .left⟩

/-! ## One-letter fixed-left suffix -/

/-- Prepend the activating strict-left input to the remaining left-block
input word. -/
def literalLeftSeamPrependStrictLeftInput
    (input : In₁ × In₂) (tail : Nat → In₁ × In₂) :
    Nat → In₁ × In₂
  | 0 => input
  | n + 1 => tail n

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Environment drop commutes with the mirror input prepend. -/
theorem drop_literalLeftSeamPrependStrictLeftEnvironment
    (input : In₁ × In₂) (tail : Nat → In₁ × In₂) :
    OmegaWord.drop
        (profiledRawJointUnitStrictLeftEnvironment
          (literalLeftSeamPrependStrictLeftInput input tail)) 1 =
      profiledRawJointUnitStrictLeftEnvironment tail := by
  funext n
  change
    profiledRawJointUnitStrictLeftEnvironment
        (literalLeftSeamPrependStrictLeftInput input tail) (1 + n) = _
  rw [Nat.one_add]
  rfl

/-- The fixed `Unit` mirror carrier accepts from the exact state reached after
the activating strict-left record. -/
theorem literalLeftSeamStage_unit_after_strictLeft_acceptsFrom
    (package : Package A strategy hwin (initial := initial))
    (stage : LeftStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂) (tail : Nat → In₁ × In₂) :
    let source :=
      package.literalLeftSeamTaggedChildSource A strategy hwin stage.child
    let policy :=
      package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child
    let bank :=
      package.literalLeftSeamTaggedChildControllerBank A strategy hwin
        stage.child
    let adapter :=
      profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy source
        policy bank (InitialOne := Unit) (InitialTwo := Unit)
          (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy source policy bank
        adapter
    let inputs := literalLeftSeamPrependStrictLeftInput input tail
    let physicalEnv := profiledRawJointUnitStrictLeftEnvironment inputs
    let freshState :=
      profiledRawJointUnitFreshMatchedLeftState A strategy source policy bank
        adapter stage.root stage.row outputOne outputTwo
    let fullWord :=
      (unitKernel.globalMachine.reroot freshState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv
    let postState := unitKernel.physicalController.advanceControls freshState
      ⟨input.1, input.2, .left⟩
    A.AcceptsFrom
      (A.runFrom (pairedCodeStateForRow A stage.row stage.root.slot.1.1)
        fullWord 1)
      ((unitKernel.globalMachine.reroot postState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment tail)) := by
  dsimp only
  let source :=
    package.literalLeftSeamTaggedChildSource A strategy hwin stage.child
  let policy :=
    package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child
  let bank :=
    package.literalLeftSeamTaggedChildControllerBank A strategy hwin
      stage.child
  let adapter :=
    profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy source policy
      bank (InitialOne := Unit) (InitialTwo := Unit)
        (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
  let unitKernel :=
    profiledRawJointUnitPolicyLeaderFreeKernel A strategy source policy bank
      adapter
  let inputs := literalLeftSeamPrependStrictLeftInput input tail
  let physicalEnv := profiledRawJointUnitStrictLeftEnvironment inputs
  let freshState :=
    profiledRawJointUnitFreshMatchedLeftState A strategy source policy bank
      adapter stage.root stage.row outputOne outputTwo
  let fullWord :=
    (unitKernel.globalMachine.reroot freshState).globalMachineTraceWord
      unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv
  let postState := unitKernel.physicalController.advanceControls freshState
    ⟨input.1, input.2, .left⟩
  have hwhole : A.AcceptsFrom
      (pairedCodeStateForRow A stage.row stage.root.slot.1.1) fullWord := by
    exact profiledRawJointUnitFreshMatchedLeft_acceptsFrom A strategy source
      policy bank adapter stage.root stage.row outputOne outputTwo inputs
  have htail : A.AcceptsFrom
      (A.runFrom (pairedCodeStateForRow A stage.row stage.root.slot.1.1)
        fullWord 1)
      (OmegaWord.drop fullWord 1) :=
    (A.acceptsFrom_runFrom_drop_iff
      (pairedCodeStateForRow A stage.row stage.root.slot.1.1) fullWord 1).mpr
        hwhole
  rw [show OmegaWord.drop fullWord 1 =
      ((unitKernel.globalMachine.reroot postState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment tail)) by
    let G := unitKernel.globalMachine.reroot freshState
    have hreroot := G.reroot_globalMachineTraceWord_drop
      unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv 1
    have hstate : G.globalStateTrace physicalEnv 1 = postState := by
      rfl
    rw [hstate,
      drop_literalLeftSeamPrependStrictLeftEnvironment input tail] at hreroot
    simpa [FiniteGlobalRoundMachine.reroot] using hreroot.symm] at htail
  exact htail

/-! ## Indexed mirror suffix -/

/-- The fixed-left post-activation acceptance transfers to the tagged indexed
mirror carrier at the same child. -/
theorem literalLeftSeamStage_tagged_after_strictLeft_acceptsFrom
    (package : Package A strategy hwin (initial := initial))
    (stage : LeftStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂) (tail : Nat → In₁ × In₂) :
    let source :=
      package.literalLeftSeamTaggedChildSource A strategy hwin stage.child
    let policy :=
      package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child
    let bank :=
      package.literalLeftSeamTaggedChildControllerBank A strategy hwin
        stage.child
    let adapter :=
      profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy source
        policy bank (InitialOne := Unit) (InitialTwo := Unit)
          (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy source policy bank
        adapter
    let inputs := literalLeftSeamPrependStrictLeftInput input tail
    let physicalEnv := profiledRawJointUnitStrictLeftEnvironment inputs
    let freshState :=
      profiledRawJointUnitFreshMatchedLeftState A strategy source policy bank
        adapter stage.root stage.row outputOne outputTwo
    let fullWord :=
      (unitKernel.globalMachine.reroot freshState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv
    let matched := package.literalLeftSeamStageMatched A strategy hwin stage
    let indexedKernel := TaggedKernel A strategy hwin package
    let indexedState := indexedKernel.physicalController.advanceControls
      ((matched.1, outputOne), (matched.2, outputTwo))
      ⟨input.1, input.2, .left⟩
    A.AcceptsFrom
      (A.runFrom (pairedCodeStateForRow A stage.row stage.root.slot.1.1)
        fullWord 1)
      ((indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
        indexedKernel.globalOutputOne indexedKernel.globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment tail)) := by
  dsimp only
  apply (profiledRawJointIndexedPolicyRecurrentAt_acceptsFrom_iff A strategy
    (TaggedChild A strategy hwin package)
    (package.literalLeftSeamTaggedChildSource A strategy hwin)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin)
    (package.literalLeftSeamTaggedChildControllerBank A strategy hwin)
    (package.literalLeftSeamTaggedUnitAdapter A strategy hwin)
    stage.child
    (profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
      (package.literalLeftSeamTaggedChildSource A strategy hwin stage.child)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child)
      (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
        stage.child)
      (InitialOne := Unit) (InitialTwo := Unit)
      (ExceptionalOne := Unit) (ExceptionalTwo := Unit))
    _ _
    (package.literalLeftSeamStage_after_strictLeft_recurrentAt A strategy hwin
      stage outputOne outputTwo input)
    (profiledRawJointUnitStrictLeftEnvironment tail) _).mpr
  simpa [profiledRawJointUnitFreshMatchedLeftState] using
    package.literalLeftSeamStage_unit_after_strictLeft_acceptsFrom A strategy
      hwin stage outputOne outputTwo input tail

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
