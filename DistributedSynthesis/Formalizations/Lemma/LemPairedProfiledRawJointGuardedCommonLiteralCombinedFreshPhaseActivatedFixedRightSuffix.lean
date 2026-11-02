/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedIndexedRecurrentSeed
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedTailOperational

/-!
# Fixed-right acceptance after literal activation

A live right stage already carries a fixed-policy root whose complete
strict-right word is accepted.  Prepending the activating strict-right input,
dropping that one physical record, and re-rooting the same finite carrier at
its post-activation state therefore proves `AcceptsFrom` for the remaining
strict-right suffix.  The indexed recurrent simulation then transports this
fact to the tagged child carrier selected by the stage.

No new controller, table abstraction, or executable side test is introduced.
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

/-- Put the activating strict-right input in front of the remaining physical
right-block input word. -/
def literalRightSeamPrependStrictRightInput
    (input : In₁ × In₂) (tail : Nat → In₂ × In₁) :
    Nat → In₂ × In₁
  | 0 => (input.2, input.1)
  | n + 1 => tail n

section
omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂]

@[simp] theorem literalRightSeamPrependStrictRightInput_zero
    (input : In₁ × In₂) (tail : Nat → In₂ × In₁) :
    literalRightSeamPrependStrictRightInput input tail 0 =
      (input.2, input.1) :=
  rfl

@[simp] theorem literalRightSeamPrependStrictRightInput_succ
    (input : In₁ × In₂) (tail : Nat → In₂ × In₁)
    (n : Nat) :
    literalRightSeamPrependStrictRightInput input tail (n + 1) = tail n :=
  rfl

/-- Dropping the activating record from the prepended all-right environment
leaves exactly the requested all-right suffix. -/
theorem drop_literalRightSeamPrependStrictRightEnvironment
    (input : In₁ × In₂) (tail : Nat → In₂ × In₁) :
    OmegaWord.drop
        (profiledRawJointUnitStrictRightEnvironment
          (literalRightSeamPrependStrictRightInput input tail)) 1 =
      profiledRawJointUnitStrictRightEnvironment tail := by
  funext n
  change
    profiledRawJointUnitStrictRightEnvironment
        (literalRightSeamPrependStrictRightInput input tail) (1 + n) = _
  rw [Nat.one_add]
  rfl

end

/-! ## Fixed-unit suffix -/

/-- The fixed `Unit` carrier selected by a stage accepts after its activating
strict-right record, from the exact DPA state reached by that record. -/
theorem literalRightSeamStage_unit_after_strictRight_acceptsFrom
    (package : Package A strategy hwin (initial := initial))
    (stage : RightStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂) (tail : Nat → In₂ × In₁) :
    let source :=
      package.literalRightSeamTaggedChildSource A strategy hwin stage.child
    let policy :=
      package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child
    let bank :=
      package.literalRightSeamTaggedChildControllerBank A strategy hwin
        stage.child
    let adapter :=
      profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy source
        policy bank (InitialOne := Unit) (InitialTwo := Unit)
          (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy source policy bank
        adapter
    let inputs := literalRightSeamPrependStrictRightInput input tail
    let physicalEnv := profiledRawJointUnitStrictRightEnvironment inputs
    let freshState :=
      profiledRawJointUnitFreshMatchedRightState A strategy source policy bank
        adapter stage.root stage.row outputOne outputTwo
    let fullWord :=
      (unitKernel.globalMachine.reroot freshState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv
    let postState := unitKernel.physicalController.advanceControls freshState
      ⟨input.1, input.2, .right⟩
    A.AcceptsFrom
      (A.runFrom (pairedCodeStateForRow A stage.row stage.root.slot.1.1)
        fullWord 1)
      ((unitKernel.globalMachine.reroot postState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo
          (profiledRawJointUnitStrictRightEnvironment tail)) := by
  dsimp only
  let source :=
    package.literalRightSeamTaggedChildSource A strategy hwin stage.child
  let policy :=
    package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child
  let bank :=
    package.literalRightSeamTaggedChildControllerBank A strategy hwin
      stage.child
  let adapter :=
    profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy source policy
      bank (InitialOne := Unit) (InitialTwo := Unit)
        (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
  let unitKernel :=
    profiledRawJointUnitPolicyLeaderFreeKernel A strategy source policy bank
      adapter
  let inputs := literalRightSeamPrependStrictRightInput input tail
  let physicalEnv := profiledRawJointUnitStrictRightEnvironment inputs
  let freshState :=
    profiledRawJointUnitFreshMatchedRightState A strategy source policy bank
      adapter stage.root stage.row outputOne outputTwo
  let fullWord :=
    (unitKernel.globalMachine.reroot freshState).globalMachineTraceWord
      unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv
  let postState := unitKernel.physicalController.advanceControls freshState
    ⟨input.1, input.2, .right⟩
  have hwhole : A.AcceptsFrom
      (pairedCodeStateForRow A stage.row stage.root.slot.1.1) fullWord := by
    exact profiledRawJointUnitFreshMatchedRight_acceptsFrom A strategy source
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
          (profiledRawJointUnitStrictRightEnvironment tail)) by
    let G := unitKernel.globalMachine.reroot freshState
    have hreroot := G.reroot_globalMachineTraceWord_drop
      unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv 1
    have hstate : G.globalStateTrace physicalEnv 1 = postState := by
      rfl
    rw [hstate,
      drop_literalRightSeamPrependStrictRightEnvironment input tail] at hreroot
    simpa [FiniteGlobalRoundMachine.reroot] using hreroot.symm] at htail
  exact htail

/-! ## Tagged indexed suffix -/

/-- The same post-activation `AcceptsFrom` fact for the actual tagged indexed
carrier.  Same-child preservation is supplied by the recurrent seed module;
the acceptance input is the fixed stage theorem above. -/
theorem literalRightSeamStage_tagged_after_strictRight_acceptsFrom
    (package : Package A strategy hwin (initial := initial))
    (stage : RightStage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂)
    (input : In₁ × In₂) (tail : Nat → In₂ × In₁) :
    let source :=
      package.literalRightSeamTaggedChildSource A strategy hwin stage.child
    let policy :=
      package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child
    let bank :=
      package.literalRightSeamTaggedChildControllerBank A strategy hwin
        stage.child
    let adapter :=
      profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy source
        policy bank (InitialOne := Unit) (InitialTwo := Unit)
          (ExceptionalOne := Unit) (ExceptionalTwo := Unit)
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy source policy bank
        adapter
    let inputs := literalRightSeamPrependStrictRightInput input tail
    let physicalEnv := profiledRawJointUnitStrictRightEnvironment inputs
    let freshState :=
      profiledRawJointUnitFreshMatchedRightState A strategy source policy bank
        adapter stage.root stage.row outputOne outputTwo
    let fullWord :=
      (unitKernel.globalMachine.reroot freshState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo physicalEnv
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    let indexedKernel := TaggedKernel A strategy hwin package
    let indexedState := indexedKernel.physicalController.advanceControls
      ((matched.1, outputOne), (matched.2, outputTwo))
      ⟨input.1, input.2, .right⟩
    A.AcceptsFrom
      (A.runFrom (pairedCodeStateForRow A stage.row stage.root.slot.1.1)
        fullWord 1)
      ((indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
        indexedKernel.globalOutputOne indexedKernel.globalOutputTwo
          (profiledRawJointUnitStrictRightEnvironment tail)) := by
  dsimp only
  apply package.literalRightSeamStage_after_strictRight_acceptsFrom A strategy
    hwin stage outputOne outputTwo input
      (profiledRawJointUnitStrictRightEnvironment tail)
  simpa [profiledRawJointUnitFreshMatchedRightState] using
    package.literalRightSeamStage_unit_after_strictRight_acceptsFrom A strategy
      hwin stage outputOne outputTwo input tail

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
