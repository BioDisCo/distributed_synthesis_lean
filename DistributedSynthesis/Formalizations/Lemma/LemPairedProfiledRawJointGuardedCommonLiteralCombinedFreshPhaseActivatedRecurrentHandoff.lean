/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedRecurrentReroot
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedIndexedRecurrentSeed
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointIndexedPolicyRecurrentPhysicalAcceptance

/-!
# Same-child handoff after the activated relay flush

The two-receive flush identifies the actual acknowledged controller with an
exact state of the tagged indexed recurrent kernel.  This file composes that
identity with the existing indexed-to-fixed-policy recurrent simulation.
Consequently the flushed state still belongs to one literal child policy and
acceptance of the corresponding fixed `Unit` suffix transfers all the way
back to the complete activated physical word.

The child key and all cut data are proof-side witnesses.  Neither executable
endpoint receives a key, graph, orientation, hierarchy side, or leader bit.
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

private abbrev TaggedKernel (package : Package A strategy hwin
    (initial := initial)) :=
  package.literalRightSeamTaggedExecutableKernel A strategy hwin

private abbrev UnitAdapter
    (package : Package A strategy hwin (initial := initial))
    (key : TaggedChild A strategy hwin package) :=
  profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin key)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin key)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin key)
    (InitialOne := Unit) (InitialTwo := Unit)
    (ExceptionalOne := Unit) (ExceptionalTwo := Unit)

private abbrev UnitKernel
    (package : Package A strategy hwin (initial := initial))
    (key : TaggedChild A strategy hwin package) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin key)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin key)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin key)
    (UnitAdapter A strategy hwin package key)

/-- One tagged recurrent state and its corresponding state in one fixed child
policy.  This is just the repository's existing same-key relation, with its
dependent parameters specialized to the literal tagged family. -/
structure LiteralRightSeamTaggedSameChildAt
    (package : Package A strategy hwin (initial := initial))
    (tagged : (TaggedKernel A strategy hwin package).globalMachine.State) where
  key : TaggedChild A strategy hwin package
  unitState : (UnitKernel A strategy hwin package key).globalMachine.State
  recurrent :
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (TaggedChild A strategy hwin package)
      (package.literalRightSeamTaggedChildSource A strategy hwin)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
      Unit Unit Unit Unit key tagged unitState

/-- One physical round preserves the selected child.  This operation lives
beside the same-child structure so its private Unit-kernel abbreviation is
shared definitionally with the finite-trace reroot below. -/
noncomputable def LiteralRightSeamTaggedSameChildAt.advance
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (round : EnvironmentRound In₁ In₂) :
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin
      ((TaggedKernel A strategy hwin package).physicalController.advanceControls
        tagged round) := by
  let unitFinal :=
    (UnitKernel A strategy hwin package same.key).physicalController
      |>.advanceControls same.unitState round
  refine ⟨same.key, unitFinal, ?_⟩
  exact same.recurrent.advanceControls A strategy
    (TaggedChild A strategy hwin package)
    (package.literalRightSeamTaggedChildSource A strategy hwin)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
    (package.literalRightSeamTaggedUnitAdapter A strategy hwin)
    same.key (UnitAdapter A strategy hwin package same.key) round

/-- Same-child preservation composes literally with the exact two-round
flush descendant. -/
noncomputable def
    LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChild
    (package : Package A strategy hwin (initial := initial))
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy
      hwin package}
    {two : ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy
      hwin package}
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (atStart :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let state := actual.globalMachine.globalStateTrace env n
      package.LiteralRightSeamTaggedSameChildAt A strategy hwin
        ((one, state.1.2), (two, state.2.2))) :
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin flush.tagged := by
  dsimp only at atStart
  let afterOne := atStart.advance A strategy hwin package (env n)
  let afterTwo := afterOne.advance A strategy hwin package (env (n + 1))
  refine ⟨afterTwo.key, afterTwo.unitState, ?_⟩
  rw [flush.descendant]
  simpa [afterOne, afterTwo,
    FiniteGlobalRoundMachine.globalStateTrace_succ, OmegaWord.drop,
    FiniteGlobalRoundMachine.reroot,
    ProfiledRawJointLeaderFreeKernel.globalMachine] using afterTwo.recurrent

/-- If the corresponding fixed-policy suffix accepts from the actual checker
state at the flushed cut, then the complete activated physical word accepts.
All finite-prefix and relay/indexed transfers are discharged here. -/
theorem
    literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_sameChild
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy
      hwin package)
    (two : ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy
      hwin package)
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (atStart :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let state := actual.globalMachine.globalStateTrace env n
      package.LiteralRightSeamTaggedSameChildAt A strategy hwin
        ((one, state.1.2), (two, state.2.2)))
    (hunit :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      let same := flush.sameChild A strategy hwin package atStart
      A.AcceptsFrom (A.run actualWord (n + 2))
        (((UnitKernel A strategy hwin package same.key).globalMachine.reroot
          same.unitState).globalMachineTraceWord
            (UnitKernel A strategy hwin package same.key).globalOutputOne
            (UnitKernel A strategy hwin package same.key).globalOutputTwo
            (OmegaWord.drop env (n + 2)))) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  let actual :=
    package.literalCombinedFreshPhaseActivatedPhysicalController A strategy hwin
  let actualWord := actual.globalMachine.globalMachineTraceWord
    actual.globalOutputOne actual.globalOutputTwo env
  let same := flush.sameChild A strategy hwin package atStart
  have htagged :
      A.AcceptsFrom (A.run actualWord (n + 2))
        (((TaggedKernel A strategy hwin package).globalMachine.reroot
          flush.tagged).globalMachineTraceWord
            (TaggedKernel A strategy hwin package).globalOutputOne
            (TaggedKernel A strategy hwin package).globalOutputTwo
            (OmegaWord.drop env (n + 2))) := by
    exact (profiledRawJointIndexedPolicyRecurrentAt_acceptsFrom_iff A strategy
      (TaggedChild A strategy hwin package)
      (package.literalRightSeamTaggedChildSource A strategy hwin)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
      (package.literalRightSeamTaggedUnitAdapter A strategy hwin)
      same.key (UnitAdapter A strategy hwin package same.key)
      flush.tagged same.unitState same.recurrent
      (OmegaWord.drop env (n + 2)) (A.run actualWord (n + 2))).mpr hunit
  exact package.literalCombinedFreshPhaseActivated_accepts_of_duplicateRecurrentAt
    A strategy hwin env (n + 2) flush.tagged flush.duplicate htagged

/-- Physical-acceptance presentation of the same handoff.  This is the exact
socket filled by the existing four-regime fixed-policy machinery, based at
the genuine DPA state after the activated prefix. -/
theorem
    literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_physicalAcceptance
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy
      hwin package)
    (two : ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy
      hwin package)
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (atStart :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let state := actual.globalMachine.globalStateTrace env n
      package.LiteralRightSeamTaggedSameChildAt A strategy hwin
        ((one, state.1.2), (two, state.2.2)))
    (physical :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      let same := flush.sameChild A strategy hwin package atStart
      let unit := UnitKernel A strategy hwin package same.key
      A.FiniteGlobalMachinePhysicalAcceptanceFrom
        (A.run actualWord (n + 2))
        (unit.globalMachine.reroot same.unitState)
        unit.globalOutputOne unit.globalOutputTwo
        (OmegaWord.drop env (n + 2))) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  apply
    package.literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_sameChild
      A strategy hwin env n one two flush atStart
  let actual :=
    package.literalCombinedFreshPhaseActivatedPhysicalController A strategy hwin
  let actualWord := actual.globalMachine.globalMachineTraceWord
    actual.globalOutputOne actual.globalOutputTwo env
  let same := flush.sameChild A strategy hwin package atStart
  let unit := UnitKernel A strategy hwin package same.key
  exact A.finiteGlobalMachineTraceWord_acceptsFrom_of_physicalAcceptanceFrom
    (A.run actualWord (n + 2))
    (unit.globalMachine.reroot same.unitState)
    unit.globalOutputOne unit.globalOutputTwo (OmegaWord.drop env (n + 2))
    physical

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
