/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedStreamingEmissionLocality
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOverlayGlobalTraceSlice

/-!
# Installing an epoch overlay in the witnessed streaming emission view

`ProfiledOpenWitnessedStreamingEmissionView` proves the four local-event
congruence laws needed for distributed implementability.  Those laws do not,
by themselves, say which proof-global right/left evaluation is returned by
`view` along one concrete run.  This file isolates that remaining operational
law at its weakest useful granularity.

The tracking predicates below do **not** add an orientation or strict-leader
flag to either local process.  The side is classified externally in the proof,
and the predicate only says that the actual Mealy emissions along the already
fixed global trace are the emissions of the boundary overlay advanced through
that epoch.  The generic Mealy timing theorem then turns tracking into the
output-agreement fields consumed by the global trace/overlay joins.
-/

namespace DistributedSynthesis

universe i u v x y s c₁ c₂

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ treeState : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A treeState).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (semanticState : ProfiledOpenIndexedOptionalControlledSemanticState A
    strategy hwin basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A policy)
variable
  (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
    strategy hwin basis initialCode policy semanticState initialRoot)
variable
  (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
    In₁ In₂ Out₁ Out₂)

private abbrev streamingBase :=
  ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin basis
    initialCode policy semanticState initialRoot package controller

private noncomputable abbrev streamingEmission
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller) :=
  ProfiledOpenWitnessedStreamingEmissionView.emission A strategy hwin basis
    initialCode policy semanticState initialRoot package controller V

/-- The literal output pairs produced by the installed Mealy view during the
half-open interval `[start, stop)`. -/
noncomputable def profiledOpenWitnessedStreamingEpochEmissions
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat) :
    List (Out₁ × Out₂) :=
  let rounds := environmentSlice env start stop
  List.ofFn fun j : Fin rounds.length ↦
    streamingEmission A strategy hwin basis initialCode policy semanticState
      initialRoot package controller V
      ((streamingBase A strategy hwin basis initialCode policy semanticState
        initialRoot package controller).globalStateTrace env (start + j))
      (env (start + j))

/-- Minimal right-epoch installation law.  It concerns the actual global
Mealy trace, not information made available to either local process. -/
def ProfiledOpenWitnessedStreamingRightEpochOverlayTracking
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) : Prop :=
  profiledOpenWitnessedStreamingEpochEmissions A strategy hwin basis
      initialCode policy semanticState initialRoot package controller V env
      start stop =
    (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay
      (leftMovesOfRounds (environmentSlice env start stop))).map
        RoundRecord.outputPair

/-- Left mirror of the minimal installation law. -/
def ProfiledOpenWitnessedStreamingLeftEpochOverlayTracking
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) : Prop :=
  profiledOpenWitnessedStreamingEpochEmissions A strategy hwin basis
      initialCode policy semanticState initialRoot package controller V env
      start stop =
    (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay
      (leftMovesOfRounds (environmentSlice env start stop))).map
        RoundRecord.outputPair

/-- Normal form of the lifted machine's output-coordinate slice. -/
theorem profiledOpenWitnessedStreaming_globalTraceSlice_outputPairs
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat) :
    (omegaPrefix
        (OmegaWord.drop
          ((FiniteGlobalRoundMachine.withMealyEmission
              (streamingBase A strategy hwin basis initialCode policy
                semanticState initialRoot package controller)
              (streamingEmission A strategy hwin basis initialCode policy
                semanticState initialRoot package controller V)).globalMachineTraceWord
              (FiniteGlobalRoundMachine.withMealyEmissionOutputOne
                (streamingEmission A strategy hwin basis initialCode policy
                  semanticState initialRoot package controller V))
              (FiniteGlobalRoundMachine.withMealyEmissionOutputTwo
                (streamingEmission A strategy hwin basis initialCode policy
                  semanticState initialRoot package controller V))
              env)
          start)
        (environmentSlice env start stop).length).map RoundRecord.outputPair =
      profiledOpenWitnessedStreamingEpochEmissions A strategy hwin basis
        initialCode policy semanticState initialRoot package controller V env
        start stop := by
  classical
  unfold profiledOpenWitnessedStreamingEpochEmissions omegaPrefix
  dsimp only
  rw [List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, OmegaWord.drop_apply]
  rw [FiniteGlobalRoundMachine.withMealyEmission_globalMachineTraceWord_apply]
  rfl

/-- Right tracking is exactly the extra operational fact required by the
abstract global output-agreement interface. -/
theorem ProfiledOpenWitnessedStreamingRightEpochOverlayTracking.outputAgreement
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (htrack : ProfiledOpenWitnessedStreamingRightEpochOverlayTracking A
      strategy hwin basis initialCode policy semanticState initialRoot package
      controller V env start stop overlay) :
    ProfiledOpenWitnessedRightOverlayEpochOutputAgreement A initialCode
      (FiniteGlobalRoundMachine.withMealyEmission
        (streamingBase A strategy hwin basis initialCode policy semanticState
          initialRoot package controller)
        (streamingEmission A strategy hwin basis initialCode policy
          semanticState initialRoot package controller V))
      (FiniteGlobalRoundMachine.withMealyEmissionOutputOne
        (streamingEmission A strategy hwin basis initialCode policy
          semanticState initialRoot package controller V))
      (FiniteGlobalRoundMachine.withMealyEmissionOutputTwo
        (streamingEmission A strategy hwin basis initialCode policy
          semanticState initialRoot package controller V))
      env start stop overlay := by
  unfold ProfiledOpenWitnessedRightOverlayEpochOutputAgreement
  dsimp only
  rw [profiledOpenWitnessedStreaming_globalTraceSlice_outputPairs A strategy
    hwin basis initialCode policy semanticState initialRoot package controller]
  simpa only [ProfiledOpenWitnessedStreamingRightEpochOverlayTracking] using
    htrack

/-- Left tracking supplies the left global output-agreement field. -/
theorem ProfiledOpenWitnessedStreamingLeftEpochOverlayTracking.outputAgreement
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (htrack : ProfiledOpenWitnessedStreamingLeftEpochOverlayTracking A
      strategy hwin basis initialCode policy semanticState initialRoot package
      controller V env start stop overlay) :
    ProfiledOpenWitnessedLeftOverlayEpochOutputAgreement A initialCode
      (FiniteGlobalRoundMachine.withMealyEmission
        (streamingBase A strategy hwin basis initialCode policy semanticState
          initialRoot package controller)
        (streamingEmission A strategy hwin basis initialCode policy
          semanticState initialRoot package controller V))
      (FiniteGlobalRoundMachine.withMealyEmissionOutputOne
        (streamingEmission A strategy hwin basis initialCode policy
          semanticState initialRoot package controller V))
      (FiniteGlobalRoundMachine.withMealyEmissionOutputTwo
        (streamingEmission A strategy hwin basis initialCode policy
          semanticState initialRoot package controller V))
      env start stop overlay := by
  unfold ProfiledOpenWitnessedLeftOverlayEpochOutputAgreement
  dsimp only
  rw [profiledOpenWitnessedStreaming_globalTraceSlice_outputPairs A strategy
    hwin basis initialCode policy semanticState initialRoot package controller]
  simpa only [ProfiledOpenWitnessedStreamingLeftEpochOverlayTracking] using
    htrack

end

end DetParityAutomaton

end DistributedSynthesis
