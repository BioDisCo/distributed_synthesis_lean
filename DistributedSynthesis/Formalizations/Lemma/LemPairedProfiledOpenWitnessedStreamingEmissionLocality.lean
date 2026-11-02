/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedStreamingQueryAccumulator
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenMealyLocalEventCongruence

/-!
# Locality endpoint for the concrete witnessed streaming recurrence

The proof-side source machine in this file is not an abstract placeholder.
It is the concrete finite recurrence already constructed by
`profiledOpenWitnessedStreamingPhysicalMachine`: distinguished fixed-policy
candidate, common bank, streaming query, recut phase, receipt bits, and the
two finite controller coordinates.

An `EmissionView` installs the two proof-erased right/left evaluations used
for the next physical Mealy output.  Its four laws are exactly the remaining
semantic transition test.  The concrete streaming step itself is already
present in every conclusion, so branch, query, phase, and epoch-reset
preservation are not additional obligations.  The laws mention only the two
honest local-event relations; they do not expose an orientation, strict
leader, or permanently hidden bit to either process.

Once these four laws hold, the generic Mealy-to-Moore and local-congruence
constructions give `ReachableBeliefsUniform` for the actual finite machine in
one arrow.
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

/-- The already-constructed finite source recurrence, before installing the
physical Mealy output. -/
abbrev ProfiledOpenWitnessedStreamingEmissionBase :=
  profiledOpenWitnessedStreamingPhysicalMachine A strategy hwin basis
    initialCode policy semanticState initialRoot package controller

private def streamingEmissionRound
    (inputOne : In₁) (inputTwo : In₂) (graph : Graph) :
    EnvironmentRound In₁ In₂ :=
  { inputOne := inputOne, inputTwo := inputTwo, graph := graph }

/-- A proof-erased emission installation on the concrete streaming state.

The four fields are deliberately the only residual.  In particular there is
no separate field for preservation of the branch/query/phase recurrence:
each target is the literal concrete `base.step` target. -/
structure ProfiledOpenWitnessedStreamingEmissionView where
  view :
    (ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin basis
      initialCode policy semanticState initialRoot package controller).State →
      ProfiledOpenLocalEventEmissionState A strategy hwin basis initialCode
  noRecvOne : ∀ {left right},
    ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
        (view left) (view right) →
      ∀ (inputOne : In₁) (leftHidden rightHidden : In₂),
        ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
          (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
            basis initialCode policy semanticState initialRoot package
              controller).step left
                (streamingEmissionRound inputOne leftHidden .right)))
          (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
            basis initialCode policy semanticState initialRoot package
              controller).step right
                (streamingEmissionRound inputOne rightHidden .right)))
  noRecvTwo : ∀ {left right},
    ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
        (view left) (view right) →
      ∀ (inputTwo : In₂) (leftHidden rightHidden : In₁),
        ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
          (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
            basis initialCode policy semanticState initialRoot package
              controller).step left
                (streamingEmissionRound leftHidden inputTwo .left)))
          (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
            basis initialCode policy semanticState initialRoot package
              controller).step right
                (streamingEmissionRound rightHidden inputTwo .left)))
  recvOne : ∀ {left right},
    ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
        (view left) (view right) →
    ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
        (view left) (view right) →
      ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
        (leftGraph = .left ∨ leftGraph = .both) →
        (rightGraph = .left ∨ rightGraph = .both) →
          ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
            (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
              basis initialCode policy semanticState initialRoot package
                controller).step left
                  (streamingEmissionRound inputOne inputTwo leftGraph)))
            (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
              basis initialCode policy semanticState initialRoot package
                controller).step right
                  (streamingEmissionRound inputOne inputTwo rightGraph)))
  recvTwo : ∀ {left right},
    ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
        (view left) (view right) →
    ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
        (view left) (view right) →
      ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
        (leftGraph = .right ∨ leftGraph = .both) →
        (rightGraph = .right ∨ rightGraph = .both) →
          ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
            (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
              basis initialCode policy semanticState initialRoot package
                controller).step left
                  (streamingEmissionRound inputOne inputTwo leftGraph)))
            (view ((ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin
              basis initialCode policy semanticState initialRoot package
                controller).step right
                  (streamingEmissionRound inputOne inputTwo rightGraph)))

namespace ProfiledOpenWitnessedStreamingEmissionView

/-- The literal physical Mealy emission installed on the concrete streaming
source state. -/
noncomputable def emission
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller) :
    (ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin basis
        initialCode policy semanticState initialRoot package controller).State →
      EnvironmentRound In₁ In₂ → Out₁ × Out₂ :=
  fun state round ↦
    profiledOpenLocalEventEmission A strategy hwin basis initialCode
      (V.view state) round

/-- The four semantic view laws instantiate the generic local congruence on
the actual streaming step. -/
noncomputable def mealyLocalCongruence
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller) :
    FiniteGlobalRoundMachine.MealyLocalCongruence
      (ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      V.emission :=
  profiledOpenLocalEventMealyLocalCongruence A strategy hwin basis initialCode
    (ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    V.view V.noRecvOne V.noRecvTwo V.recvOne V.recvTwo

/-- **Concrete dangerous-zone endpoint.**  No output-uniformity hypothesis
remains after the four transition laws of `V`; the result is for the literal
streaming branch/query/recut recurrence followed by the exact Mealy emission.
-/
theorem reachableBeliefsUniform
    (V : ProfiledOpenWitnessedStreamingEmissionView A strategy hwin basis
      initialCode policy semanticState initialRoot package controller) :
    (FiniteGlobalRoundMachine.withMealyEmission
        (ProfiledOpenWitnessedStreamingEmissionBase A strategy hwin basis
          initialCode policy semanticState initialRoot package controller)
        V.emission).ReachableBeliefsUniform
      (FiniteGlobalRoundMachine.withMealyEmissionOutputOne V.emission)
      (FiniteGlobalRoundMachine.withMealyEmissionOutputTwo V.emission) :=
  V.mealyLocalCongruence.reachableBeliefsUniform

end ProfiledOpenWitnessedStreamingEmissionView

end

end DetParityAutomaton

end DistributedSynthesis
