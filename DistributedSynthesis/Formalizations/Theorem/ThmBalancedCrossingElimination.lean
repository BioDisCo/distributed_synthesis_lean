/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyCrossing

/-!
# Balanced half-step crossing elimination

This repairs the under-specified intermediary observation in Lemma 12.  At a
target with strict information order, the less-informed player receives their
own target observation while the more-informed player receives the knowledge
set that identifies precisely the less-informed target information class.  The
more-informed player's own target observation is delayed until the forced
second half-step.  Hence a reversal passes through equality rather than a
direct strict-order crossing.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

theorem PlayHistory.observations1_getLast?_last
    {H : FiniteConcurrentGame.{u}} (history : H.PlayHistory) :
    history.observations1.getLast? = some (H.observe1 history.lastState) := by
  cases history with
  | initial => rfl
  | step previous actionOne actionTwo nature =>
      rw [PlayHistory.observations1_step]
      simp [PlayHistory.lastState]

theorem PlayHistory.observations2_getLast?_last
    {H : FiniteConcurrentGame.{u}} (history : H.PlayHistory) :
    history.observations2.getLast? = some (H.observe2 history.lastState) := by
  cases history with
  | initial => rfl
  | step previous actionOne actionTwo nature =>
      rw [PlayHistory.observations2_step]
      simp [PlayHistory.lastState]

/-- A bridge letter is either the less-informed player's own target
observation or the more-informed player's representation of the less-informed
information class. -/
abbrev BalancedBridgeOne := Sum G.Observation1 (Finset G.Observation1)
abbrev BalancedBridgeTwo := Sum G.Observation2 (Finset G.Observation2)

/-- The repaired doubled arena. -/
noncomputable def balancedCrossingEliminationGame : FiniteConcurrentGame where
  State := G.CrossingState
  Action1 := G.Action1
  Action2 := G.Action2
  Nature := G.Nature
  Observation1 := Sum (G.Observation1 × Fin 2) G.BalancedBridgeOne
  Observation2 := Sum (G.Observation2 × Fin 2) G.BalancedBridgeTwo
  stateFinite := by infer_instance
  action1Finite := G.action1Finite
  action2Finite := G.action2Finite
  natureFinite := G.natureFinite
  observation1Finite := by
    classical
    infer_instance
  observation2Finite := by
    classical
    infer_instance
  initial := G.crossingEliminationGame.initial
  next := G.crossingEliminationGame.next
  observe1 state :=
    if state.1 then
      Sum.inr <|
        if G.rankOneMachine.output state.2.2.1 = 0 then
          Sum.inr (G.knowledgeTwoOfOneMachine.output state.2.2.2)
        else
          Sum.inl (G.observe1 state.2.1)
    else
      Sum.inl
        (G.observe1 state.2.1, G.rankOneMachine.output state.2.2.1)
  observe2 state :=
    if state.1 then
      Sum.inr <|
        if G.rankTwoMachine.output state.2.2.2 = 0 then
          Sum.inr (G.knowledgeOneOfTwoMachine.output state.2.2.1)
        else
          Sum.inl (G.observe2 state.2.1)
    else
      Sum.inl
        (G.observe2 state.2.1, G.rankTwoMachine.output state.2.2.2)
  priority state := G.priority state.2.1

/-- Canonical embedding into the balanced arena. -/
noncomputable def balancedCrossingLift :
    G.PlayHistory -> G.balancedCrossingEliminationGame.PlayHistory
  | .initial => .initial
  | .step previous actionOne actionTwo nature =>
      ((balancedCrossingLift previous).step actionOne actionTwo nature).step
        actionOne actionTwo nature

noncomputable def balancedCrossingBridgeLift
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.balancedCrossingEliminationGame.PlayHistory :=
  (G.balancedCrossingLift history).step actionOne actionTwo nature

theorem balancedCrossingLift_lastState (history : G.PlayHistory) :
    (G.balancedCrossingLift history).lastState =
      (false, history.lastState,
        G.rankOneMachine.run history.observations1,
        G.rankTwoMachine.run history.observations2) := by
  induction history with
  | initial =>
      simp [balancedCrossingLift, balancedCrossingEliminationGame,
        crossingEliminationGame, MooreController.run, rankOneMachine,
        rankTwoMachine, PlayHistory.lastState, initialRankTwoBelief]
  | step previous actionOne actionTwo nature ih =>
      rw [balancedCrossingLift]
      change G.balancedCrossingEliminationGame.next
        (G.balancedCrossingEliminationGame.next
          (G.balancedCrossingLift previous).lastState
          actionOne actionTwo nature) actionOne actionTwo nature = _
      rw [ih]
      simp [balancedCrossingEliminationGame, crossingEliminationGame,
        crossingAdvance, PlayHistory.lastState,
        PlayHistory.observations1_step, PlayHistory.observations2_step]

theorem balancedCrossingBridgeLift_lastState
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    (G.balancedCrossingBridgeLift history actionOne actionTwo nature).lastState =
      (true, (history.step actionOne actionTwo nature).lastState,
        G.rankOneMachine.run
          (history.step actionOne actionTwo nature).observations1,
        G.rankTwoMachine.run
          (history.step actionOne actionTwo nature).observations2) := by
  unfold balancedCrossingBridgeLift
  change G.balancedCrossingEliminationGame.next
    (G.balancedCrossingLift history).lastState actionOne actionTwo nature = _
  rw [G.balancedCrossingLift_lastState]
  simp [balancedCrossingEliminationGame, crossingEliminationGame,
    crossingAdvance, PlayHistory.lastState,
    PlayHistory.observations1_step, PlayHistory.observations2_step]

/-- Exact balanced player-one bridge letter. -/
theorem balancedCrossingBridgeLift_observe1
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    let target := history.step actionOne actionTwo nature
    G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift history actionOne actionTwo nature).lastState =
      Sum.inr
        (if G.informationRankOne target = 0 then
          Sum.inr (G.knowledgeTwoOfOneAt target)
        else Sum.inl (G.observe1 target.lastState)) := by
  dsimp only
  rw [G.balancedCrossingBridgeLift_lastState]
  simp only [balancedCrossingEliminationGame, if_true]
  rw [G.rankOneMachine_output_run]
  have hknowledge := G.knowledgeTwoOfOneMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeTwoOfOneMachine_run] at hknowledge
  rw [hknowledge]

/-- Exact balanced player-two bridge letter. -/
theorem balancedCrossingBridgeLift_observe2
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    let target := history.step actionOne actionTwo nature
    G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift history actionOne actionTwo nature).lastState =
      Sum.inr
        (if G.informationRankTwo target = 0 then
          Sum.inr (G.knowledgeOneOfTwoAt target)
        else Sum.inl (G.observe2 target.lastState)) := by
  dsimp only
  rw [G.balancedCrossingBridgeLift_lastState]
  simp only [balancedCrossingEliminationGame, if_true]
  rw [G.rankTwoMachine_output_run hhier]
  have hknowledge := G.knowledgeOneOfTwoMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeOneOfTwoMachine_run] at hknowledge
  rw [hknowledge]

theorem balancedCrossingLift_observe1 (history : G.PlayHistory) :
    G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingLift history).lastState =
      Sum.inl (G.observe1 history.lastState,
        G.informationRankOne history) := by
  rw [G.balancedCrossingLift_lastState]
  simp [balancedCrossingEliminationGame, G.rankOneMachine_output_run]

theorem balancedCrossingLift_observe2
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingLift history).lastState =
      Sum.inl (G.observe2 history.lastState,
        G.informationRankTwo history) := by
  rw [G.balancedCrossingLift_lastState]
  simp [balancedCrossingEliminationGame,
    G.rankTwoMachine_output_run hhier]

theorem balancedCrossingLift_observations1_congr
    (left right : G.PlayHistory)
    (heq : left.observations1 = right.observations1) :
    (G.balancedCrossingLift left).observations1 =
      (G.balancedCrossingLift right).observations1 := by
  induction left generalizing right with
  | initial =>
      have hright := G.eq_initial_of_observations1_eq_singleton right heq.symm
      subst right
      rfl
  | step left actionOne actionTwo nature ih =>
      cases right with
      | initial =>
          exfalso
          have hlen := congrArg List.length heq
          have hpos := G.observations1_length_pos left
          simp only [PlayHistory.observations1_step,
            PlayHistory.observations1_initial, List.length_append,
            List.length_singleton] at hlen
          omega
      | step right rightActionOne rightActionTwo rightNature =>
          rw [PlayHistory.observations1_step,
            PlayHistory.observations1_step] at heq
          obtain ⟨hprefix, hlast⟩ := List.append_inj' heq (by simp)
          have ih' := ih right hprefix
          rw [balancedCrossingLift, balancedCrossingLift,
            PlayHistory.observations1_step, PlayHistory.observations1_step,
            PlayHistory.observations1_step, PlayHistory.observations1_step,
            ih']
          have htarget :
              (left.step actionOne actionTwo nature).observations1 =
                (right.step rightActionOne rightActionTwo rightNature).observations1 :=
            by simpa only [PlayHistory.observations1_step] using heq
          have hrank := G.informationRankOne_consistent
            (left.step actionOne actionTwo nature)
            (right.step rightActionOne rightActionTwo rightNature) htarget
          have hbridgeObs :
              G.balancedCrossingEliminationGame.observe1
                  (G.balancedCrossingBridgeLift left actionOne actionTwo nature).lastState =
                G.balancedCrossingEliminationGame.observe1
                  (G.balancedCrossingBridgeLift right rightActionOne
                    rightActionTwo rightNature).lastState := by
            rw [G.balancedCrossingBridgeLift_observe1,
              G.balancedCrossingBridgeLift_observe1]
            by_cases hzero :
                G.informationRankOne
                  (left.step actionOne actionTwo nature) = 0
            · have hzeroRight :
                  G.informationRankOne
                    (right.step rightActionOne rightActionTwo rightNature) = 0 := by
                rwa [← hrank]
              rw [if_pos hzero, if_pos hzeroRight]
              congr 2
              exact G.knowledgeTwoOfOneAt_congr_observations2 _ _
                ((G.informationRankOne_eq_zero_iff _).mp hzero _
                  htarget.symm).symm
            · have hzeroRight :
                  G.informationRankOne
                    (right.step rightActionOne rightActionTwo rightNature) ≠ 0 := by
                rwa [← hrank]
              rw [if_neg hzero, if_neg hzeroRight]
              exact congrArg Sum.inr (congrArg Sum.inl (by
                simpa [PlayHistory.lastState] using
                  (List.singleton_inj.mp hlast)))
          have horiginalObs :
              G.balancedCrossingEliminationGame.observe1
                  (G.balancedCrossingLift
                    (left.step actionOne actionTwo nature)).lastState =
                G.balancedCrossingEliminationGame.observe1
                  (G.balancedCrossingLift
                    (right.step rightActionOne rightActionTwo rightNature)).lastState := by
            rw [G.balancedCrossingLift_observe1,
              G.balancedCrossingLift_observe1]
            exact congrArg Sum.inl (Prod.ext
              (by simpa [PlayHistory.lastState] using
                (List.singleton_inj.mp hlast)) hrank)
          change (G.balancedCrossingLift right).observations1 ++
              [G.balancedCrossingEliminationGame.observe1
                (G.balancedCrossingBridgeLift left actionOne actionTwo nature).lastState] ++
              [G.balancedCrossingEliminationGame.observe1
                (G.balancedCrossingLift
                  (left.step actionOne actionTwo nature)).lastState] = _
          rw [hbridgeObs, horiginalObs]
          rfl

theorem balancedCrossingLift_observations2_congr
    (hhier : G.DynamicHierarchy) (left right : G.PlayHistory)
    (heq : left.observations2 = right.observations2) :
    (G.balancedCrossingLift left).observations2 =
      (G.balancedCrossingLift right).observations2 := by
  induction left generalizing right with
  | initial =>
      have hright := G.eq_initial_of_observations2_eq_singleton right heq.symm
      subst right
      rfl
  | step left actionOne actionTwo nature ih =>
      cases right with
      | initial =>
          exfalso
          have hlen := congrArg List.length heq
          rw [PlayHistory.observations2_step] at hlen
          have hpos := G.observations1_length_pos left
          rw [G.observations_length_eq left] at hpos
          simp only [PlayHistory.observations2_initial, List.length_append,
            List.length_singleton] at hlen
          omega
      | step right rightActionOne rightActionTwo rightNature =>
          rw [PlayHistory.observations2_step,
            PlayHistory.observations2_step] at heq
          obtain ⟨hprefix, hlast⟩ := List.append_inj' heq (by simp)
          have ih' := ih right hprefix
          rw [balancedCrossingLift, balancedCrossingLift,
            PlayHistory.observations2_step, PlayHistory.observations2_step,
            PlayHistory.observations2_step, PlayHistory.observations2_step,
            ih']
          have htarget :
              (left.step actionOne actionTwo nature).observations2 =
                (right.step rightActionOne rightActionTwo rightNature).observations2 :=
            by simpa only [PlayHistory.observations2_step] using heq
          have hrank := G.informationRankTwo_consistent hhier
            (left.step actionOne actionTwo nature)
            (right.step rightActionOne rightActionTwo rightNature) htarget
          have hbridgeObs :
              G.balancedCrossingEliminationGame.observe2
                  (G.balancedCrossingBridgeLift left actionOne actionTwo nature).lastState =
                G.balancedCrossingEliminationGame.observe2
                  (G.balancedCrossingBridgeLift right rightActionOne
                    rightActionTwo rightNature).lastState := by
            rw [G.balancedCrossingBridgeLift_observe2 hhier,
              G.balancedCrossingBridgeLift_observe2 hhier]
            by_cases hzero :
                G.informationRankTwo
                  (left.step actionOne actionTwo nature) = 0
            · have hzeroRight :
                  G.informationRankTwo
                    (right.step rightActionOne rightActionTwo rightNature) = 0 := by
                rwa [← hrank]
              rw [if_pos hzero, if_pos hzeroRight]
              congr 2
              have hnot := (G.informationRankTwo_eq_zero_iff _).mp hzero
              have htwo := (hhier _).resolve_left hnot
              exact G.knowledgeOneOfTwoAt_congr_observations1 _ _
                (htwo _ htarget.symm).symm
            · have hzeroRight :
                  G.informationRankTwo
                    (right.step rightActionOne rightActionTwo rightNature) ≠ 0 := by
                rwa [← hrank]
              rw [if_neg hzero, if_neg hzeroRight]
              exact congrArg Sum.inr (congrArg Sum.inl (by
                simpa [PlayHistory.lastState] using
                  (List.singleton_inj.mp hlast)))
          have horiginalObs :
              G.balancedCrossingEliminationGame.observe2
                  (G.balancedCrossingLift
                    (left.step actionOne actionTwo nature)).lastState =
                G.balancedCrossingEliminationGame.observe2
                  (G.balancedCrossingLift
                    (right.step rightActionOne rightActionTwo rightNature)).lastState := by
            rw [G.balancedCrossingLift_observe2 hhier,
              G.balancedCrossingLift_observe2 hhier]
            exact congrArg Sum.inl (Prod.ext
              (by simpa [PlayHistory.lastState] using
                (List.singleton_inj.mp hlast)) hrank)
          change (G.balancedCrossingLift right).observations2 ++
              [G.balancedCrossingEliminationGame.observe2
                (G.balancedCrossingBridgeLift left actionOne actionTwo nature).lastState] ++
              [G.balancedCrossingEliminationGame.observe2
                (G.balancedCrossingLift
                  (left.step actionOne actionTwo nature)).lastState] = _
          rw [hbridgeObs, horiginalObs]
          rfl

def projectBalancedObservationOne :
    G.balancedCrossingEliminationGame.Observation1 -> Option G.Observation1
  | Sum.inl original => some original.1
  | Sum.inr _ => none

def projectBalancedObservationTwo :
    G.balancedCrossingEliminationGame.Observation2 -> Option G.Observation2
  | Sum.inl original => some original.1
  | Sum.inr _ => none

theorem project_balancedCrossingLift_observations1
    (history : G.PlayHistory) :
    (G.balancedCrossingLift history).observations1.filterMap
        G.projectBalancedObservationOne = history.observations1 := by
  induction history with
  | initial =>
      simp [balancedCrossingLift, balancedCrossingEliminationGame,
        crossingEliminationGame, projectBalancedObservationOne]
  | step previous actionOne actionTwo nature ih =>
      rw [balancedCrossingLift, PlayHistory.observations1_step,
        PlayHistory.observations1_step, List.filterMap_append,
        List.filterMap_append, ih]
      change previous.observations1 ++
          List.filterMap G.projectBalancedObservationOne
            [G.balancedCrossingEliminationGame.observe1
              (G.balancedCrossingBridgeLift previous actionOne actionTwo
                nature).lastState] ++
          List.filterMap G.projectBalancedObservationOne
            [G.balancedCrossingEliminationGame.observe1
              (G.balancedCrossingLift
                (previous.step actionOne actionTwo nature)).lastState] = _
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingLift_observe1]
      simp [projectBalancedObservationOne, PlayHistory.lastState]

theorem project_balancedCrossingLift_observations2
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    (G.balancedCrossingLift history).observations2.filterMap
        G.projectBalancedObservationTwo = history.observations2 := by
  induction history with
  | initial =>
      simp [balancedCrossingLift, balancedCrossingEliminationGame,
        crossingEliminationGame, projectBalancedObservationTwo]
  | step previous actionOne actionTwo nature ih =>
      rw [balancedCrossingLift, PlayHistory.observations2_step,
        PlayHistory.observations2_step, List.filterMap_append,
        List.filterMap_append, ih]
      change previous.observations2 ++
          List.filterMap G.projectBalancedObservationTwo
            [G.balancedCrossingEliminationGame.observe2
              (G.balancedCrossingBridgeLift previous actionOne actionTwo
                nature).lastState] ++
          List.filterMap G.projectBalancedObservationTwo
            [G.balancedCrossingEliminationGame.observe2
              (G.balancedCrossingLift
                (previous.step actionOne actionTwo nature)).lastState] = _
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingLift_observe2 hhier]
      simp [projectBalancedObservationTwo, PlayHistory.lastState]

theorem balancedCrossingLift_observations1_injective
    (left right : G.PlayHistory)
    (heq : (G.balancedCrossingLift left).observations1 =
      (G.balancedCrossingLift right).observations1) :
    left.observations1 = right.observations1 := by
  have h := congrArg
    (List.filterMap G.projectBalancedObservationOne) heq
  simpa [G.project_balancedCrossingLift_observations1] using h

theorem balancedCrossingLift_observations2_injective
    (hhier : G.DynamicHierarchy) (left right : G.PlayHistory)
    (heq : (G.balancedCrossingLift left).observations2 =
      (G.balancedCrossingLift right).observations2) :
    left.observations2 = right.observations2 := by
  have h := congrArg
    (List.filterMap G.projectBalancedObservationTwo) heq
  simpa [G.project_balancedCrossingLift_observations2 hhier] using h

/- Moved below the `BalancedCrossingRep` normal-form construction.
theorem balancedCrossingRep_phase_false_of_observations1_eq
    {alternative : G.balancedCrossingEliminationGame.PlayHistory}
    {phase : Bool} {represented history : G.PlayHistory}
    (rep : G.BalancedCrossingRep alternative phase represented)
    (heq : alternative.observations1 =
      (G.balancedCrossingLift history).observations1) : phase = false := by
  cases phase with
  | false => rfl
  | true =>
      exfalso
      have hlastGet := congrArg List.getLast? heq
      rw [PlayHistory.observations1_getLast?_last,
        PlayHistory.observations1_getLast?_last] at hlastGet
      have hlast := Option.some.inj hlastGet
      rw [G.balancedCrossingRep_lastState rep,
        G.balancedCrossingLift_lastState] at hlast
      simp [balancedCrossingEliminationGame] at hlast

theorem balancedCrossingRep_phase_false_of_observations2_eq
    {alternative : G.balancedCrossingEliminationGame.PlayHistory}
    {phase : Bool} {represented history : G.PlayHistory}
    (rep : G.BalancedCrossingRep alternative phase represented)
    (heq : alternative.observations2 =
      (G.balancedCrossingLift history).observations2) : phase = false := by
  cases phase with
  | false => rfl
  | true =>
      exfalso
      have hlast := congrArg List.getLast? heq
      have halt :=
        G.observations1_getLast?_eq
          (G := G.balancedCrossingEliminationGame) alternative
      have hlift :=
        G.observations1_getLast?_eq
          (G := G.balancedCrossingEliminationGame)
          (G.balancedCrossingLift history)
      -- Use the player-two observation analogue directly from nonempty lists.
      have hcurrent :
          G.balancedCrossingEliminationGame.observe2 alternative.lastState =
            G.balancedCrossingEliminationGame.observe2
              (G.balancedCrossingLift history).lastState := by
        have ha := PlayHistory.observations2_getLast?_last alternative
        have hb := PlayHistory.observations2_getLast?_last
          (G.balancedCrossingLift history)
        rw [ha, hb] at hlast
        exact Option.some.inj hlast
      rw [G.balancedCrossingRep_lastState rep,
        G.balancedCrossingLift_lastState] at hcurrent
      simp [balancedCrossingEliminationGame] at hcurrent

theorem balancedCrossingLift_oneDeterminesTwoAt_iff
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.balancedCrossingEliminationGame.OneDeterminesTwoAt
        (G.balancedCrossingLift history) ↔
      G.OneDeterminesTwoAt history := by
  constructor
  · intro hdet alternative heq
    have hliftOne := G.balancedCrossingLift_observations1_congr
      alternative history heq
    have hliftTwo := hdet (G.balancedCrossingLift alternative) hliftOne
    exact G.balancedCrossingLift_observations2_injective hhier _ _ hliftTwo
  · intro hdet alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase := G.balancedCrossingRep_phase_false_of_observations1_eq
      rep heq
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
      if_false] at hnormal
    have hrepresentedOne : represented.observations1 = history.observations1 :=
      G.balancedCrossingLift_observations1_injective represented history
        (hnormal.1.symm.trans heq)
    have hrepresentedTwo := hdet represented hrepresentedOne
    exact hnormal.2.trans
      (G.balancedCrossingLift_observations2_congr hhier represented history
        hrepresentedTwo)

theorem balancedCrossingLift_twoDeterminesOneAt_iff
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.balancedCrossingEliminationGame.TwoDeterminesOneAt
        (G.balancedCrossingLift history) ↔
      G.TwoDeterminesOneAt history := by
  constructor
  · intro hdet alternative heq
    have hliftTwo := G.balancedCrossingLift_observations2_congr
      hhier alternative history heq
    have hliftOne := hdet (G.balancedCrossingLift alternative) hliftTwo
    exact G.balancedCrossingLift_observations1_injective _ _ hliftOne
  · intro hdet alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase := G.balancedCrossingRep_phase_false_of_observations2_eq
      rep heq
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
      if_false] at hnormal
    have hrepresentedTwo : represented.observations2 = history.observations2 :=
      G.balancedCrossingLift_observations2_injective hhier represented history
        (hnormal.2.symm.trans heq)
    have hrepresentedOne := hdet represented hrepresentedTwo
    exact hnormal.1.trans
      (G.balancedCrossingLift_observations1_congr represented history
        hrepresentedOne)

/-- At a one-to-two reversal, equality of complete canonical bridge views is
the same for both players. -/
theorem balancedBridge_observations_equiv_one_to_two
    (hhier : G.DynamicHierarchy)
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsourceOne : G.OneDeterminesTwoAt source)
    (htargetNotOne : ¬ G.OneDeterminesTwoAt
      (source.step actionOne actionTwo nature)) :
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations1 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations1 ↔
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations2 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations2 := by
  let target := source.step actionOne actionTwo nature
  let alternativeTarget := alternativeSource.step alternativeActionOne
    alternativeActionTwo alternativeNature
  have htargetTwo : G.TwoDeterminesOneAt target :=
    (hhier target).resolve_left htargetNotOne
  constructor
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixOne : alternativeSource.observations1 = source.observations1 :=
      G.balancedCrossingLift_observations1_injective _ _ hprefixLift
    have haltNotOne : ¬ G.OneDeterminesTwoAt alternativeTarget := by
      intro haltOne
      have haltZero := (G.informationRankOne_eq_zero_iff _).mpr haltOne
      have htargetNonzero : G.informationRankOne target ≠ 0 := by
        exact fun hz => htargetNotOne
          ((G.informationRankOne_eq_zero_iff _).mp hz)
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1,
        if_pos haltZero, if_neg htargetNonzero] at hlastBridge
      simp at hlastBridge
    have haltTwo : G.TwoDeterminesOneAt alternativeTarget :=
      (hhier alternativeTarget).resolve_left haltNotOne
    have htargetNonzero : G.informationRankOne target ≠ 0 := by
      exact fun hz => htargetNotOne ((G.informationRankOne_eq_zero_iff _).mp hz)
    have haltNonzero : G.informationRankOne alternativeTarget ≠ 0 := by
      exact fun hz => haltNotOne ((G.informationRankOne_eq_zero_iff _).mp hz)
    rw [G.balancedCrossingBridgeLift_observe1,
      G.balancedCrossingBridgeLift_observe1,
      if_neg haltNonzero, if_neg htargetNonzero] at hlastBridge
    have hlastOne : G.observe1 alternativeTarget.lastState =
        G.observe1 target.lastState := by simpa using hlastBridge
    have hview := (G.balanced_bridge_view_equiv_one_to_two
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceOne haltTwo).mp
      ⟨hprefixOne, hlastOne⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations2_congr hhier _ _ hview.1
    · rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier]
      have hzTarget := (G.informationRankTwo_eq_zero_iff target).mpr htargetNotOne
      have hzAlt := (G.informationRankTwo_eq_zero_iff alternativeTarget).mpr haltNotOne
      rw [if_pos hzAlt, if_pos hzTarget, hview.2]
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixTwo : alternativeSource.observations2 = source.observations2 :=
      G.balancedCrossingLift_observations2_injective hhier _ _ hprefixLift
    have haltNotOne : ¬ G.OneDeterminesTwoAt alternativeTarget := by
      intro haltOne
      have htargetZero := (G.informationRankTwo_eq_zero_iff target).mpr htargetNotOne
      have haltNonzero : G.informationRankTwo alternativeTarget ≠ 0 := by
        intro hz
        exact haltOne ((G.informationRankTwo_eq_zero_iff _).mp hz)
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier,
        if_neg haltNonzero, if_pos htargetZero] at hlastBridge
      simp at hlastBridge
    have haltTwo : G.TwoDeterminesOneAt alternativeTarget :=
      (hhier alternativeTarget).resolve_left haltNotOne
    have hzTarget := (G.informationRankTwo_eq_zero_iff target).mpr htargetNotOne
    have hzAlt := (G.informationRankTwo_eq_zero_iff alternativeTarget).mpr haltNotOne
    rw [G.balancedCrossingBridgeLift_observe2 hhier,
      G.balancedCrossingBridgeLift_observe2 hhier,
      if_pos hzAlt, if_pos hzTarget] at hlastBridge
    have hknowledge : G.knowledgeOneOfTwoAt alternativeTarget =
        G.knowledgeOneOfTwoAt target := by simpa using hlastBridge
    have hview := (G.balanced_bridge_view_equiv_one_to_two
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceOne haltTwo).mpr
      ⟨hprefixTwo, hknowledge⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations1_congr _ _ hview.1
    · rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1]
      have htargetNonzero : G.informationRankOne target ≠ 0 := by
        exact fun hz => htargetNotOne
          ((G.informationRankOne_eq_zero_iff _).mp hz)
      have haltNonzero : G.informationRankOne alternativeTarget ≠ 0 := by
        exact fun hz => haltNotOne
          ((G.informationRankOne_eq_zero_iff _).mp hz)
      rw [if_neg haltNonzero, if_neg htargetNonzero, hview.2]

/-- A strict one-to-two reversal reaches an actual information tie at the
balanced bridge. -/
theorem balancedBridge_tie_one_to_two
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.OneStrictlyMoreInformedAt source)
    (htarget : G.TwoStrictlyMoreInformedAt
      (source.step actionOne actionTwo nature)) :
    G.balancedCrossingEliminationGame.OneDeterminesTwoAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) ∧
      G.balancedCrossingEliminationGame.TwoDeterminesOneAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) := by
  let bridge := G.balancedCrossingBridgeLift source actionOne actionTwo nature
  have bridgeEquiv := G.balancedBridge_observations_equiv_one_to_two hhier
    source
  constructor
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.1.symm.trans heq)
          rw [PlayHistory.observations1_getLast?_last,
            PlayHistory.observations1_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalOne := hnormalOne.symm.trans heq
    have hcanonicalTwo :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mp
        hcanonicalOne
    exact hnormalTwo.trans hcanonicalTwo
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.2.symm.trans heq)
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalTwo := hnormalTwo.symm.trans heq
    have hcanonicalOne :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mpr
        hcanonicalTwo
    exact hnormalOne.trans hcanonicalOne

/-- Symmetric complete-view equivalence for a two-to-one reversal. -/
theorem balancedBridge_observations_equiv_two_to_one
    (hhier : G.DynamicHierarchy)
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsourceTwo : G.TwoDeterminesOneAt source)
    (htargetNotTwo : ¬ G.TwoDeterminesOneAt
      (source.step actionOne actionTwo nature)) :
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations2 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations2 ↔
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations1 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations1 := by
  let target := source.step actionOne actionTwo nature
  let alternativeTarget := alternativeSource.step alternativeActionOne
    alternativeActionTwo alternativeNature
  have htargetOne : G.OneDeterminesTwoAt target :=
    (hhier target).resolve_right htargetNotTwo
  constructor
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixTwo :=
      G.balancedCrossingLift_observations2_injective hhier _ _ hprefixLift
    have haltOne : G.OneDeterminesTwoAt alternativeTarget := by
      by_contra hnot
      have hzAlt := (G.informationRankTwo_eq_zero_iff _).mpr hnot
      have hnonzeroTarget : G.informationRankTwo target ≠ 0 := by
        intro hz
        exact htargetNotTwo ((hhier target).resolve_left
          ((G.informationRankTwo_eq_zero_iff _).mp hz))
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier,
        if_pos hzAlt, if_neg hnonzeroTarget] at hlastBridge
      cases hlastBridge
    have hnonzeroTarget : G.informationRankTwo target ≠ 0 := by
      intro hz
      exact htargetNotTwo ((hhier target).resolve_left
        ((G.informationRankTwo_eq_zero_iff _).mp hz))
    have hnonzeroAlt : G.informationRankTwo alternativeTarget ≠ 0 := by
      intro hz
      exact haltOne ((G.informationRankTwo_eq_zero_iff _).mp hz)
    rw [G.balancedCrossingBridgeLift_observe2 hhier,
      G.balancedCrossingBridgeLift_observe2 hhier,
      if_neg hnonzeroAlt, if_neg hnonzeroTarget] at hlastBridge
    have hlastTwo : G.observe2 alternativeTarget.lastState =
        G.observe2 target.lastState :=
      Sum.inl.inj (Sum.inr.inj hlastBridge)
    have hview := (G.balanced_bridge_view_equiv_two_to_one
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceTwo haltOne).mp
      ⟨hprefixTwo, hlastTwo⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations1_congr _ _ hview.1
    · change G.balancedCrossingEliminationGame.observe1
          (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.balancedCrossingEliminationGame.observe1
          (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1]
      have hzTarget := (G.informationRankOne_eq_zero_iff target).mpr htargetOne
      have hzAlt := (G.informationRankOne_eq_zero_iff alternativeTarget).mpr haltOne
      rw [if_pos hzAlt, if_pos hzTarget, hview.2]
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixOne :=
      G.balancedCrossingLift_observations1_injective _ _ hprefixLift
    have haltOne : G.OneDeterminesTwoAt alternativeTarget := by
      by_contra hnot
      have hnonzeroAlt : G.informationRankOne alternativeTarget ≠ 0 :=
        fun hz => hnot ((G.informationRankOne_eq_zero_iff _).mp hz)
      have hzTarget := (G.informationRankOne_eq_zero_iff target).mpr htargetOne
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1,
        if_neg hnonzeroAlt, if_pos hzTarget] at hlastBridge
      cases hlastBridge
    have hzTarget := (G.informationRankOne_eq_zero_iff target).mpr htargetOne
    have hzAlt := (G.informationRankOne_eq_zero_iff alternativeTarget).mpr haltOne
    rw [G.balancedCrossingBridgeLift_observe1,
      G.balancedCrossingBridgeLift_observe1,
      if_pos hzAlt, if_pos hzTarget] at hlastBridge
    have hknowledge : G.knowledgeTwoOfOneAt alternativeTarget =
        G.knowledgeTwoOfOneAt target :=
      Sum.inr.inj (Sum.inr.inj hlastBridge)
    have hview := (G.balanced_bridge_view_equiv_two_to_one
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceTwo haltOne).mpr
      ⟨hprefixOne, hknowledge⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations2_congr hhier _ _ hview.1
    · change G.balancedCrossingEliminationGame.observe2
          (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.balancedCrossingEliminationGame.observe2
          (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier]
      have hnonzeroTarget : G.informationRankTwo target ≠ 0 := by
        intro hz
        exact htargetNotTwo ((hhier target).resolve_left
          ((G.informationRankTwo_eq_zero_iff _).mp hz))
      have hnonzeroAlt : G.informationRankTwo alternativeTarget ≠ 0 := by
        intro hz
        exact haltOne ((G.informationRankTwo_eq_zero_iff _).mp hz)
      rw [if_neg hnonzeroAlt, if_neg hnonzeroTarget, hview.2]

theorem balancedBridge_tie_two_to_one
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.TwoStrictlyMoreInformedAt source)
    (htarget : G.OneStrictlyMoreInformedAt
      (source.step actionOne actionTwo nature)) :
    G.balancedCrossingEliminationGame.OneDeterminesTwoAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) ∧
      G.balancedCrossingEliminationGame.TwoDeterminesOneAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) := by
  let bridge := G.balancedCrossingBridgeLift source actionOne actionTwo nature
  have bridgeEquiv := G.balancedBridge_observations_equiv_two_to_one hhier
    source
  constructor
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.1.symm.trans heq)
          rw [PlayHistory.observations1_getLast?_last,
            PlayHistory.observations1_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalOne := hnormalOne.symm.trans heq
    have hcanonicalTwo :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mpr
        hcanonicalOne
    exact hnormalTwo.trans hcanonicalTwo
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.2.symm.trans heq)
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalTwo := hnormalTwo.symm.trans heq
    have hcanonicalOne :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mp
        hcanonicalTwo
    exact hnormalOne.trans hcanonicalOne
-/

/-! ## The bridge equalisation lemma -/

/-- On a reversal from strict player-one information to strict player-two
information, the two balanced bridge views induce the same equivalence
relation.  This is the set-theoretic core absent from the informal proof of
Lemma 12. -/
theorem balanced_bridge_view_equiv_one_to_two
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsource : G.OneDeterminesTwoAt source)
    (haltTargetTwo : G.TwoDeterminesOneAt
      (alternativeSource.step alternativeActionOne alternativeActionTwo
        alternativeNature)) :
    (alternativeSource.observations1 = source.observations1 ∧
        G.observe1
            (alternativeSource.step alternativeActionOne alternativeActionTwo
              alternativeNature).lastState =
          G.observe1 (source.step actionOne actionTwo nature).lastState) ↔
      (alternativeSource.observations2 = source.observations2 ∧
        G.knowledgeOneOfTwoAt
            (alternativeSource.step alternativeActionOne alternativeActionTwo
              alternativeNature) =
          G.knowledgeOneOfTwoAt
            (source.step actionOne actionTwo nature)) := by
  classical
  let target := source.step actionOne actionTwo nature
  let alternativeTarget :=
    alternativeSource.step alternativeActionOne alternativeActionTwo
      alternativeNature
  constructor
  · rintro ⟨hsourceOne, hlastOne⟩
    have hsourceTwo :
        alternativeSource.observations2 = source.observations2 :=
      hsource alternativeSource hsourceOne
    refine ⟨hsourceTwo, ?_⟩
    apply G.knowledgeOneOfTwoAt_congr_observations1
    simp only [PlayHistory.observations1_step]
    exact congrArg₂ (fun xs last => xs ++ [last])
      hsourceOne hlastOne
  · rintro ⟨hsourceTwo, hknowledge⟩
    have hcurrentMem :
        G.observe2 alternativeTarget.lastState ∈
          G.knowledgeOneOfTwoAt alternativeTarget :=
      G.currentObservation_mem_knowledgeOneOfTwoAt alternativeTarget
    have hcurrentMemTarget :
        G.observe2 alternativeTarget.lastState ∈
          G.knowledgeOneOfTwoAt target := by
      rwa [← hknowledge]
    simp only [knowledgeOneOfTwoAt, Finset.mem_filter, Finset.mem_univ,
      true_and] at hcurrentMemTarget
    obtain ⟨witness, hwitnessOne, hwitnessLastTwo⟩ := hcurrentMemTarget
    have hwitnessShape :
        witness.observations1 = source.observations1 ++
          [G.observe1 target.lastState] := by
      simpa [target, PlayHistory.observations1_step] using hwitnessOne
    obtain ⟨witnessSource, witnessActionOne, witnessActionTwo,
      witnessNature, rfl, hwitnessSourceOne, hwitnessLastOne⟩ :=
        G.exists_step_of_observations1_eq_append witness source.observations1
          (G.observe1 target.lastState) (G.observations1_length_pos source)
          hwitnessShape
    have hwitnessSourceTwo :
        witnessSource.observations2 = source.observations2 :=
      hsource witnessSource hwitnessSourceOne
    have hwitnessTwoEqAlternative :
        (witnessSource.step witnessActionOne witnessActionTwo witnessNature).observations2 =
          alternativeTarget.observations2 := by
      simp only [PlayHistory.observations2_step, alternativeTarget]
      apply congrArg₂ (fun xs last => xs ++ [last])
      · exact hwitnessSourceTwo.trans hsourceTwo.symm
      · exact hwitnessLastTwo
    have hwitnessOneEqAlternative :
        (witnessSource.step witnessActionOne witnessActionTwo witnessNature).observations1 =
          alternativeTarget.observations1 :=
      haltTargetTwo _ hwitnessTwoEqAlternative
    have htargetOne : target.observations1 = alternativeTarget.observations1 := by
      exact hwitnessOne.symm.trans hwitnessOneEqAlternative
    simp only [target, alternativeTarget, PlayHistory.observations1_step] at htargetOne
    obtain ⟨hprefix, hlast⟩ := List.append_inj' htargetOne.symm (by simp)
    exact ⟨hprefix, by simpa using hlast⟩

/-- Symmetric bridge equalisation for a reversal from strict player-two to
strict player-one information. -/
theorem balanced_bridge_view_equiv_two_to_one
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsource : G.TwoDeterminesOneAt source)
    (haltTargetOne : G.OneDeterminesTwoAt
      (alternativeSource.step alternativeActionOne alternativeActionTwo
        alternativeNature)) :
    (alternativeSource.observations2 = source.observations2 ∧
        G.observe2
            (alternativeSource.step alternativeActionOne alternativeActionTwo
              alternativeNature).lastState =
          G.observe2 (source.step actionOne actionTwo nature).lastState) ↔
      (alternativeSource.observations1 = source.observations1 ∧
        G.knowledgeTwoOfOneAt
            (alternativeSource.step alternativeActionOne alternativeActionTwo
              alternativeNature) =
          G.knowledgeTwoOfOneAt
            (source.step actionOne actionTwo nature)) := by
  have hsourceSwap :
      G.swapPlayers.OneDeterminesTwoAt (G.swapHistory source) :=
    (G.swap_oneDeterminesTwoAt_iff source).mpr hsource
  have htargetSwap :
      G.swapPlayers.TwoDeterminesOneAt
        (G.swapHistory
          (alternativeSource.step alternativeActionOne alternativeActionTwo
            alternativeNature)) :=
    (G.swap_twoDeterminesOneAt_iff _).mpr haltTargetOne
  have h := G.swapPlayers.balanced_bridge_view_equiv_one_to_two
    (G.swapHistory source) (G.swapHistory alternativeSource)
    actionTwo alternativeActionTwo actionOne alternativeActionOne
    nature alternativeNature hsourceSwap
    (by simpa [swapHistory] using htargetSwap)
  rw [show (G.swapHistory alternativeSource).step alternativeActionTwo
      alternativeActionOne alternativeNature =
        G.swapHistory
          (alternativeSource.step alternativeActionOne alternativeActionTwo
            alternativeNature) by rfl,
    show (G.swapHistory source).step actionTwo actionOne nature =
        G.swapHistory (source.step actionOne actionTwo nature) by rfl] at h
  rw [G.swapHistory_observations1, G.swapHistory_observations1,
    G.swapHistory_observations2, G.swapHistory_observations2,
    G.swapHistory_lastState, G.swapHistory_lastState,
    G.swap_knowledgeOneOfTwoAt, G.swap_knowledgeOneOfTwoAt] at h
  exact h

/-! ## Arbitrary-history normal form -/

inductive BalancedCrossingRep :
    G.balancedCrossingEliminationGame.PlayHistory -> Bool ->
      G.PlayHistory -> Prop
  | initial : BalancedCrossingRep PlayHistory.initial false PlayHistory.initial
  | toBridge {doubled : G.balancedCrossingEliminationGame.PlayHistory}
      {history : G.PlayHistory}
      (rep : BalancedCrossingRep doubled false history)
      (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
      BalancedCrossingRep (doubled.step actionOne actionTwo nature) true
        (history.step actionOne actionTwo nature)
  | toOriginal {doubled : G.balancedCrossingEliminationGame.PlayHistory}
      {history : G.PlayHistory}
      (rep : BalancedCrossingRep doubled true history)
      (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
      BalancedCrossingRep (doubled.step actionOne actionTwo nature) false history

theorem balancedCrossingRep_lastState
    {doubled : G.balancedCrossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (rep : G.BalancedCrossingRep doubled phase history) :
    doubled.lastState =
      (phase, history.lastState,
        G.rankOneMachine.run history.observations1,
        G.rankTwoMachine.run history.observations2) := by
  induction rep with
  | initial =>
      simp [balancedCrossingEliminationGame, crossingEliminationGame,
        MooreController.run, rankOneMachine, rankTwoMachine,
        PlayHistory.lastState, initialRankTwoBelief]
  | toBridge rep actionOne actionTwo nature ih =>
      change G.balancedCrossingEliminationGame.next _ actionOne actionTwo nature = _
      rw [ih]
      simp [balancedCrossingEliminationGame, crossingEliminationGame,
        crossingAdvance, PlayHistory.lastState,
        PlayHistory.observations1_step, PlayHistory.observations2_step]
  | toOriginal rep actionOne actionTwo nature ih =>
      change G.balancedCrossingEliminationGame.next _ actionOne actionTwo nature = _
      rw [ih]
      simp [balancedCrossingEliminationGame, crossingEliminationGame]

theorem exists_balancedCrossingRep
    (doubled : G.balancedCrossingEliminationGame.PlayHistory) :
    ∃ (phase : Bool) (history : G.PlayHistory),
      G.BalancedCrossingRep doubled phase history := by
  induction doubled with
  | initial => exact ⟨false, PlayHistory.initial, BalancedCrossingRep.initial⟩
  | step previous actionOne actionTwo nature ih =>
      obtain ⟨phase, history, rep⟩ := ih
      cases phase with
      | false => exact ⟨true, history.step actionOne actionTwo nature,
          BalancedCrossingRep.toBridge rep actionOne actionTwo nature⟩
      | true => exact ⟨false, history,
          BalancedCrossingRep.toOriginal rep actionOne actionTwo nature⟩

def BalancedCrossingObservationNormal
    {doubled : G.balancedCrossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (_rep : G.BalancedCrossingRep doubled phase history) : Prop :=
  if phase then
    ∃ (previous : G.PlayHistory) (actionOne : G.Action1)
      (actionTwo : G.Action2) (nature : G.Nature),
      history = previous.step actionOne actionTwo nature ∧
        doubled.observations1 =
          (G.balancedCrossingBridgeLift previous actionOne actionTwo nature).observations1 ∧
        doubled.observations2 =
          (G.balancedCrossingBridgeLift previous actionOne actionTwo nature).observations2
  else
    doubled.observations1 =
        (G.balancedCrossingLift history).observations1 ∧
      doubled.observations2 =
        (G.balancedCrossingLift history).observations2

theorem balancedCrossingRep_observation_normal
    {doubled : G.balancedCrossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (rep : G.BalancedCrossingRep doubled phase history) :
    G.BalancedCrossingObservationNormal rep := by
  induction rep with
  | initial =>
      simp [BalancedCrossingObservationNormal, balancedCrossingLift]
  | toBridge rep actionOne actionTwo nature ih =>
      simp only [BalancedCrossingObservationNormal, if_true]
      simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
        if_false] at ih
      refine ⟨_, actionOne, actionTwo, nature, rfl, ?_, ?_⟩
      · rw [PlayHistory.observations1_step, ih.1]
        rw [balancedCrossingBridgeLift, PlayHistory.observations1_step]
        congr 1
        rw [G.balancedCrossingRep_lastState rep,
          G.balancedCrossingLift_lastState]
      · rw [PlayHistory.observations2_step, ih.2]
        rw [balancedCrossingBridgeLift, PlayHistory.observations2_step]
        congr 1
        rw [G.balancedCrossingRep_lastState rep,
          G.balancedCrossingLift_lastState]
  | toOriginal rep actionOne actionTwo nature ih =>
      simp only [BalancedCrossingObservationNormal, if_true] at ih
      simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
        if_false]
      obtain ⟨previous, originalOne, originalTwo, originalNature,
        hhistory, hobsOne, hobsTwo⟩ := ih
      constructor
      · rw [PlayHistory.observations1_step, hobsOne]
        rw [hhistory, balancedCrossingLift, PlayHistory.observations1_step,
          PlayHistory.observations1_step]
        rw [balancedCrossingBridgeLift, PlayHistory.observations1_step]
        congr 2
        rw [G.balancedCrossingRep_lastState rep]
        change _ = G.balancedCrossingEliminationGame.observe1
          (G.balancedCrossingEliminationGame.next
            (G.balancedCrossingBridgeLift previous originalOne originalTwo
              originalNature).lastState originalOne originalTwo originalNature)
        rw [G.balancedCrossingBridgeLift_lastState, hhistory]
        simp [balancedCrossingEliminationGame, crossingEliminationGame]
      · rw [PlayHistory.observations2_step, hobsTwo]
        rw [hhistory, balancedCrossingLift, PlayHistory.observations2_step,
          PlayHistory.observations2_step]
        rw [balancedCrossingBridgeLift, PlayHistory.observations2_step]
        congr 2
        rw [G.balancedCrossingRep_lastState rep]
        change _ = G.balancedCrossingEliminationGame.observe2
          (G.balancedCrossingEliminationGame.next
            (G.balancedCrossingBridgeLift previous originalOne originalTwo
              originalNature).lastState originalOne originalTwo originalNature)
        rw [G.balancedCrossingBridgeLift_lastState, hhistory]
        simp [balancedCrossingEliminationGame, crossingEliminationGame]

theorem balancedCrossingLift_rep (history : G.PlayHistory) :
    G.BalancedCrossingRep (G.balancedCrossingLift history) false history := by
  induction history with
  | initial => exact BalancedCrossingRep.initial
  | step previous actionOne actionTwo nature ih =>
      exact BalancedCrossingRep.toOriginal
        (BalancedCrossingRep.toBridge ih actionOne actionTwo nature)
        actionOne actionTwo nature

theorem balancedCrossingBridgeLift_rep
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.BalancedCrossingRep
      (G.balancedCrossingBridgeLift history actionOne actionTwo nature) true
      (history.step actionOne actionTwo nature) := by
  exact BalancedCrossingRep.toBridge (G.balancedCrossingLift_rep history)
    actionOne actionTwo nature

theorem balancedCrossingRep_phase_false_of_observations1_eq
    {alternative : G.balancedCrossingEliminationGame.PlayHistory}
    {phase : Bool} {represented history : G.PlayHistory}
    (rep : G.BalancedCrossingRep alternative phase represented)
    (heq : alternative.observations1 =
      (G.balancedCrossingLift history).observations1) : phase = false := by
  cases phase with
  | false => rfl
  | true =>
      exfalso
      have hlastGet := congrArg List.getLast? heq
      rw [PlayHistory.observations1_getLast?_last,
        PlayHistory.observations1_getLast?_last] at hlastGet
      have hlast := Option.some.inj hlastGet
      rw [G.balancedCrossingRep_lastState rep,
        G.balancedCrossingLift_lastState] at hlast
      simp [balancedCrossingEliminationGame] at hlast

theorem balancedCrossingRep_phase_false_of_observations2_eq
    {alternative : G.balancedCrossingEliminationGame.PlayHistory}
    {phase : Bool} {represented history : G.PlayHistory}
    (rep : G.BalancedCrossingRep alternative phase represented)
    (heq : alternative.observations2 =
      (G.balancedCrossingLift history).observations2) : phase = false := by
  cases phase with
  | false => rfl
  | true =>
      exfalso
      have hlast := congrArg List.getLast? heq
      have hcurrent :
          G.balancedCrossingEliminationGame.observe2 alternative.lastState =
            G.balancedCrossingEliminationGame.observe2
              (G.balancedCrossingLift history).lastState := by
        have ha := PlayHistory.observations2_getLast?_last alternative
        have hb := PlayHistory.observations2_getLast?_last
          (G.balancedCrossingLift history)
        rw [ha, hb] at hlast
        exact Option.some.inj hlast
      rw [G.balancedCrossingRep_lastState rep,
        G.balancedCrossingLift_lastState] at hcurrent
      simp [balancedCrossingEliminationGame] at hcurrent

theorem balancedCrossingLift_oneDeterminesTwoAt_iff
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.balancedCrossingEliminationGame.OneDeterminesTwoAt
        (G.balancedCrossingLift history) ↔
      G.OneDeterminesTwoAt history := by
  constructor
  · intro hdet alternative heq
    have hliftOne := G.balancedCrossingLift_observations1_congr
      alternative history heq
    have hliftTwo := hdet (G.balancedCrossingLift alternative) hliftOne
    exact G.balancedCrossingLift_observations2_injective hhier _ _ hliftTwo
  · intro hdet alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase := G.balancedCrossingRep_phase_false_of_observations1_eq
      rep heq
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
      if_false] at hnormal
    have hrepresentedOne : represented.observations1 = history.observations1 :=
      G.balancedCrossingLift_observations1_injective represented history
        (hnormal.1.symm.trans heq)
    have hrepresentedTwo := hdet represented hrepresentedOne
    exact hnormal.2.trans
      (G.balancedCrossingLift_observations2_congr hhier represented history
        hrepresentedTwo)

theorem balancedCrossingLift_twoDeterminesOneAt_iff
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.balancedCrossingEliminationGame.TwoDeterminesOneAt
        (G.balancedCrossingLift history) ↔
      G.TwoDeterminesOneAt history := by
  constructor
  · intro hdet alternative heq
    have hliftTwo := G.balancedCrossingLift_observations2_congr
      hhier alternative history heq
    have hliftOne := hdet (G.balancedCrossingLift alternative) hliftTwo
    exact G.balancedCrossingLift_observations1_injective _ _ hliftOne
  · intro hdet alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase := G.balancedCrossingRep_phase_false_of_observations2_eq
      rep heq
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
      if_false] at hnormal
    have hrepresentedTwo : represented.observations2 = history.observations2 :=
      G.balancedCrossingLift_observations2_injective hhier represented history
        (hnormal.2.symm.trans heq)
    have hrepresentedOne := hdet represented hrepresentedTwo
    exact hnormal.1.trans
      (G.balancedCrossingLift_observations1_congr represented history
        hrepresentedOne)

/-- At a one-to-two reversal, equality of complete canonical bridge views is
the same for both players. -/
theorem balancedBridge_observations_equiv_one_to_two
    (hhier : G.DynamicHierarchy)
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsourceOne : G.OneDeterminesTwoAt source)
    (htargetNotOne : ¬ G.OneDeterminesTwoAt
      (source.step actionOne actionTwo nature)) :
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations1 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations1 ↔
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations2 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations2 := by
  let target := source.step actionOne actionTwo nature
  let alternativeTarget := alternativeSource.step alternativeActionOne
    alternativeActionTwo alternativeNature
  have htargetTwo : G.TwoDeterminesOneAt target :=
    (hhier target).resolve_left htargetNotOne
  constructor
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixOne : alternativeSource.observations1 = source.observations1 :=
      G.balancedCrossingLift_observations1_injective _ _ hprefixLift
    have haltNotOne : ¬ G.OneDeterminesTwoAt alternativeTarget := by
      intro haltOne
      have haltZero := (G.informationRankOne_eq_zero_iff _).mpr haltOne
      have htargetNonzero : G.informationRankOne target ≠ 0 := by
        exact fun hz => htargetNotOne
          ((G.informationRankOne_eq_zero_iff _).mp hz)
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1,
        if_pos haltZero, if_neg htargetNonzero] at hlastBridge
      cases hlastBridge
    have haltTwo : G.TwoDeterminesOneAt alternativeTarget :=
      (hhier alternativeTarget).resolve_left haltNotOne
    have htargetNonzero : G.informationRankOne target ≠ 0 := by
      exact fun hz => htargetNotOne ((G.informationRankOne_eq_zero_iff _).mp hz)
    have haltNonzero : G.informationRankOne alternativeTarget ≠ 0 := by
      exact fun hz => haltNotOne ((G.informationRankOne_eq_zero_iff _).mp hz)
    rw [G.balancedCrossingBridgeLift_observe1,
      G.balancedCrossingBridgeLift_observe1,
      if_neg haltNonzero, if_neg htargetNonzero] at hlastBridge
    have hlastOne : G.observe1 alternativeTarget.lastState =
        G.observe1 target.lastState :=
      Sum.inl.inj (Sum.inr.inj hlastBridge)
    have hview := (G.balanced_bridge_view_equiv_one_to_two
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceOne haltTwo).mp
      ⟨hprefixOne, hlastOne⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations2_congr hhier _ _ hview.1
    · change G.balancedCrossingEliminationGame.observe2
          (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.balancedCrossingEliminationGame.observe2
          (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier]
      have hzTarget := (G.informationRankTwo_eq_zero_iff target).mpr htargetNotOne
      have hzAlt := (G.informationRankTwo_eq_zero_iff alternativeTarget).mpr haltNotOne
      rw [if_pos hzAlt, if_pos hzTarget, hview.2]
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixTwo : alternativeSource.observations2 = source.observations2 :=
      G.balancedCrossingLift_observations2_injective hhier _ _ hprefixLift
    have haltNotOne : ¬ G.OneDeterminesTwoAt alternativeTarget := by
      intro haltOne
      have htargetZero := (G.informationRankTwo_eq_zero_iff target).mpr htargetNotOne
      have haltNonzero : G.informationRankTwo alternativeTarget ≠ 0 := by
        intro hz
        exact ((G.informationRankTwo_eq_zero_iff _).mp hz) haltOne
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier,
        if_neg haltNonzero, if_pos htargetZero] at hlastBridge
      cases hlastBridge
    have haltTwo : G.TwoDeterminesOneAt alternativeTarget :=
      (hhier alternativeTarget).resolve_left haltNotOne
    have hzTarget := (G.informationRankTwo_eq_zero_iff target).mpr htargetNotOne
    have hzAlt := (G.informationRankTwo_eq_zero_iff alternativeTarget).mpr haltNotOne
    rw [G.balancedCrossingBridgeLift_observe2 hhier,
      G.balancedCrossingBridgeLift_observe2 hhier,
      if_pos hzAlt, if_pos hzTarget] at hlastBridge
    have hknowledge : G.knowledgeOneOfTwoAt alternativeTarget =
        G.knowledgeOneOfTwoAt target :=
      Sum.inr.inj (Sum.inr.inj hlastBridge)
    have hview := (G.balanced_bridge_view_equiv_one_to_two
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceOne haltTwo).mpr
      ⟨hprefixTwo, hknowledge⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations1_congr _ _ hview.1
    · change G.balancedCrossingEliminationGame.observe1
          (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.balancedCrossingEliminationGame.observe1
          (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1]
      have htargetNonzero : G.informationRankOne target ≠ 0 := by
        exact fun hz => htargetNotOne
          ((G.informationRankOne_eq_zero_iff _).mp hz)
      have haltNonzero : G.informationRankOne alternativeTarget ≠ 0 := by
        exact fun hz => haltNotOne
          ((G.informationRankOne_eq_zero_iff _).mp hz)
      rw [if_neg haltNonzero, if_neg htargetNonzero, hview.2]

/-- A strict one-to-two reversal reaches an actual information tie at the
balanced bridge. -/
theorem balancedBridge_tie_one_to_two
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.OneStrictlyMoreInformedAt source)
    (htarget : G.TwoStrictlyMoreInformedAt
      (source.step actionOne actionTwo nature)) :
    G.balancedCrossingEliminationGame.OneDeterminesTwoAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) ∧
      G.balancedCrossingEliminationGame.TwoDeterminesOneAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) := by
  let bridge := G.balancedCrossingBridgeLift source actionOne actionTwo nature
  have bridgeEquiv := G.balancedBridge_observations_equiv_one_to_two hhier
    source
  constructor
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.1.symm.trans heq)
          rw [PlayHistory.observations1_getLast?_last,
            PlayHistory.observations1_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalOne := hnormalOne.symm.trans heq
    have hcanonicalTwo :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mp
        hcanonicalOne
    exact hnormalTwo.trans hcanonicalTwo
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.2.symm.trans heq)
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalTwo := hnormalTwo.symm.trans heq
    have hcanonicalOne :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mpr
        hcanonicalTwo
    exact hnormalOne.trans hcanonicalOne

/-- Symmetric complete-view equivalence for a two-to-one reversal. -/
theorem balancedBridge_observations_equiv_two_to_one
    (hhier : G.DynamicHierarchy)
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsourceTwo : G.TwoDeterminesOneAt source)
    (htargetNotTwo : ¬ G.TwoDeterminesOneAt
      (source.step actionOne actionTwo nature)) :
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations2 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations2 ↔
    (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations1 =
      (G.balancedCrossingBridgeLift source actionOne actionTwo nature).observations1 := by
  let target := source.step actionOne actionTwo nature
  let alternativeTarget := alternativeSource.step alternativeActionOne
    alternativeActionTwo alternativeNature
  have htargetOne : G.OneDeterminesTwoAt target :=
    (hhier target).resolve_right htargetNotTwo
  constructor
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe2
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixTwo :=
      G.balancedCrossingLift_observations2_injective hhier _ _ hprefixLift
    have haltOne : G.OneDeterminesTwoAt alternativeTarget := by
      by_contra hnot
      have hzAlt := (G.informationRankTwo_eq_zero_iff _).mpr hnot
      have hnonzeroTarget : G.informationRankTwo target ≠ 0 := by
        intro hz
        exact htargetNotTwo ((hhier target).resolve_left
          ((G.informationRankTwo_eq_zero_iff _).mp hz))
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier,
        if_pos hzAlt, if_neg hnonzeroTarget] at hlastBridge
      cases hlastBridge
    have hnonzeroTarget : G.informationRankTwo target ≠ 0 := by
      intro hz
      exact htargetNotTwo ((hhier target).resolve_left
        ((G.informationRankTwo_eq_zero_iff _).mp hz))
    have hnonzeroAlt : G.informationRankTwo alternativeTarget ≠ 0 := by
      intro hz
      exact ((G.informationRankTwo_eq_zero_iff _).mp hz) haltOne
    rw [G.balancedCrossingBridgeLift_observe2 hhier,
      G.balancedCrossingBridgeLift_observe2 hhier,
      if_neg hnonzeroAlt, if_neg hnonzeroTarget] at hlastBridge
    have hlastTwo : G.observe2 alternativeTarget.lastState =
        G.observe2 target.lastState :=
      Sum.inl.inj (Sum.inr.inj hlastBridge)
    have hview := (G.balanced_bridge_view_equiv_two_to_one
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceTwo haltOne).mp
      ⟨hprefixTwo, hlastTwo⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations1_congr _ _ hview.1
    · change G.balancedCrossingEliminationGame.observe1
          (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.balancedCrossingEliminationGame.observe1
          (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1]
      have hzTarget := (G.informationRankOne_eq_zero_iff target).mpr htargetOne
      have hzAlt := (G.informationRankOne_eq_zero_iff alternativeTarget).mpr haltOne
      rw [if_pos hzAlt, if_pos hzTarget, hview.2]
  · intro hobs
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step] at hobs
    obtain ⟨hprefixLift, hlastBridgeList⟩ := List.append_inj' hobs (by simp)
    have hlastBridge := List.singleton_inj.mp hlastBridgeList
    change G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.balancedCrossingEliminationGame.observe1
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      at hlastBridge
    have hprefixOne :=
      G.balancedCrossingLift_observations1_injective _ _ hprefixLift
    have haltOne : G.OneDeterminesTwoAt alternativeTarget := by
      by_contra hnot
      have hnonzeroAlt : G.informationRankOne alternativeTarget ≠ 0 :=
        fun hz => hnot ((G.informationRankOne_eq_zero_iff _).mp hz)
      have hzTarget := (G.informationRankOne_eq_zero_iff target).mpr htargetOne
      rw [G.balancedCrossingBridgeLift_observe1,
        G.balancedCrossingBridgeLift_observe1,
        if_neg hnonzeroAlt, if_pos hzTarget] at hlastBridge
      cases hlastBridge
    have hzTarget := (G.informationRankOne_eq_zero_iff target).mpr htargetOne
    have hzAlt := (G.informationRankOne_eq_zero_iff alternativeTarget).mpr haltOne
    rw [G.balancedCrossingBridgeLift_observe1,
      G.balancedCrossingBridgeLift_observe1,
      if_pos hzAlt, if_pos hzTarget] at hlastBridge
    have hknowledge : G.knowledgeTwoOfOneAt alternativeTarget =
        G.knowledgeTwoOfOneAt target :=
      Sum.inr.inj (Sum.inr.inj hlastBridge)
    have hview := (G.balanced_bridge_view_equiv_two_to_one
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceTwo haltOne).mpr
      ⟨hprefixOne, hknowledge⟩
    rw [balancedCrossingBridgeLift, balancedCrossingBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step]
    apply congrArg₂ (fun xs last => xs ++ [last])
    · exact G.balancedCrossingLift_observations2_congr hhier _ _ hview.1
    · change G.balancedCrossingEliminationGame.observe2
          (G.balancedCrossingBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.balancedCrossingEliminationGame.observe2
          (G.balancedCrossingBridgeLift source actionOne actionTwo nature).lastState
      rw [G.balancedCrossingBridgeLift_observe2 hhier,
        G.balancedCrossingBridgeLift_observe2 hhier]
      have hnonzeroTarget : G.informationRankTwo target ≠ 0 := by
        intro hz
        exact htargetNotTwo ((hhier target).resolve_left
          ((G.informationRankTwo_eq_zero_iff _).mp hz))
      have hnonzeroAlt : G.informationRankTwo alternativeTarget ≠ 0 := by
        intro hz
        exact ((G.informationRankTwo_eq_zero_iff _).mp hz) haltOne
      rw [if_neg hnonzeroAlt, if_neg hnonzeroTarget, hview.2]

theorem balancedBridge_tie_two_to_one
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.TwoStrictlyMoreInformedAt source)
    (htarget : G.OneStrictlyMoreInformedAt
      (source.step actionOne actionTwo nature)) :
    G.balancedCrossingEliminationGame.OneDeterminesTwoAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) ∧
      G.balancedCrossingEliminationGame.TwoDeterminesOneAt
        (G.balancedCrossingBridgeLift source actionOne actionTwo nature) := by
  let bridge := G.balancedCrossingBridgeLift source actionOne actionTwo nature
  have bridgeEquiv := G.balancedBridge_observations_equiv_two_to_one hhier
    source
  constructor
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.1.symm.trans heq)
          rw [PlayHistory.observations1_getLast?_last,
            PlayHistory.observations1_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalOne := hnormalOne.symm.trans heq
    have hcanonicalTwo :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mpr
        hcanonicalOne
    exact hnormalTwo.trans hcanonicalTwo
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_balancedCrossingRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.balancedCrossingRep_observation_normal rep
          simp only [BalancedCrossingObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.2.symm.trans heq)
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.balancedCrossingLift_lastState,
            G.balancedCrossingBridgeLift_lastState] at hlast
          simp [balancedCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.balancedCrossingRep_observation_normal rep
    simp only [BalancedCrossingObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalTwo := hnormalTwo.symm.trans heq
    have hcanonicalOne :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget.2).mp
        hcanonicalTwo
    exact hnormalOne.trans hcanonicalOne

end FiniteConcurrentGame

end DistributedSynthesis
