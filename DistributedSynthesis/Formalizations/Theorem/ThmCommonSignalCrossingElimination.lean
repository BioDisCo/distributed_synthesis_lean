/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBalancedCrossingElimination

/-!
# Crossing elimination with a common bridge signal

The knowledge-set-only bridge is sufficient at a strict reversal, but it need
not preserve the information order on a move whose direction does not change:
two different information classes can have the same set of current possible
observations.  The bridge below records the missing discriminator as well.

At a target where player one is at least as informed, both players receive
`(knowledgeTwoOfOneAt target, observe2 target.lastState)`.  Otherwise both
receive the mirror pair.  This is a common signal computable from either
player's complete target view.  Since the bridge has no effective choice, its
early delivery does not add a strategic decision point.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

/-- The common bridge letter.  The left summand is used when player two is
strictly more informed; the right summand when player one is at least as
informed. -/
abbrev CommonBridgeSignal :=
  Sum (G.Observation1 × Finset G.Observation2)
    (Finset G.Observation1 × G.Observation2)

noncomputable def commonBridgeSignalAt (history : G.PlayHistory) :
    G.CommonBridgeSignal :=
  if G.informationRankOne history = 0 then
    Sum.inr (G.knowledgeTwoOfOneAt history, G.observe2 history.lastState)
  else
    Sum.inl (G.observe1 history.lastState, G.knowledgeOneOfTwoAt history)

/-- The doubled arena with the same bridge letter for both players. -/
noncomputable def commonSignalCrossingEliminationGame :
    FiniteConcurrentGame where
  State := G.CrossingState
  Action1 := G.Action1
  Action2 := G.Action2
  Nature := G.Nature
  Observation1 := Sum (G.Observation1 × Fin 2) G.CommonBridgeSignal
  Observation2 := Sum (G.Observation2 × Fin 2) G.CommonBridgeSignal
  stateFinite := by infer_instance
  action1Finite := G.action1Finite
  action2Finite := G.action2Finite
  natureFinite := G.natureFinite
  observation1Finite := by classical infer_instance
  observation2Finite := by classical infer_instance
  initial := G.crossingEliminationGame.initial
  next := G.crossingEliminationGame.next
  observe1 state :=
    if state.1 then
      Sum.inr <|
        if G.rankOneMachine.output state.2.2.1 = 0 then
          Sum.inr
            (G.knowledgeTwoOfOneMachine.output state.2.2.2,
              G.observe2 state.2.1)
        else
          Sum.inl
            (G.observe1 state.2.1,
              G.knowledgeOneOfTwoMachine.output state.2.2.1)
    else
      Sum.inl
        (G.observe1 state.2.1, G.rankOneMachine.output state.2.2.1)
  observe2 state :=
    if state.1 then
      Sum.inr <|
        if G.rankOneMachine.output state.2.2.1 = 0 then
          Sum.inr
            (G.knowledgeTwoOfOneMachine.output state.2.2.2,
              G.observe2 state.2.1)
        else
          Sum.inl
            (G.observe1 state.2.1,
              G.knowledgeOneOfTwoMachine.output state.2.2.1)
    else
      Sum.inl
        (G.observe2 state.2.1, G.rankTwoMachine.output state.2.2.2)
  priority state := G.priority state.2.1

noncomputable def commonSignalLift :
    G.PlayHistory -> G.commonSignalCrossingEliminationGame.PlayHistory
  | .initial => .initial
  | .step previous actionOne actionTwo nature =>
      ((commonSignalLift previous).step actionOne actionTwo nature).step
        actionOne actionTwo nature

noncomputable def commonSignalBridgeLift
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.commonSignalCrossingEliminationGame.PlayHistory :=
  (G.commonSignalLift history).step actionOne actionTwo nature

theorem commonSignalLift_lastState (history : G.PlayHistory) :
    (G.commonSignalLift history).lastState =
      (false, history.lastState,
        G.rankOneMachine.run history.observations1,
        G.rankTwoMachine.run history.observations2) := by
  induction history with
  | initial =>
      simp [commonSignalLift, commonSignalCrossingEliminationGame,
        crossingEliminationGame, MooreController.run, rankOneMachine,
        rankTwoMachine, PlayHistory.lastState, initialRankTwoBelief]
  | step previous actionOne actionTwo nature ih =>
      rw [commonSignalLift]
      change G.commonSignalCrossingEliminationGame.next
        (G.commonSignalCrossingEliminationGame.next
          (G.commonSignalLift previous).lastState
          actionOne actionTwo nature) actionOne actionTwo nature = _
      rw [ih]
      simp [commonSignalCrossingEliminationGame, crossingEliminationGame,
        crossingAdvance, PlayHistory.lastState,
        PlayHistory.observations1_step, PlayHistory.observations2_step]

theorem commonSignalBridgeLift_lastState
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    (G.commonSignalBridgeLift history actionOne actionTwo nature).lastState =
      (true, (history.step actionOne actionTwo nature).lastState,
        G.rankOneMachine.run
          (history.step actionOne actionTwo nature).observations1,
        G.rankTwoMachine.run
          (history.step actionOne actionTwo nature).observations2) := by
  unfold commonSignalBridgeLift
  change G.commonSignalCrossingEliminationGame.next
    (G.commonSignalLift history).lastState actionOne actionTwo nature = _
  rw [G.commonSignalLift_lastState]
  simp [commonSignalCrossingEliminationGame, crossingEliminationGame,
    crossingAdvance, PlayHistory.lastState,
    PlayHistory.observations1_step, PlayHistory.observations2_step]

theorem commonSignalBridgeLift_observe1
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalBridgeLift history actionOne actionTwo nature).lastState =
      Sum.inr (G.commonBridgeSignalAt
        (history.step actionOne actionTwo nature)) := by
  rw [G.commonSignalBridgeLift_lastState]
  simp only [commonSignalCrossingEliminationGame, if_true]
  rw [G.rankOneMachine_output_run]
  have htwo := G.knowledgeTwoOfOneMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeTwoOfOneMachine_run] at htwo
  have hone := G.knowledgeOneOfTwoMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeOneOfTwoMachine_run] at hone
  rw [htwo, hone]
  rfl

theorem commonSignalBridgeLift_observe2
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalBridgeLift history actionOne actionTwo nature).lastState =
      Sum.inr (G.commonBridgeSignalAt
        (history.step actionOne actionTwo nature)) := by
  rw [G.commonSignalBridgeLift_lastState]
  simp only [commonSignalCrossingEliminationGame, if_true]
  rw [G.rankOneMachine_output_run]
  have htwo := G.knowledgeTwoOfOneMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeTwoOfOneMachine_run] at htwo
  have hone := G.knowledgeOneOfTwoMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeOneOfTwoMachine_run] at hone
  rw [htwo, hone]
  rfl

theorem commonSignalLift_observe1 (history : G.PlayHistory) :
    G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalLift history).lastState =
      Sum.inl (G.observe1 history.lastState,
        G.informationRankOne history) := by
  rw [G.commonSignalLift_lastState]
  simp [commonSignalCrossingEliminationGame,
    G.rankOneMachine_output_run]

theorem commonSignalLift_observe2
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalLift history).lastState =
      Sum.inl (G.observe2 history.lastState,
        G.informationRankTwo history) := by
  rw [G.commonSignalLift_lastState]
  simp [commonSignalCrossingEliminationGame,
    G.rankTwoMachine_output_run hhier]

/-- The common signal is a function of player one's complete target view. -/
theorem commonBridgeSignalAt_congr_observations1
    (history alternative : G.PlayHistory)
    (heq : history.observations1 = alternative.observations1) :
    G.commonBridgeSignalAt history = G.commonBridgeSignalAt alternative := by
  classical
  have hrank := G.informationRankOne_consistent history alternative heq
  unfold commonBridgeSignalAt
  by_cases hz : G.informationRankOne history = 0
  · have hzAlt : G.informationRankOne alternative = 0 := by rwa [← hrank]
    rw [if_pos hz, if_pos hzAlt]
    apply congrArg Sum.inr
    apply Prod.ext
    · exact G.knowledgeTwoOfOneAt_consistent_to_one history alternative
        ((G.informationRankOne_eq_zero_iff history).mp hz) heq
    · have htwo := (G.informationRankOne_eq_zero_iff history).mp hz
          alternative heq.symm
      have hlast := congrArg List.getLast? htwo.symm
      rw [PlayHistory.observations2_getLast?_last,
        PlayHistory.observations2_getLast?_last] at hlast
      exact Option.some.inj hlast
  · have hzAlt : G.informationRankOne alternative ≠ 0 := by rwa [← hrank]
    rw [if_neg hz, if_neg hzAlt]
    apply congrArg Sum.inl
    apply Prod.ext
    · have hlast := congrArg List.getLast? heq
      rw [PlayHistory.observations1_getLast?_last,
        PlayHistory.observations1_getLast?_last] at hlast
      exact Option.some.inj hlast
    · exact G.knowledgeOneOfTwoAt_congr_observations1 history alternative heq

/-- Under hierarchy, the common signal is also a function of player two's
complete target view. -/
theorem commonBridgeSignalAt_congr_observations2
    (hhier : G.DynamicHierarchy) (history alternative : G.PlayHistory)
    (heq : history.observations2 = alternative.observations2) :
    G.commonBridgeSignalAt history = G.commonBridgeSignalAt alternative := by
  classical
  have hrank := G.informationRankTwo_consistent hhier history alternative heq
  have hbranch : (G.informationRankOne history = 0) =
      (G.informationRankOne alternative = 0) := by
    apply propext
    rw [G.informationRankOne_eq_zero_iff,
      G.informationRankOne_eq_zero_iff]
    constructor
    · intro hone
      by_contra hnot
      have htwo := (hhier alternative).resolve_left hnot
      have honeAlt : G.OneDeterminesTwoAt alternative := by
        intro third hthird
        have hsourceOne := htwo history heq
        have hthirdHistory : third.observations1 = history.observations1 :=
          hthird.trans hsourceOne.symm
        exact (hone third hthirdHistory).trans heq
      exact hnot honeAlt
    · intro hone
      by_contra hnot
      have htwo := (hhier history).resolve_left hnot
      have honeHistory : G.OneDeterminesTwoAt history := by
        intro third hthird
        have hsourceOne := htwo alternative heq.symm
        have hthirdAlt : third.observations1 = alternative.observations1 :=
          hthird.trans hsourceOne.symm
        exact (hone third hthirdAlt).trans heq.symm
      exact hnot honeHistory
  unfold commonBridgeSignalAt
  by_cases hz : G.informationRankOne history = 0
  · have hzAlt : G.informationRankOne alternative = 0 := by
      rwa [← hbranch]
    rw [if_pos hz, if_pos hzAlt]
    apply congrArg Sum.inr
    apply Prod.ext
    · exact G.knowledgeTwoOfOneAt_congr_observations2 history alternative heq
    · have hlast := congrArg List.getLast? heq
      rw [PlayHistory.observations2_getLast?_last,
        PlayHistory.observations2_getLast?_last] at hlast
      exact Option.some.inj hlast
  · have hzAlt : G.informationRankOne alternative ≠ 0 := by
      intro hzero
      exact hz (hbranch.mpr hzero)
    rw [if_neg hz, if_neg hzAlt]
    apply congrArg Sum.inl
    apply Prod.ext
    · have hnotOne : ¬ G.OneDeterminesTwoAt history := fun hone => hz
          ((G.informationRankOne_eq_zero_iff history).mpr hone)
      have htwo := (hhier history).resolve_left hnotOne
      have hone := htwo alternative heq.symm
      have hlast := congrArg List.getLast? hone.symm
      rw [PlayHistory.observations1_getLast?_last,
        PlayHistory.observations1_getLast?_last] at hlast
      exact Option.some.inj hlast
    · have hnotOne : ¬ G.OneDeterminesTwoAt history := fun hone => hz
          ((G.informationRankOne_eq_zero_iff history).mpr hone)
      exact G.knowledgeOneOfTwoAt_consistent_to_two history alternative
        ((hhier history).resolve_left hnotOne) heq

theorem commonSignalLift_observations1_congr
    (left right : G.PlayHistory)
    (heq : left.observations1 = right.observations1) :
    (G.commonSignalLift left).observations1 =
      (G.commonSignalLift right).observations1 := by
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
          simp only [PlayHistory.observations1_step,
            PlayHistory.observations1_initial, List.length_append,
            List.length_singleton] at hlen
          have hpos := G.observations1_length_pos left
          omega
      | step right rightActionOne rightActionTwo rightNature =>
          rw [PlayHistory.observations1_step,
            PlayHistory.observations1_step] at heq
          obtain ⟨hprefix, _⟩ := List.append_inj' heq (by simp)
          have ih' := ih right hprefix
          have htarget :
              (left.step actionOne actionTwo nature).observations1 =
                (right.step rightActionOne rightActionTwo rightNature).observations1 :=
            by simpa only [PlayHistory.observations1_step] using heq
          have hsignal := G.commonBridgeSignalAt_congr_observations1
            (left.step actionOne actionTwo nature)
            (right.step rightActionOne rightActionTwo rightNature) htarget
          have hrank := G.informationRankOne_consistent
            (left.step actionOne actionTwo nature)
            (right.step rightActionOne rightActionTwo rightNature) htarget
          have hbridgeObs :
              G.commonSignalCrossingEliminationGame.observe1
                  (G.commonSignalBridgeLift left actionOne actionTwo nature).lastState =
                G.commonSignalCrossingEliminationGame.observe1
                  (G.commonSignalBridgeLift right rightActionOne
                    rightActionTwo rightNature).lastState := by
            rw [G.commonSignalBridgeLift_observe1,
              G.commonSignalBridgeLift_observe1, hsignal]
          have horiginalObs :
              G.commonSignalCrossingEliminationGame.observe1
                  (G.commonSignalLift
                    (left.step actionOne actionTwo nature)).lastState =
                G.commonSignalCrossingEliminationGame.observe1
                  (G.commonSignalLift
                    (right.step rightActionOne rightActionTwo rightNature)).lastState := by
            rw [G.commonSignalLift_observe1, G.commonSignalLift_observe1]
            have hlast := congrArg List.getLast? htarget
            rw [PlayHistory.observations1_getLast?_last,
              PlayHistory.observations1_getLast?_last] at hlast
            rw [Option.some.inj hlast, hrank]
          rw [commonSignalLift, commonSignalLift,
            PlayHistory.observations1_step, PlayHistory.observations1_step,
            PlayHistory.observations1_step, PlayHistory.observations1_step,
            ih']
          change (G.commonSignalLift right).observations1 ++
              [G.commonSignalCrossingEliminationGame.observe1
                (G.commonSignalBridgeLift left actionOne actionTwo nature).lastState] ++
              [G.commonSignalCrossingEliminationGame.observe1
                (G.commonSignalLift
                  (left.step actionOne actionTwo nature)).lastState] = _
          rw [hbridgeObs, horiginalObs]
          rfl

theorem commonSignalLift_observations2_congr
    (hhier : G.DynamicHierarchy) (left right : G.PlayHistory)
    (heq : left.observations2 = right.observations2) :
    (G.commonSignalLift left).observations2 =
      (G.commonSignalLift right).observations2 := by
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
          simp only [PlayHistory.observations2_step,
            PlayHistory.observations2_initial, List.length_append,
            List.length_singleton] at hlen
          have hpos := G.observations1_length_pos left
          rw [G.observations_length_eq left] at hpos
          omega
      | step right rightActionOne rightActionTwo rightNature =>
          rw [PlayHistory.observations2_step,
            PlayHistory.observations2_step] at heq
          obtain ⟨hprefix, _⟩ := List.append_inj' heq (by simp)
          have ih' := ih right hprefix
          have htarget :
              (left.step actionOne actionTwo nature).observations2 =
                (right.step rightActionOne rightActionTwo rightNature).observations2 :=
            by simpa only [PlayHistory.observations2_step] using heq
          have hsignal := G.commonBridgeSignalAt_congr_observations2 hhier
            (left.step actionOne actionTwo nature)
            (right.step rightActionOne rightActionTwo rightNature) htarget
          have hrank := G.informationRankTwo_consistent hhier
            (left.step actionOne actionTwo nature)
            (right.step rightActionOne rightActionTwo rightNature) htarget
          have hbridgeObs :
              G.commonSignalCrossingEliminationGame.observe2
                  (G.commonSignalBridgeLift left actionOne actionTwo nature).lastState =
                G.commonSignalCrossingEliminationGame.observe2
                  (G.commonSignalBridgeLift right rightActionOne
                    rightActionTwo rightNature).lastState := by
            rw [G.commonSignalBridgeLift_observe2,
              G.commonSignalBridgeLift_observe2, hsignal]
          have horiginalObs :
              G.commonSignalCrossingEliminationGame.observe2
                  (G.commonSignalLift
                    (left.step actionOne actionTwo nature)).lastState =
                G.commonSignalCrossingEliminationGame.observe2
                  (G.commonSignalLift
                    (right.step rightActionOne rightActionTwo rightNature)).lastState := by
            rw [G.commonSignalLift_observe2 hhier,
              G.commonSignalLift_observe2 hhier]
            have hlast := congrArg List.getLast? htarget
            rw [PlayHistory.observations2_getLast?_last,
              PlayHistory.observations2_getLast?_last] at hlast
            rw [Option.some.inj hlast, hrank]
          rw [commonSignalLift, commonSignalLift,
            PlayHistory.observations2_step, PlayHistory.observations2_step,
            PlayHistory.observations2_step, PlayHistory.observations2_step,
            ih']
          change (G.commonSignalLift right).observations2 ++
              [G.commonSignalCrossingEliminationGame.observe2
                (G.commonSignalBridgeLift left actionOne actionTwo nature).lastState] ++
              [G.commonSignalCrossingEliminationGame.observe2
                (G.commonSignalLift
                  (left.step actionOne actionTwo nature)).lastState] = _
          rw [hbridgeObs, horiginalObs]
          rfl

def projectCommonObservationOne :
    G.commonSignalCrossingEliminationGame.Observation1 → Option G.Observation1
  | Sum.inl original => some original.1
  | Sum.inr _ => none

def projectCommonObservationTwo :
    G.commonSignalCrossingEliminationGame.Observation2 → Option G.Observation2
  | Sum.inl original => some original.1
  | Sum.inr _ => none

theorem project_commonSignalLift_observations1 (history : G.PlayHistory) :
    (G.commonSignalLift history).observations1.filterMap
        G.projectCommonObservationOne = history.observations1 := by
  induction history with
  | initial =>
      simp [commonSignalLift, commonSignalCrossingEliminationGame,
        crossingEliminationGame, projectCommonObservationOne]
  | step previous actionOne actionTwo nature ih =>
      rw [commonSignalLift, PlayHistory.observations1_step,
        PlayHistory.observations1_step, List.filterMap_append,
        List.filterMap_append, ih]
      change previous.observations1 ++
          List.filterMap G.projectCommonObservationOne
            [G.commonSignalCrossingEliminationGame.observe1
              (G.commonSignalBridgeLift previous actionOne actionTwo nature).lastState] ++
          List.filterMap G.projectCommonObservationOne
            [G.commonSignalCrossingEliminationGame.observe1
              (G.commonSignalLift
                (previous.step actionOne actionTwo nature)).lastState] = _
      rw [G.commonSignalBridgeLift_observe1, G.commonSignalLift_observe1]
      simp [projectCommonObservationOne, PlayHistory.lastState]

theorem project_commonSignalLift_observations2
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    (G.commonSignalLift history).observations2.filterMap
        G.projectCommonObservationTwo = history.observations2 := by
  induction history with
  | initial =>
      simp [commonSignalLift, commonSignalCrossingEliminationGame,
        crossingEliminationGame, projectCommonObservationTwo]
  | step previous actionOne actionTwo nature ih =>
      rw [commonSignalLift, PlayHistory.observations2_step,
        PlayHistory.observations2_step, List.filterMap_append,
        List.filterMap_append, ih]
      change previous.observations2 ++
          List.filterMap G.projectCommonObservationTwo
            [G.commonSignalCrossingEliminationGame.observe2
              (G.commonSignalBridgeLift previous actionOne actionTwo nature).lastState] ++
          List.filterMap G.projectCommonObservationTwo
            [G.commonSignalCrossingEliminationGame.observe2
              (G.commonSignalLift
                (previous.step actionOne actionTwo nature)).lastState] = _
      rw [G.commonSignalBridgeLift_observe2,
        G.commonSignalLift_observe2 hhier]
      simp [projectCommonObservationTwo, PlayHistory.lastState]

theorem commonSignalLift_observations1_injective
    (left right : G.PlayHistory)
    (heq : (G.commonSignalLift left).observations1 =
      (G.commonSignalLift right).observations1) :
    left.observations1 = right.observations1 := by
  have h := congrArg (List.filterMap G.projectCommonObservationOne) heq
  simpa [G.project_commonSignalLift_observations1] using h

theorem commonSignalLift_observations2_injective
    (hhier : G.DynamicHierarchy) (left right : G.PlayHistory)
    (heq : (G.commonSignalLift left).observations2 =
      (G.commonSignalLift right).observations2) :
    left.observations2 = right.observations2 := by
  have h := congrArg (List.filterMap G.projectCommonObservationTwo) heq
  simpa [G.project_commonSignalLift_observations2 hhier] using h

/-! ### Arbitrary-history normalization for the common-signal arena

Every doubled history is, up to a Boolean phase, the lift of a unique original
history; on the `false` phase it is the plain lift, and on the `true` phase it
is the bridge lift of the original's one-step predecessor.  This is the
common-signal mirror of `BalancedCrossingRep`, and it is what lets an
arbitrary alternative be replaced by a normal-form representative in the
determination transfer below. -/

inductive CommonSignalRep :
    G.commonSignalCrossingEliminationGame.PlayHistory -> Bool ->
      G.PlayHistory -> Prop
  | initial : CommonSignalRep PlayHistory.initial false PlayHistory.initial
  | toBridge {doubled : G.commonSignalCrossingEliminationGame.PlayHistory}
      {history : G.PlayHistory}
      (rep : CommonSignalRep doubled false history)
      (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
      CommonSignalRep (doubled.step actionOne actionTwo nature) true
        (history.step actionOne actionTwo nature)
  | toOriginal {doubled : G.commonSignalCrossingEliminationGame.PlayHistory}
      {history : G.PlayHistory}
      (rep : CommonSignalRep doubled true history)
      (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
      CommonSignalRep (doubled.step actionOne actionTwo nature) false history

theorem commonSignalRep_lastState
    {doubled : G.commonSignalCrossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (rep : G.CommonSignalRep doubled phase history) :
    doubled.lastState =
      (phase, history.lastState,
        G.rankOneMachine.run history.observations1,
        G.rankTwoMachine.run history.observations2) := by
  induction rep with
  | initial =>
      simp [commonSignalCrossingEliminationGame, crossingEliminationGame,
        MooreController.run, rankOneMachine, rankTwoMachine,
        PlayHistory.lastState, initialRankTwoBelief]
  | toBridge rep actionOne actionTwo nature ih =>
      change G.commonSignalCrossingEliminationGame.next _ actionOne actionTwo nature = _
      rw [ih]
      simp [commonSignalCrossingEliminationGame, crossingEliminationGame,
        crossingAdvance, PlayHistory.lastState,
        PlayHistory.observations1_step, PlayHistory.observations2_step]
  | toOriginal rep actionOne actionTwo nature ih =>
      change G.commonSignalCrossingEliminationGame.next _ actionOne actionTwo nature = _
      rw [ih]
      simp [commonSignalCrossingEliminationGame, crossingEliminationGame]

theorem exists_commonSignalRep
    (doubled : G.commonSignalCrossingEliminationGame.PlayHistory) :
    ∃ (phase : Bool) (history : G.PlayHistory),
      G.CommonSignalRep doubled phase history := by
  induction doubled with
  | initial => exact ⟨false, PlayHistory.initial, CommonSignalRep.initial⟩
  | step previous actionOne actionTwo nature ih =>
      obtain ⟨phase, history, rep⟩ := ih
      cases phase with
      | false => exact ⟨true, history.step actionOne actionTwo nature,
          CommonSignalRep.toBridge rep actionOne actionTwo nature⟩
      | true => exact ⟨false, history,
          CommonSignalRep.toOriginal rep actionOne actionTwo nature⟩

def CommonSignalObservationNormal
    {doubled : G.commonSignalCrossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (_rep : G.CommonSignalRep doubled phase history) : Prop :=
  if phase then
    ∃ (previous : G.PlayHistory) (actionOne : G.Action1)
      (actionTwo : G.Action2) (nature : G.Nature),
      history = previous.step actionOne actionTwo nature ∧
        doubled.observations1 =
          (G.commonSignalBridgeLift previous actionOne actionTwo nature).observations1 ∧
        doubled.observations2 =
          (G.commonSignalBridgeLift previous actionOne actionTwo nature).observations2
  else
    doubled.observations1 =
        (G.commonSignalLift history).observations1 ∧
      doubled.observations2 =
        (G.commonSignalLift history).observations2

theorem commonSignalRep_observation_normal
    {doubled : G.commonSignalCrossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (rep : G.CommonSignalRep doubled phase history) :
    G.CommonSignalObservationNormal rep := by
  induction rep with
  | initial =>
      simp [CommonSignalObservationNormal, commonSignalLift]
  | toBridge rep actionOne actionTwo nature ih =>
      simp only [CommonSignalObservationNormal, if_true]
      simp only [CommonSignalObservationNormal, Bool.false_eq_true,
        if_false] at ih
      refine ⟨_, actionOne, actionTwo, nature, rfl, ?_, ?_⟩
      · rw [PlayHistory.observations1_step, ih.1]
        rw [commonSignalBridgeLift, PlayHistory.observations1_step]
        congr 1
        rw [G.commonSignalRep_lastState rep,
          G.commonSignalLift_lastState]
      · rw [PlayHistory.observations2_step, ih.2]
        rw [commonSignalBridgeLift, PlayHistory.observations2_step]
        congr 1
        rw [G.commonSignalRep_lastState rep,
          G.commonSignalLift_lastState]
  | toOriginal rep actionOne actionTwo nature ih =>
      simp only [CommonSignalObservationNormal, if_true] at ih
      simp only [CommonSignalObservationNormal, Bool.false_eq_true,
        if_false]
      obtain ⟨previous, originalOne, originalTwo, originalNature,
        hhistory, hobsOne, hobsTwo⟩ := ih
      constructor
      · rw [PlayHistory.observations1_step, hobsOne]
        rw [hhistory, commonSignalLift, PlayHistory.observations1_step,
          PlayHistory.observations1_step]
        rw [commonSignalBridgeLift, PlayHistory.observations1_step]
        congr 2
        rw [G.commonSignalRep_lastState rep]
        change _ = G.commonSignalCrossingEliminationGame.observe1
          (G.commonSignalCrossingEliminationGame.next
            (G.commonSignalBridgeLift previous originalOne originalTwo
              originalNature).lastState originalOne originalTwo originalNature)
        rw [G.commonSignalBridgeLift_lastState, hhistory]
        simp [commonSignalCrossingEliminationGame, crossingEliminationGame]
      · rw [PlayHistory.observations2_step, hobsTwo]
        rw [hhistory, commonSignalLift, PlayHistory.observations2_step,
          PlayHistory.observations2_step]
        rw [commonSignalBridgeLift, PlayHistory.observations2_step]
        congr 2
        rw [G.commonSignalRep_lastState rep]
        change _ = G.commonSignalCrossingEliminationGame.observe2
          (G.commonSignalCrossingEliminationGame.next
            (G.commonSignalBridgeLift previous originalOne originalTwo
              originalNature).lastState originalOne originalTwo originalNature)
        rw [G.commonSignalBridgeLift_lastState, hhistory]
        simp [commonSignalCrossingEliminationGame, crossingEliminationGame]

theorem commonSignalRep_phase_false_of_observations1_eq
    {alternative : G.commonSignalCrossingEliminationGame.PlayHistory}
    {phase : Bool} {represented history : G.PlayHistory}
    (rep : G.CommonSignalRep alternative phase represented)
    (heq : alternative.observations1 =
      (G.commonSignalLift history).observations1) : phase = false := by
  cases phase with
  | false => rfl
  | true =>
      exfalso
      have hlastGet := congrArg List.getLast? heq
      rw [PlayHistory.observations1_getLast?_last,
        PlayHistory.observations1_getLast?_last] at hlastGet
      have hlast := Option.some.inj hlastGet
      rw [G.commonSignalRep_lastState rep,
        G.commonSignalLift_lastState] at hlast
      simp [commonSignalCrossingEliminationGame] at hlast

theorem commonSignalRep_phase_false_of_observations2_eq
    {alternative : G.commonSignalCrossingEliminationGame.PlayHistory}
    {phase : Bool} {represented history : G.PlayHistory}
    (rep : G.CommonSignalRep alternative phase represented)
    (heq : alternative.observations2 =
      (G.commonSignalLift history).observations2) : phase = false := by
  cases phase with
  | false => rfl
  | true =>
      exfalso
      have hlast := congrArg List.getLast? heq
      have hcurrent :
          G.commonSignalCrossingEliminationGame.observe2 alternative.lastState =
            G.commonSignalCrossingEliminationGame.observe2
              (G.commonSignalLift history).lastState := by
        have ha := PlayHistory.observations2_getLast?_last alternative
        have hb := PlayHistory.observations2_getLast?_last
          (G.commonSignalLift history)
        rw [ha, hb] at hlast
        exact Option.some.inj hlast
      rw [G.commonSignalRep_lastState rep,
        G.commonSignalLift_lastState] at hcurrent
      simp [commonSignalCrossingEliminationGame] at hcurrent

/-! ### Determination transfer at lifted original positions

At the lift of an original history, each player's determination in the
common-signal arena is exactly its determination in the base game.  The
normalization above supplies the representative for the reverse direction. -/

theorem commonSignalLift_oneDeterminesTwoAt_iff
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
        (G.commonSignalLift history) ↔
      G.OneDeterminesTwoAt history := by
  constructor
  · intro hdet alternative heq
    have hliftOne := G.commonSignalLift_observations1_congr
      alternative history heq
    have hliftTwo := hdet (G.commonSignalLift alternative) hliftOne
    exact G.commonSignalLift_observations2_injective hhier _ _ hliftTwo
  · intro hdet alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
    have hphase := G.commonSignalRep_phase_false_of_observations1_eq
      rep heq
    subst phase
    have hnormal := G.commonSignalRep_observation_normal rep
    simp only [CommonSignalObservationNormal, Bool.false_eq_true,
      if_false] at hnormal
    have hrepresentedOne : represented.observations1 = history.observations1 :=
      G.commonSignalLift_observations1_injective represented history
        (hnormal.1.symm.trans heq)
    have hrepresentedTwo := hdet represented hrepresentedOne
    exact hnormal.2.trans
      (G.commonSignalLift_observations2_congr hhier represented history
        hrepresentedTwo)

theorem commonSignalLift_twoDeterminesOneAt_iff
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
        (G.commonSignalLift history) ↔
      G.TwoDeterminesOneAt history := by
  constructor
  · intro hdet alternative heq
    have hliftTwo := G.commonSignalLift_observations2_congr
      hhier alternative history heq
    have hliftOne := hdet (G.commonSignalLift alternative) hliftTwo
    exact G.commonSignalLift_observations1_injective _ _ hliftOne
  · intro hdet alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
    have hphase := G.commonSignalRep_phase_false_of_observations2_eq
      rep heq
    subst phase
    have hnormal := G.commonSignalRep_observation_normal rep
    simp only [CommonSignalObservationNormal, Bool.false_eq_true,
      if_false] at hnormal
    have hrepresentedTwo : represented.observations2 = history.observations2 :=
      G.commonSignalLift_observations2_injective hhier represented history
        (hnormal.2.symm.trans heq)
    have hrepresentedOne := hdet represented hrepresentedTwo
    exact hnormal.1.trans
      (G.commonSignalLift_observations1_congr represented history
        hrepresentedOne)

/-! ### Source-order preservation at bridges

The common bridge letter is delivered identically to both players
(`commonSignalBridgeLift_observe1/2`), so at a genuine reversal the two lifted
observation histories induce the same equivalence: matching one player's
complete bridge view is the same constraint as matching the other's.  This is
the common-signal strengthening of `balancedBridge_observations_equiv_*`, and
it collapses the per-player letter analysis of the balanced arena.  From it the
bridge is a full information tie at a reversal, which is what excludes a strict
order reversal across the doubled step. -/

theorem commonBridgeSignalAt_eq_inl_of_rankOne_ne_zero
    (h : G.PlayHistory) (hne : G.informationRankOne h ≠ 0) :
    G.commonBridgeSignalAt h =
      Sum.inl (G.observe1 h.lastState, G.knowledgeOneOfTwoAt h) := by
  unfold commonBridgeSignalAt
  rw [if_neg hne]

theorem commonBridgeSignalAt_eq_inr_of_rankOne_eq_zero
    (h : G.PlayHistory) (hz : G.informationRankOne h = 0) :
    G.commonBridgeSignalAt h =
      Sum.inr (G.knowledgeTwoOfOneAt h, G.observe2 h.lastState) := by
  unfold commonBridgeSignalAt
  rw [if_pos hz]

theorem commonSignalBridge_observations_equiv_one_to_two
    (hhier : G.DynamicHierarchy)
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsourceOne : G.OneDeterminesTwoAt source)
    (htargetNotOne : ¬ G.OneDeterminesTwoAt
      (source.step actionOne actionTwo nature)) :
    (G.commonSignalBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations1 =
      (G.commonSignalBridgeLift source actionOne actionTwo nature).observations1 ↔
    (G.commonSignalBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations2 =
      (G.commonSignalBridgeLift source actionOne actionTwo nature).observations2 := by
  classical
  set target := source.step actionOne actionTwo nature with htargetDef
  set alternativeTarget := alternativeSource.step alternativeActionOne
    alternativeActionTwo alternativeNature with halternativeTargetDef
  have htargetNonzero : G.informationRankOne target ≠ 0 :=
    fun hz => htargetNotOne ((G.informationRankOne_eq_zero_iff _).mp hz)
  have hcbTarget := G.commonBridgeSignalAt_eq_inl_of_rankOne_ne_zero target htargetNonzero
  -- From equality of the shared bridge letters, recover the reversal view data.
  have hsignal_to_view :
      G.commonBridgeSignalAt alternativeTarget = G.commonBridgeSignalAt target ->
        G.TwoDeterminesOneAt alternativeTarget ∧
          G.observe1 alternativeTarget.lastState = G.observe1 target.lastState ∧
          G.knowledgeOneOfTwoAt alternativeTarget = G.knowledgeOneOfTwoAt target := by
    intro hsig
    have haltNonzero : G.informationRankOne alternativeTarget ≠ 0 := by
      intro hz
      rw [G.commonBridgeSignalAt_eq_inr_of_rankOne_eq_zero alternativeTarget hz,
        hcbTarget] at hsig
      cases hsig
    have hcbAlt := G.commonBridgeSignalAt_eq_inl_of_rankOne_ne_zero
      alternativeTarget haltNonzero
    rw [hcbAlt, hcbTarget] at hsig
    have hpair := Sum.inl.inj hsig
    have haltTwo : G.TwoDeterminesOneAt alternativeTarget :=
      (hhier alternativeTarget).resolve_left
        (fun h => haltNonzero ((G.informationRankOne_eq_zero_iff _).mpr h))
    exact ⟨haltTwo, (Prod.mk.injEq _ _ _ _).mp hpair |>.1,
      (Prod.mk.injEq _ _ _ _).mp hpair |>.2⟩
  constructor
  · intro hobs
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step] at hobs
    obtain ⟨hprefixLift, hlastList⟩ := List.append_inj' hobs (by simp)
    have hlast := List.singleton_inj.mp hlastList
    change G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      at hlast
    rw [G.commonSignalBridgeLift_observe1, G.commonSignalBridgeLift_observe1] at hlast
    have hsig : G.commonBridgeSignalAt alternativeTarget =
        G.commonBridgeSignalAt target := Sum.inr.inj hlast
    have hprefixOne : alternativeSource.observations1 = source.observations1 :=
      G.commonSignalLift_observations1_injective _ _ hprefixLift
    obtain ⟨haltTwo, hlastOne, _hknow⟩ := hsignal_to_view hsig
    have hview := (G.balanced_bridge_view_equiv_one_to_two
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceOne haltTwo).mp
      ⟨hprefixOne, hlastOne⟩
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step]
    refine congrArg₂ (fun xs last => xs ++ [last]) ?_ ?_
    · exact G.commonSignalLift_observations2_congr hhier _ _ hview.1
    · change G.commonSignalCrossingEliminationGame.observe2
          (G.commonSignalBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.commonSignalCrossingEliminationGame.observe2
          (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      rw [G.commonSignalBridgeLift_observe2, G.commonSignalBridgeLift_observe2, hsig]
  · intro hobs
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step] at hobs
    obtain ⟨hprefixLift, hlastList⟩ := List.append_inj' hobs (by simp)
    have hlast := List.singleton_inj.mp hlastList
    change G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      at hlast
    rw [G.commonSignalBridgeLift_observe2, G.commonSignalBridgeLift_observe2] at hlast
    have hsig : G.commonBridgeSignalAt alternativeTarget =
        G.commonBridgeSignalAt target := Sum.inr.inj hlast
    have hprefixTwo : alternativeSource.observations2 = source.observations2 :=
      G.commonSignalLift_observations2_injective hhier _ _ hprefixLift
    obtain ⟨haltTwo, _hlastOne, hknow⟩ := hsignal_to_view hsig
    have hview := (G.balanced_bridge_view_equiv_one_to_two
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceOne haltTwo).mpr
      ⟨hprefixTwo, hknow⟩
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step]
    refine congrArg₂ (fun xs last => xs ++ [last]) ?_ ?_
    · exact G.commonSignalLift_observations1_congr _ _ hview.1
    · change G.commonSignalCrossingEliminationGame.observe1
          (G.commonSignalBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.commonSignalCrossingEliminationGame.observe1
          (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      rw [G.commonSignalBridgeLift_observe1, G.commonSignalBridgeLift_observe1, hsig]

/-- A strict one-to-two reversal reaches an actual information tie at the
common-signal bridge: both players determine each other there. -/
theorem commonSignalBridge_tie_one_to_two
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.OneDeterminesTwoAt source)
    (htarget : G.TwoStrictlyMoreInformedAt
      (source.step actionOne actionTwo nature)) :
    G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
        (G.commonSignalBridgeLift source actionOne actionTwo nature) ∧
      G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
        (G.commonSignalBridgeLift source actionOne actionTwo nature) := by
  have bridgeEquiv := G.commonSignalBridge_observations_equiv_one_to_two hhier
    source
  constructor
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.commonSignalRep_observation_normal rep
          simp only [CommonSignalObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.1.symm.trans heq)
          rw [PlayHistory.observations1_getLast?_last,
            PlayHistory.observations1_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.commonSignalLift_lastState,
            G.commonSignalBridgeLift_lastState] at hlast
          simp [commonSignalCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.commonSignalRep_observation_normal rep
    simp only [CommonSignalObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalOne := hnormalOne.symm.trans heq
    have hcanonicalTwo :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource htarget.2).mp
        hcanonicalOne
    exact hnormalTwo.trans hcanonicalTwo
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.commonSignalRep_observation_normal rep
          simp only [CommonSignalObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.2.symm.trans heq)
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.commonSignalLift_lastState,
            G.commonSignalBridgeLift_lastState] at hlast
          simp [commonSignalCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.commonSignalRep_observation_normal rep
    simp only [CommonSignalObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalTwo := hnormalTwo.symm.trans heq
    have hcanonicalOne :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource htarget.2).mpr
        hcanonicalTwo
    exact hnormalOne.trans hcanonicalOne

theorem commonSignalBridge_observations_equiv_two_to_one
    (hhier : G.DynamicHierarchy)
    (source alternativeSource : G.PlayHistory)
    (actionOne alternativeActionOne : G.Action1)
    (actionTwo alternativeActionTwo : G.Action2)
    (nature alternativeNature : G.Nature)
    (hsourceTwo : G.TwoDeterminesOneAt source)
    (htargetOne : G.OneDeterminesTwoAt
      (source.step actionOne actionTwo nature)) :
    (G.commonSignalBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations1 =
      (G.commonSignalBridgeLift source actionOne actionTwo nature).observations1 ↔
    (G.commonSignalBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).observations2 =
      (G.commonSignalBridgeLift source actionOne actionTwo nature).observations2 := by
  classical
  set target := source.step actionOne actionTwo nature with htargetDef
  set alternativeTarget := alternativeSource.step alternativeActionOne
    alternativeActionTwo alternativeNature with halternativeTargetDef
  have hzTarget : G.informationRankOne target = 0 :=
    (G.informationRankOne_eq_zero_iff target).mpr htargetOne
  have hcbTarget := G.commonBridgeSignalAt_eq_inr_of_rankOne_eq_zero target hzTarget
  have hsignal_to_view :
      G.commonBridgeSignalAt alternativeTarget = G.commonBridgeSignalAt target ->
        G.OneDeterminesTwoAt alternativeTarget ∧
          G.observe2 alternativeTarget.lastState = G.observe2 target.lastState ∧
          G.knowledgeTwoOfOneAt alternativeTarget = G.knowledgeTwoOfOneAt target := by
    intro hsig
    have haltZero : G.informationRankOne alternativeTarget = 0 := by
      by_contra hz
      rw [G.commonBridgeSignalAt_eq_inl_of_rankOne_ne_zero alternativeTarget hz,
        hcbTarget] at hsig
      cases hsig
    have hcbAlt := G.commonBridgeSignalAt_eq_inr_of_rankOne_eq_zero
      alternativeTarget haltZero
    rw [hcbAlt, hcbTarget] at hsig
    have hpair := Sum.inr.inj hsig
    refine ⟨(G.informationRankOne_eq_zero_iff _).mp haltZero, ?_, ?_⟩
    · exact ((Prod.mk.injEq _ _ _ _).mp hpair).2
    · exact ((Prod.mk.injEq _ _ _ _).mp hpair).1
  constructor
  · intro hobs
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step] at hobs
    obtain ⟨hprefixLift, hlastList⟩ := List.append_inj' hobs (by simp)
    have hlast := List.singleton_inj.mp hlastList
    change G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      at hlast
    rw [G.commonSignalBridgeLift_observe1, G.commonSignalBridgeLift_observe1] at hlast
    have hsig : G.commonBridgeSignalAt alternativeTarget =
        G.commonBridgeSignalAt target := Sum.inr.inj hlast
    have hprefixOne : alternativeSource.observations1 = source.observations1 :=
      G.commonSignalLift_observations1_injective _ _ hprefixLift
    obtain ⟨haltOne, _hobs2, hknow⟩ := hsignal_to_view hsig
    have hview := (G.balanced_bridge_view_equiv_two_to_one
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceTwo haltOne).mpr
      ⟨hprefixOne, hknow⟩
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step]
    refine congrArg₂ (fun xs last => xs ++ [last]) ?_ ?_
    · exact G.commonSignalLift_observations2_congr hhier _ _ hview.1
    · change G.commonSignalCrossingEliminationGame.observe2
          (G.commonSignalBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.commonSignalCrossingEliminationGame.observe2
          (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      rw [G.commonSignalBridgeLift_observe2, G.commonSignalBridgeLift_observe2, hsig]
  · intro hobs
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations2_step, PlayHistory.observations2_step] at hobs
    obtain ⟨hprefixLift, hlastList⟩ := List.append_inj' hobs (by simp)
    have hlast := List.singleton_inj.mp hlastList
    change G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      at hlast
    rw [G.commonSignalBridgeLift_observe2, G.commonSignalBridgeLift_observe2] at hlast
    have hsig : G.commonBridgeSignalAt alternativeTarget =
        G.commonBridgeSignalAt target := Sum.inr.inj hlast
    have hprefixTwo : alternativeSource.observations2 = source.observations2 :=
      G.commonSignalLift_observations2_injective hhier _ _ hprefixLift
    obtain ⟨haltOne, hobs2, _hknow⟩ := hsignal_to_view hsig
    have hview := (G.balanced_bridge_view_equiv_two_to_one
      source alternativeSource actionOne alternativeActionOne actionTwo
      alternativeActionTwo nature alternativeNature hsourceTwo haltOne).mp
      ⟨hprefixTwo, hobs2⟩
    rw [commonSignalBridgeLift, commonSignalBridgeLift,
      PlayHistory.observations1_step, PlayHistory.observations1_step]
    refine congrArg₂ (fun xs last => xs ++ [last]) ?_ ?_
    · exact G.commonSignalLift_observations1_congr _ _ hview.1
    · change G.commonSignalCrossingEliminationGame.observe1
          (G.commonSignalBridgeLift alternativeSource alternativeActionOne
            alternativeActionTwo alternativeNature).lastState =
        G.commonSignalCrossingEliminationGame.observe1
          (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
      rw [G.commonSignalBridgeLift_observe1, G.commonSignalBridgeLift_observe1, hsig]

/-- A strict two-to-one reversal reaches an actual information tie at the
common-signal bridge. -/
theorem commonSignalBridge_tie_two_to_one
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.TwoStrictlyMoreInformedAt source)
    (htarget : G.OneDeterminesTwoAt
      (source.step actionOne actionTwo nature)) :
    G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
        (G.commonSignalBridgeLift source actionOne actionTwo nature) ∧
      G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
        (G.commonSignalBridgeLift source actionOne actionTwo nature) := by
  have bridgeEquiv := G.commonSignalBridge_observations_equiv_two_to_one hhier
    source
  constructor
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.commonSignalRep_observation_normal rep
          simp only [CommonSignalObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.1.symm.trans heq)
          rw [PlayHistory.observations1_getLast?_last,
            PlayHistory.observations1_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.commonSignalLift_lastState,
            G.commonSignalBridgeLift_lastState] at hlast
          simp [commonSignalCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.commonSignalRep_observation_normal rep
    simp only [CommonSignalObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalOne := hnormalOne.symm.trans heq
    have hcanonicalTwo :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget).mp
        hcanonicalOne
    exact hnormalTwo.trans hcanonicalTwo
  · intro alternative heq
    obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
    have hphase : phase = true := by
      cases phase with
      | true => rfl
      | false =>
          exfalso
          have hnormal := G.commonSignalRep_observation_normal rep
          simp only [CommonSignalObservationNormal, Bool.false_eq_true,
            if_false] at hnormal
          have hlastGet := congrArg List.getLast? (hnormal.2.symm.trans heq)
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlastGet
          have hlast := Option.some.inj hlastGet
          rw [G.commonSignalLift_lastState,
            G.commonSignalBridgeLift_lastState] at hlast
          simp [commonSignalCrossingEliminationGame] at hlast
    subst phase
    have hnormal := G.commonSignalRep_observation_normal rep
    simp only [CommonSignalObservationNormal, if_true] at hnormal
    obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
      alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
    subst represented
    have hcanonicalTwo := hnormalTwo.symm.trans heq
    have hcanonicalOne :=
      (bridgeEquiv alternativeSource actionOne alternativeActionOne actionTwo
        alternativeActionTwo nature alternativeNature hsource.1 htarget).mpr
        hcanonicalTwo
    exact hnormalOne.trans hcanonicalOne

/-- **Every tie-broken rank switch passes through an information tie.**  This
strengthens strict crossing elimination with the tie-entry/tie-exit cases
needed by the shadow-player construction: ranks may change when a strict
leader reaches a tie because ties are awarded to player one. -/
theorem commonSignalBridge_tie_of_rank_change
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hchange : G.informationRankOne source ≠
      G.informationRankOne (source.step actionOne actionTwo nature)) :
    G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
        (G.commonSignalBridgeLift source actionOne actionTwo nature) ∧
      G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
        (G.commonSignalBridgeLift source actionOne actionTwo nature) := by
  by_cases hsourceOne : G.OneDeterminesTwoAt source
  · have htargetNotOne : ¬ G.OneDeterminesTwoAt
        (source.step actionOne actionTwo nature) := by
      intro htargetOne
      apply hchange
      unfold informationRankOne
      simp [hsourceOne, htargetOne]
    have htargetTwo : G.TwoDeterminesOneAt
        (source.step actionOne actionTwo nature) :=
      (hhier _).resolve_left htargetNotOne
    exact G.commonSignalBridge_tie_one_to_two hhier source actionOne actionTwo
      nature hsourceOne ⟨htargetTwo, htargetNotOne⟩
  · have hsourceTwo : G.TwoDeterminesOneAt source :=
      (hhier source).resolve_left hsourceOne
    have htargetOne : G.OneDeterminesTwoAt
        (source.step actionOne actionTwo nature) := by
      by_contra htargetNotOne
      apply hchange
      unfold informationRankOne
      simp [hsourceOne, htargetNotOne]
    exact G.commonSignalBridge_tie_two_to_one hhier source actionOne actionTwo
      nature ⟨hsourceTwo, hsourceOne⟩ htargetOne

/-! ### Determination lifts from the source to the bridge

If a player already determines the other at the source, the bridge only adds a
common last letter, so determination survives.  These monotonicity facts, with
the reversal ties above, close every case of the crossing-freeness proof. -/

theorem commonSignalBridge_oneDeterminesTwoAt_of_source
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.OneDeterminesTwoAt source) :
    G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
      (G.commonSignalBridgeLift source actionOne actionTwo nature) := by
  intro alternative heq
  obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
  have hphase : phase = true := by
    cases phase with
    | true => rfl
    | false =>
        exfalso
        have hnormal := G.commonSignalRep_observation_normal rep
        simp only [CommonSignalObservationNormal, Bool.false_eq_true,
          if_false] at hnormal
        have hlastGet := congrArg List.getLast? (hnormal.1.symm.trans heq)
        rw [PlayHistory.observations1_getLast?_last,
          PlayHistory.observations1_getLast?_last] at hlastGet
        have hlast := Option.some.inj hlastGet
        rw [G.commonSignalLift_lastState,
          G.commonSignalBridgeLift_lastState] at hlast
        simp [commonSignalCrossingEliminationGame] at hlast
  subst phase
  have hnormal := G.commonSignalRep_observation_normal rep
  simp only [CommonSignalObservationNormal, if_true] at hnormal
  obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
    alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
  subst represented
  have hbridgeOne :
      (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).observations1 =
        (G.commonSignalBridgeLift source actionOne actionTwo nature).observations1 :=
    hnormalOne.symm.trans heq
  rw [commonSignalBridgeLift, commonSignalBridgeLift,
    PlayHistory.observations1_step, PlayHistory.observations1_step] at hbridgeOne
  obtain ⟨hprefixLift, hlastList⟩ := List.append_inj' hbridgeOne (by simp)
  have hlast := List.singleton_inj.mp hlastList
  change G.commonSignalCrossingEliminationGame.observe1
      (G.commonSignalBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).lastState =
    G.commonSignalCrossingEliminationGame.observe1
      (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
    at hlast
  rw [G.commonSignalBridgeLift_observe1, G.commonSignalBridgeLift_observe1] at hlast
  have hsig : G.commonBridgeSignalAt
      (alternativeSource.step alternativeActionOne alternativeActionTwo
        alternativeNature) =
      G.commonBridgeSignalAt (source.step actionOne actionTwo nature) :=
    Sum.inr.inj hlast
  have hprefixOne : alternativeSource.observations1 = source.observations1 :=
    G.commonSignalLift_observations1_injective _ _ hprefixLift
  have haltSourceTwo : alternativeSource.observations2 = source.observations2 :=
    hsource alternativeSource hprefixOne
  rw [hnormalTwo, commonSignalBridgeLift, commonSignalBridgeLift,
    PlayHistory.observations2_step, PlayHistory.observations2_step]
  refine congrArg₂ (fun xs last => xs ++ [last]) ?_ ?_
  · exact G.commonSignalLift_observations2_congr hhier _ _ haltSourceTwo
  · change G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.commonSignalCrossingEliminationGame.observe2
        (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
    rw [G.commonSignalBridgeLift_observe2, G.commonSignalBridgeLift_observe2, hsig]

theorem commonSignalBridge_twoDeterminesOneAt_of_source
    (hhier : G.DynamicHierarchy) (source : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsource : G.TwoDeterminesOneAt source) :
    G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
      (G.commonSignalBridgeLift source actionOne actionTwo nature) := by
  intro alternative heq
  obtain ⟨phase, represented, rep⟩ := G.exists_commonSignalRep alternative
  have hphase : phase = true := by
    cases phase with
    | true => rfl
    | false =>
        exfalso
        have hnormal := G.commonSignalRep_observation_normal rep
        simp only [CommonSignalObservationNormal, Bool.false_eq_true,
          if_false] at hnormal
        have hlastGet := congrArg List.getLast? (hnormal.2.symm.trans heq)
        rw [PlayHistory.observations2_getLast?_last,
          PlayHistory.observations2_getLast?_last] at hlastGet
        have hlast := Option.some.inj hlastGet
        rw [G.commonSignalLift_lastState,
          G.commonSignalBridgeLift_lastState] at hlast
        simp [commonSignalCrossingEliminationGame] at hlast
  subst phase
  have hnormal := G.commonSignalRep_observation_normal rep
  simp only [CommonSignalObservationNormal, if_true] at hnormal
  obtain ⟨alternativeSource, alternativeActionOne, alternativeActionTwo,
    alternativeNature, hrepresented, hnormalOne, hnormalTwo⟩ := hnormal
  subst represented
  have hbridgeTwo :
      (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).observations2 =
        (G.commonSignalBridgeLift source actionOne actionTwo nature).observations2 :=
    hnormalTwo.symm.trans heq
  rw [commonSignalBridgeLift, commonSignalBridgeLift,
    PlayHistory.observations2_step, PlayHistory.observations2_step] at hbridgeTwo
  obtain ⟨hprefixLift, hlastList⟩ := List.append_inj' hbridgeTwo (by simp)
  have hlast := List.singleton_inj.mp hlastList
  change G.commonSignalCrossingEliminationGame.observe2
      (G.commonSignalBridgeLift alternativeSource alternativeActionOne
        alternativeActionTwo alternativeNature).lastState =
    G.commonSignalCrossingEliminationGame.observe2
      (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
    at hlast
  rw [G.commonSignalBridgeLift_observe2, G.commonSignalBridgeLift_observe2] at hlast
  have hsig : G.commonBridgeSignalAt
      (alternativeSource.step alternativeActionOne alternativeActionTwo
        alternativeNature) =
      G.commonBridgeSignalAt (source.step actionOne actionTwo nature) :=
    Sum.inr.inj hlast
  have hprefixTwo : alternativeSource.observations2 = source.observations2 :=
    G.commonSignalLift_observations2_injective hhier _ _ hprefixLift
  have haltSourceOne : alternativeSource.observations1 = source.observations1 :=
    hsource alternativeSource hprefixTwo
  rw [hnormalOne, commonSignalBridgeLift, commonSignalBridgeLift,
    PlayHistory.observations1_step, PlayHistory.observations1_step]
  refine congrArg₂ (fun xs last => xs ++ [last]) ?_ ?_
  · exact G.commonSignalLift_observations1_congr _ _ haltSourceOne
  · change G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalBridgeLift alternativeSource alternativeActionOne
          alternativeActionTwo alternativeNature).lastState =
      G.commonSignalCrossingEliminationGame.observe1
        (G.commonSignalBridgeLift source actionOne actionTwo nature).lastState
    rw [G.commonSignalBridgeLift_observe1, G.commonSignalBridgeLift_observe1, hsig]

/-! ### Crossing freeness of the common-signal adapter game

Determination depends only on the observation lists, so it is invariant under
the normal-form identification; every doubled step has exactly one bridge
endpoint; and the monotonicity and reversal-tie facts forbid a strict order
reversal across such a step.  This is the strict `DynamicHierarchy` input the
finite-state engine needs, obtained on the compiled arena. -/

theorem oneDeterminesTwoAt_congr {G' : FiniteConcurrentGame.{u}}
    {d e : G'.PlayHistory}
    (h1 : d.observations1 = e.observations1)
    (h2 : d.observations2 = e.observations2) :
    G'.OneDeterminesTwoAt d ↔ G'.OneDeterminesTwoAt e :=
  ⟨fun h alt halt => (h alt (halt.trans h1.symm)).trans h2,
    fun h alt halt => (h alt (halt.trans h1)).trans h2.symm⟩

theorem twoDeterminesOneAt_congr {G' : FiniteConcurrentGame.{u}}
    {d e : G'.PlayHistory}
    (h1 : d.observations1 = e.observations1)
    (h2 : d.observations2 = e.observations2) :
    G'.TwoDeterminesOneAt d ↔ G'.TwoDeterminesOneAt e :=
  ⟨fun h alt halt => (h alt (halt.trans h2.symm)).trans h1,
    fun h alt halt => (h alt (halt.trans h2)).trans h1.symm⟩

theorem commonSignalRep_false_step_obs
    {d : G.commonSignalCrossingEliminationGame.PlayHistory} {orig : G.PlayHistory}
    (rep : G.CommonSignalRep d false orig)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    (d.step actionOne actionTwo nature).observations1 =
        (G.commonSignalBridgeLift orig actionOne actionTwo nature).observations1 ∧
      (d.step actionOne actionTwo nature).observations2 =
        (G.commonSignalBridgeLift orig actionOne actionTwo nature).observations2 := by
  have hlast : d.lastState = (G.commonSignalLift orig).lastState := by
    rw [G.commonSignalRep_lastState rep, G.commonSignalLift_lastState]
  have hobs := G.commonSignalRep_observation_normal rep
  simp only [CommonSignalObservationNormal, Bool.false_eq_true, if_false] at hobs
  refine ⟨?_, ?_⟩
  · rw [PlayHistory.observations1_step, commonSignalBridgeLift,
      PlayHistory.observations1_step]
    refine congrArg₂ (fun xs last => xs ++ [last]) hobs.1 ?_
    rw [hlast]
  · rw [PlayHistory.observations2_step, commonSignalBridgeLift,
      PlayHistory.observations2_step]
    refine congrArg₂ (fun xs last => xs ++ [last]) hobs.2 ?_
    rw [hlast]

theorem commonSignalRep_true_step_obs
    {d : G.commonSignalCrossingEliminationGame.PlayHistory} {orig : G.PlayHistory}
    (rep : G.CommonSignalRep d true orig)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    (d.step actionOne actionTwo nature).observations1 =
        (G.commonSignalLift orig).observations1 ∧
      (d.step actionOne actionTwo nature).observations2 =
        (G.commonSignalLift orig).observations2 := by
  have hnormal := G.commonSignalRep_observation_normal
    (rep.toOriginal actionOne actionTwo nature)
  simp only [CommonSignalObservationNormal, Bool.false_eq_true, if_false] at hnormal
  exact hnormal

/-- **The common-signal adapter game is crossing-free.**  No doubled step
reverses the strict information order: on a step out of a lifted position the
order is preserved by monotonicity, and a step touching a bridge cannot be a
strict reversal because at a genuine reversal the bridge is an information tie
(`commonSignalBridge_tie_one_to_two`/`_two_to_one`).  This is paper `thm:main`'s
crossing elimination (BMvdB Lemma 12) realized on the common-signal arena. -/
theorem commonSignalCrossingEliminationGame_crossFree
    (hhier : G.DynamicHierarchy) :
    G.commonSignalCrossingEliminationGame.CrossFree := by
  intro d actionOne actionTwo nature hcross
  obtain ⟨phase, orig, rep⟩ := G.exists_commonSignalRep d
  cases phase with
  | false =>
      have hdObs := G.commonSignalRep_observation_normal rep
      simp only [CommonSignalObservationNormal, Bool.false_eq_true, if_false] at hdObs
      obtain ⟨hstep1, hstep2⟩ :=
        G.commonSignalRep_false_step_obs rep actionOne actionTwo nature
      have hOneD := (oneDeterminesTwoAt_congr hdObs.1 hdObs.2).trans
        (G.commonSignalLift_oneDeterminesTwoAt_iff hhier orig)
      have hTwoD := (twoDeterminesOneAt_congr hdObs.1 hdObs.2).trans
        (G.commonSignalLift_twoDeterminesOneAt_iff hhier orig)
      rcases hcross with ⟨hStrictD, hStrictD'⟩ | ⟨hStrictD, hStrictD'⟩
      · have hOneBridge := G.commonSignalBridge_oneDeterminesTwoAt_of_source hhier orig
          actionOne actionTwo nature (hOneD.mp hStrictD.1)
        exact hStrictD'.2 ((oneDeterminesTwoAt_congr hstep1 hstep2).mpr hOneBridge)
      · have hTwoBridge := G.commonSignalBridge_twoDeterminesOneAt_of_source hhier orig
          actionOne actionTwo nature (hTwoD.mp hStrictD.1)
        exact hStrictD'.2 ((twoDeterminesOneAt_congr hstep1 hstep2).mpr hTwoBridge)
  | true =>
      have hdObs := G.commonSignalRep_observation_normal rep
      simp only [CommonSignalObservationNormal, if_true] at hdObs
      obtain ⟨previous, pActionOne, pActionTwo, pNature, horig, hd1, hd2⟩ := hdObs
      obtain ⟨hstep1, hstep2⟩ :=
        G.commonSignalRep_true_step_obs rep actionOne actionTwo nature
      have hOneD' := (oneDeterminesTwoAt_congr hstep1 hstep2).trans
        (G.commonSignalLift_oneDeterminesTwoAt_iff hhier orig)
      have hTwoD' := (twoDeterminesOneAt_congr hstep1 hstep2).trans
        (G.commonSignalLift_twoDeterminesOneAt_iff hhier orig)
      rcases hcross with ⟨hStrictD, hStrictD'⟩ | ⟨hStrictD, hStrictD'⟩
      · -- `d` is the bridge; derive `TwoDeterminesOneAt d`, contradicting `OneStrict d`.
        have hTwoOrig : G.TwoDeterminesOneAt orig := hTwoD'.mp hStrictD'.1
        have hNotOneOrig : ¬ G.OneDeterminesTwoAt orig :=
          fun h => hStrictD'.2 (hOneD'.mpr h)
        have hTwoBridge : G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
            (G.commonSignalBridgeLift previous pActionOne pActionTwo pNature) := by
          rcases hhier previous with hDetPrev | hDetPrev
          · by_cases hTwoPrev : G.TwoDeterminesOneAt previous
            · exact G.commonSignalBridge_twoDeterminesOneAt_of_source hhier previous
                pActionOne pActionTwo pNature hTwoPrev
            · exact (G.commonSignalBridge_tie_one_to_two hhier previous pActionOne
                pActionTwo pNature hDetPrev
                (by rw [← horig]; exact ⟨hTwoOrig, hNotOneOrig⟩)).2
          · exact G.commonSignalBridge_twoDeterminesOneAt_of_source hhier previous
              pActionOne pActionTwo pNature hDetPrev
        exact hStrictD.2 ((twoDeterminesOneAt_congr hd1 hd2).mpr hTwoBridge)
      · have hOneOrig : G.OneDeterminesTwoAt orig := hOneD'.mp hStrictD'.1
        have hNotTwoOrig : ¬ G.TwoDeterminesOneAt orig :=
          fun h => hStrictD'.2 (hTwoD'.mpr h)
        have hOneBridge : G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
            (G.commonSignalBridgeLift previous pActionOne pActionTwo pNature) := by
          rcases hhier previous with hDetPrev | hDetPrev
          · exact G.commonSignalBridge_oneDeterminesTwoAt_of_source hhier previous
              pActionOne pActionTwo pNature hDetPrev
          · by_cases hOnePrev : G.OneDeterminesTwoAt previous
            · exact G.commonSignalBridge_oneDeterminesTwoAt_of_source hhier previous
                pActionOne pActionTwo pNature hOnePrev
            · exact (G.commonSignalBridge_tie_two_to_one hhier previous pActionOne
                pActionTwo pNature ⟨hDetPrev, hOnePrev⟩
                (by rw [← horig]; exact hOneOrig)).1
        exact hStrictD.2 ((oneDeterminesTwoAt_congr hd1 hd2).mpr hOneBridge)

end FiniteConcurrentGame

end DistributedSynthesis
