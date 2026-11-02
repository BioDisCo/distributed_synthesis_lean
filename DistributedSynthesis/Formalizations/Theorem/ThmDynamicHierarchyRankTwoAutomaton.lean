/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyRankAutomaton

/-!
# Finite observer for player two's tie-broken information rank

Unlike the player-one observer, this machine cannot be obtained by swapping
the players: equal information is deliberately ranked in player one's favour.
On a player-two observation word it tracks a represented history `left` and a
history `right` with the same player-one observations, remembering whether
their player-two observations differ.  Under dynamic hierarchy, existence of
such a divergent pair is constant throughout player two's information class.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

abbrev RankTwoBelief := G.RankPairState -> Bool

noncomputable def initialRankTwoBelief : G.RankTwoBelief :=
  G.initialRankBelief

/-- Advance a represented player-two history and a same-player-one-view
counterexample candidate. -/
noncomputable def rankTwoBeliefStep
    (belief : G.RankTwoBelief) (observation : G.Observation2) :
    G.RankTwoBelief := by
  classical
  exact fun target => decide <|
    ∃ pair : G.RankPairState,
      belief pair = true ∧
        target.1 ∈ G.allSuccessors pair.1 ∧
        target.2.1 ∈ G.allSuccessors pair.2.1 ∧
        G.observe2 target.1 = observation ∧
        G.observe1 target.1 = G.observe1 target.2.1 ∧
        target.2.2 =
          (pair.2.2 || G.observationTwoDiffers target.1 target.2.1)

theorem rankTwoBeliefStep_eq_true_iff
    (belief : G.RankTwoBelief) (observation : G.Observation2)
    (target : G.RankPairState) :
    G.rankTwoBeliefStep belief observation target = true ↔
      ∃ pair : G.RankPairState,
        belief pair = true ∧
          target.1 ∈ G.allSuccessors pair.1 ∧
          target.2.1 ∈ G.allSuccessors pair.2.1 ∧
          G.observe2 target.1 = observation ∧
          G.observe1 target.1 = G.observe1 target.2.1 ∧
          target.2.2 =
            (pair.2.2 || G.observationTwoDiffers target.1 target.2.1) := by
  classical
  simp [rankTwoBeliefStep]

/-- Semantic meaning of a pair reachable after reading player two's view. -/
def RankTwoPairWitness (observations : List G.Observation2)
    (pair : G.RankPairState) : Prop :=
  ∃ left right : G.PlayHistory,
    left.observations2 = observations ∧
      right.observations1 = left.observations1 ∧
      left.lastState = pair.1 ∧
      right.lastState = pair.2.1 ∧
      pair.2.2 = G.historiesTwoDiffer left right

/-- A player-two observation word extended after its nonempty initial prefix
comes from an actual final play step. -/
theorem exists_step_of_observations2_eq_append
    (history : G.PlayHistory) (observations : List G.Observation2)
    (observation : G.Observation2) (hnonempty : 0 < observations.length)
    (hobs : history.observations2 = observations ++ [observation]) :
    ∃ (previous : G.PlayHistory) (actionOne : G.Action1)
      (actionTwo : G.Action2) (nature : G.Nature),
      history = previous.step actionOne actionTwo nature ∧
        previous.observations2 = observations ∧
        G.observe2 (G.next previous.lastState actionOne actionTwo nature) =
          observation := by
  cases history with
  | initial =>
      exfalso
      have hlen := congrArg List.length hobs
      simp only [PlayHistory.observations2_initial, List.length_singleton,
        List.length_append] at hlen
      omega
  | step previous actionOne actionTwo nature =>
      have hobs' := hobs
      rw [PlayHistory.observations2_step] at hobs'
      obtain ⟨hprevious, hlast⟩ := List.append_inj' hobs' (by simp)
      refine ⟨previous, actionOne, actionTwo, nature, rfl, hprevious, ?_⟩
      simpa using hlast

theorem rankTwoBeliefStep_witness_forward
    (belief : G.RankTwoBelief) (observations : List G.Observation2)
    (observation : G.Observation2)
    (hinvariant : ∀ pair, belief pair = true ->
      G.RankTwoPairWitness observations pair)
    (target : G.RankPairState)
    (htarget : G.rankTwoBeliefStep belief observation target = true) :
    G.RankTwoPairWitness (observations ++ [observation]) target := by
  classical
  obtain ⟨pair, hpair, hsuccLeft, hsuccRight, hobsTwo, hobsOne, hflag⟩ :=
    (G.rankTwoBeliefStep_eq_true_iff belief observation target).mp htarget
  obtain ⟨left, right, hleftObs, hsameOne, hleftState,
    hrightState, hpairFlag⟩ := hinvariant pair hpair
  obtain ⟨leftActionOne, leftActionTwo, leftNature, hleftSucc⟩ :=
    (G.mem_allSuccessors_iff).mp hsuccLeft
  obtain ⟨rightActionOne, rightActionTwo, rightNature, hrightSucc⟩ :=
    (G.mem_allSuccessors_iff).mp hsuccRight
  refine
    ⟨left.step leftActionOne leftActionTwo leftNature,
      right.step rightActionOne rightActionTwo rightNature, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PlayHistory.observations2_step, hleftObs]
    congr 1
    rw [hleftState, ← hleftSucc]
    exact congrArg (fun x => [x]) hobsTwo
  · rw [PlayHistory.observations1_step, PlayHistory.observations1_step,
      hsameOne]
    congr 1
    rw [hleftState, hrightState, ← hleftSucc, ← hrightSucc]
    exact congrArg (fun x => [x]) hobsOne.symm
  · change G.next left.lastState leftActionOne leftActionTwo leftNature = target.1
    rw [hleftState, ← hleftSucc]
  · change
      G.next right.lastState rightActionOne rightActionTwo rightNature = target.2.1
    rw [hrightState, ← hrightSucc]
  · calc
      target.2.2 = (pair.2.2 ||
          G.observationTwoDiffers target.1 target.2.1) := hflag
      _ = (G.historiesTwoDiffer left right ||
          G.observationTwoDiffers
            (G.next left.lastState leftActionOne leftActionTwo leftNature)
            (G.next right.lastState rightActionOne rightActionTwo rightNature)) := by
              rw [hpairFlag, hleftState, hrightState, ← hleftSucc,
                ← hrightSucc]
      _ = G.historiesTwoDiffer
          (left.step leftActionOne leftActionTwo leftNature)
          (right.step rightActionOne rightActionTwo rightNature) :=
            (G.historiesTwoDiffer_step left right leftActionOne rightActionOne
              leftActionTwo rightActionTwo leftNature rightNature
              (by rw [hsameOne])).symm

theorem rankTwoBeliefStep_witness_backward
    (belief : G.RankTwoBelief) (observations : List G.Observation2)
    (observation : G.Observation2) (hnonempty : 0 < observations.length)
    (hinvariant : ∀ pair, G.RankTwoPairWitness observations pair ->
      belief pair = true)
    (target : G.RankPairState)
    (htarget : G.RankTwoPairWitness (observations ++ [observation]) target) :
    G.rankTwoBeliefStep belief observation target = true := by
  classical
  obtain ⟨left, right, hleftObs, hsameOne, hleftState,
    hrightState, hflag⟩ := htarget
  obtain ⟨leftPrevious, leftActionOne, leftActionTwo, leftNature,
    rfl, hleftPreviousObs, hleftLastObs⟩ :=
      G.exists_step_of_observations2_eq_append left observations observation
        hnonempty hleftObs
  have hrightObs :
      right.observations1 =
        leftPrevious.observations1 ++
          [G.observe1
            (G.next leftPrevious.lastState leftActionOne leftActionTwo leftNature)] := by
    simpa [PlayHistory.observations1_step] using hsameOne
  obtain ⟨rightPrevious, rightActionOne, rightActionTwo, rightNature,
    rfl, hsamePreviousOne, hsameLastOne⟩ :=
      G.exists_step_of_observations1_eq_append right leftPrevious.observations1
        (G.observe1
          (G.next leftPrevious.lastState leftActionOne leftActionTwo leftNature))
        (G.observations1_length_pos leftPrevious) hrightObs
  let predecessor : G.RankPairState :=
    (leftPrevious.lastState, rightPrevious.lastState,
      G.historiesTwoDiffer leftPrevious rightPrevious)
  apply (G.rankTwoBeliefStep_eq_true_iff belief observation target).mpr
  refine ⟨predecessor, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hinvariant predecessor
    exact ⟨leftPrevious, rightPrevious, hleftPreviousObs,
      hsamePreviousOne, rfl, rfl, rfl⟩
  · apply (G.mem_allSuccessors_iff).mpr
    exact ⟨leftActionOne, leftActionTwo, leftNature, hleftState.symm⟩
  · apply (G.mem_allSuccessors_iff).mpr
    exact ⟨rightActionOne, rightActionTwo, rightNature, hrightState.symm⟩
  · rw [← hleftState]
    exact hleftLastObs
  · rw [← hleftState, ← hrightState]
    exact hsameLastOne.symm
  · change target.2.2 =
      (G.historiesTwoDiffer leftPrevious rightPrevious ||
        G.observationTwoDiffers target.1 target.2.1)
    calc
      target.2.2 = G.historiesTwoDiffer
          (leftPrevious.step leftActionOne leftActionTwo leftNature)
          (rightPrevious.step rightActionOne rightActionTwo rightNature) := hflag
      _ = (G.historiesTwoDiffer leftPrevious rightPrevious ||
          G.observationTwoDiffers
            (G.next leftPrevious.lastState leftActionOne leftActionTwo leftNature)
            (G.next rightPrevious.lastState rightActionOne rightActionTwo rightNature)) :=
          G.historiesTwoDiffer_step leftPrevious rightPrevious
            leftActionOne rightActionOne leftActionTwo rightActionTwo
            leftNature rightNature (by rw [hsamePreviousOne])
      _ = (G.historiesTwoDiffer leftPrevious rightPrevious ||
          G.observationTwoDiffers target.1 target.2.1) := by
            have hleftNext :
                G.next leftPrevious.lastState leftActionOne leftActionTwo
                    leftNature = target.1 := by
              simpa using hleftState
            have hrightNext :
                G.next rightPrevious.lastState rightActionOne rightActionTwo
                    rightNature = target.2.1 := by
              simpa using hrightState
            rw [hleftNext, hrightNext]

theorem rankTwoBeliefStep_witness_iff
    (belief : G.RankTwoBelief) (observations : List G.Observation2)
    (observation : G.Observation2) (hnonempty : 0 < observations.length)
    (hinvariant : ∀ pair, belief pair = true ↔
      G.RankTwoPairWitness observations pair)
    (target : G.RankPairState) :
    G.rankTwoBeliefStep belief observation target = true ↔
      G.RankTwoPairWitness (observations ++ [observation]) target := by
  constructor
  · exact G.rankTwoBeliefStep_witness_forward belief observations observation
      (fun pair h => (hinvariant pair).mp h) target
  · exact G.rankTwoBeliefStep_witness_backward belief observations observation
      hnonempty (fun pair h => (hinvariant pair).mpr h) target

def rankTwoBeliefAmbiguous (belief : G.RankTwoBelief) : Prop :=
  ∃ pair, belief pair = true ∧ pair.2.2 = true

noncomputable instance (belief : G.RankTwoBelief) :
    Decidable (G.rankTwoBeliefAmbiguous belief) :=
  Classical.propDecidable _

abbrev RankTwoMachineMemory := Option G.RankTwoBelief

/-- Player two's finite observer for the globally tie-broken order signal. -/
noncomputable def rankTwoMachine :
    MooreController.{u, 0, u} G.Observation2 (Fin 2) where
  Memory := G.RankTwoMachineMemory
  memoryFinite := by
    classical
    letI : DecidableEq G.State := Classical.decEq _
    letI : Fintype G.RankPairState := inferInstance
    letI : Fintype G.RankTwoBelief := Pi.instFintype
    infer_instance
  initial := none
  update memory observation :=
    letI := Classical.decEq G.Observation2
    match memory with
    | none =>
        if observation = G.observe2 G.initial then some G.initialRankTwoBelief
        else some (fun _ => false)
    | some belief => some (G.rankTwoBeliefStep belief observation)
  output memory :=
    match memory with
    | none => 1
    | some belief => if G.rankTwoBeliefAmbiguous belief then 0 else 1

/-- A generated history with a singleton player-two observation word is the
initial history. -/
theorem eq_initial_of_observations2_eq_singleton
    (history : G.PlayHistory)
    (hobs : history.observations2 = [G.observe2 G.initial]) :
    history = PlayHistory.initial := by
  cases history with
  | initial => rfl
  | step previous actionOne actionTwo nature =>
      exfalso
      have hlen := congrArg List.length hobs
      rw [PlayHistory.observations2_step] at hlen
      have hpos := G.observations1_length_pos previous
      have heq : previous.observations2.length + 1 = 1 := by
        simpa using hlen
      rw [← G.observations_length_eq previous] at heq
      omega

/-- A generated history with a singleton player-one observation word is the
initial history. -/
theorem eq_initial_of_observations1_eq_singleton
    (history : G.PlayHistory)
    (hobs : history.observations1 = [G.observe1 G.initial]) :
    history = PlayHistory.initial := by
  cases history with
  | initial => rfl
  | step previous actionOne actionTwo nature =>
      exfalso
      have hlen := congrArg List.length hobs
      rw [PlayHistory.observations1_step] at hlen
      have hpos := G.observations1_length_pos previous
      have heq : previous.observations1.length + 1 = 1 := by
        simpa using hlen
      omega

theorem initialRankTwoBelief_witness_iff (target : G.RankPairState) :
    G.initialRankTwoBelief target = true ↔
      G.RankTwoPairWitness [G.observe2 G.initial] target := by
  rw [show G.initialRankTwoBelief = G.initialRankBelief from rfl,
    G.initialRankBelief_eq_true_iff]
  constructor
  · rintro rfl
    exact ⟨PlayHistory.initial, PlayHistory.initial, rfl, rfl, rfl, rfl,
      by simp [historiesTwoDiffer]⟩
  · rintro ⟨left, right, hleftObs, hsameOne, hleftState,
      hrightState, hflag⟩
    have hleft := G.eq_initial_of_observations2_eq_singleton left hleftObs
    subst left
    have hrightObs : right.observations1 = [G.observe1 G.initial] := by
      simpa using hsameOne
    have hright := G.eq_initial_of_observations1_eq_singleton right hrightObs
    subst right
    rcases target with ⟨stateOne, stateTwo, flag⟩
    change G.initial = stateOne at hleftState
    change G.initial = stateTwo at hrightState
    have hflag' : flag = false := by
      simpa [historiesTwoDiffer] using hflag
    subst stateOne
    subst stateTwo
    subst flag
    rfl

theorem rankTwoBelief_fold_witness_iff
    (belief : G.RankTwoBelief) (observations suffix : List G.Observation2)
    (hnonempty : 0 < observations.length)
    (hinvariant : ∀ pair, belief pair = true ↔
      G.RankTwoPairWitness observations pair)
    (target : G.RankPairState) :
    (suffix.foldl G.rankTwoBeliefStep belief) target = true ↔
      G.RankTwoPairWitness (observations ++ suffix) target := by
  induction suffix generalizing belief observations with
  | nil => simpa using hinvariant target
  | cons observation suffix ih =>
      rw [List.foldl_cons]
      have hstep := G.rankTwoBeliefStep_witness_iff belief observations
        observation hnonempty hinvariant
      have hnonempty' : 0 < (observations ++ [observation]).length := by simp
      have htail := ih (G.rankTwoBeliefStep belief observation)
        (observations ++ [observation]) hnonempty' hstep
      simpa [List.append_assoc] using htail

theorem rankTwoMachine_foldl_some
    (suffix : List G.Observation2) (belief : G.RankTwoBelief) :
    suffix.foldl G.rankTwoMachine.update (some belief) =
      some (suffix.foldl G.rankTwoBeliefStep belief) := by
  induction suffix generalizing belief with
  | nil => rfl
  | cons observation suffix ih =>
      simp only [List.foldl_cons]
      change suffix.foldl G.rankTwoMachine.update
          (some (G.rankTwoBeliefStep belief observation)) = _
      exact ih (G.rankTwoBeliefStep belief observation)

theorem rankTwoMachine_run_initial_cons (suffix : List G.Observation2) :
    G.rankTwoMachine.run (G.observe2 G.initial :: suffix) =
      some (suffix.foldl G.rankTwoBeliefStep G.initialRankTwoBelief) := by
  rw [MooreController.run_eq_foldl]
  simp only [List.foldl_cons]
  have hinitial :
      G.rankTwoMachine.update G.rankTwoMachine.initial
          (G.observe2 G.initial) = some G.initialRankTwoBelief := by
    simp [rankTwoMachine]
  rw [hinitial]
  exact G.rankTwoMachine_foldl_some suffix G.initialRankTwoBelief

theorem exists_observations2_tail (history : G.PlayHistory) :
    ∃ suffix, history.observations2 = G.observe2 G.initial :: suffix := by
  induction history with
  | initial => exact ⟨[], rfl⟩
  | step previous actionOne actionTwo nature ih =>
      obtain ⟨suffix, hsuffix⟩ := ih
      refine
        ⟨suffix ++
          [G.observe2 (G.next previous.lastState actionOne actionTwo nature)], ?_⟩
      rw [PlayHistory.observations2_step, hsuffix]
      simp

theorem rankTwoMachine_run_witness_iff (history : G.PlayHistory) :
    ∃ belief : G.RankTwoBelief,
      G.rankTwoMachine.run history.observations2 = some belief ∧
        ∀ target, belief target = true ↔
          G.RankTwoPairWitness history.observations2 target := by
  obtain ⟨suffix, hsuffix⟩ := G.exists_observations2_tail history
  let belief := suffix.foldl G.rankTwoBeliefStep G.initialRankTwoBelief
  refine ⟨belief, ?_, fun target => ?_⟩
  · rw [hsuffix]
    exact G.rankTwoMachine_run_initial_cons suffix
  · have hfold := G.rankTwoBelief_fold_witness_iff
      G.initialRankTwoBelief [G.observe2 G.initial] suffix (by simp)
      (fun pair => initialRankTwoBelief_witness_iff (G := G) pair) target
    simpa [belief, hsuffix] using hfold

/-- Dynamic hierarchy makes the existential counterexample monitor agree
with player one's determining status at the actual represented history. -/
theorem rankTwoBeliefAmbiguous_iff_not_oneDeterminesTwoAt
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory)
    (belief : G.RankTwoBelief)
    (hinvariant : ∀ target, belief target = true ↔
      G.RankTwoPairWitness history.observations2 target) :
    G.rankTwoBeliefAmbiguous belief ↔ ¬ G.OneDeterminesTwoAt history := by
  classical
  constructor
  · rintro ⟨pair, hpair, hflag⟩ hdetermines
    obtain ⟨left, right, hleftObs, hsameOne, -, -, hpairFlag⟩ :=
      (hinvariant pair).mp hpair
    have hdeterminesLeft : G.OneDeterminesTwoAt left :=
      (G.oneDeterminesTwoAt_congr_observations2_of_dynamic hhier
        history left hleftObs.symm).mp hdetermines
    have hsameTwo := hdeterminesLeft right hsameOne
    have hdifferent : left.observations2 ≠ right.observations2 := by
      have : G.historiesTwoDiffer left right = true := by
        rw [← hpairFlag]
        exact hflag
      simpa [historiesTwoDiffer] using this
    exact hdifferent hsameTwo.symm
  · intro hnot
    unfold OneDeterminesTwoAt at hnot
    push Not at hnot
    obtain ⟨alternative, hsameOne, hdifferentTwo⟩ := hnot
    have hdifferentTwo' :
        history.observations2 ≠ alternative.observations2 := by
      intro heq
      exact hdifferentTwo heq.symm
    let target : G.RankPairState :=
      (history.lastState, alternative.lastState, true)
    refine ⟨target, (hinvariant target).mpr ?_, rfl⟩
    exact ⟨history, alternative, rfl, hsameOne, rfl, rfl,
      by simp [target, historiesTwoDiffer, hdifferentTwo']⟩

/-- Correctness of player two's finite rank observer under dynamic
hierarchical information. -/
theorem rankTwoMachine_output_run
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.rankTwoMachine.output
        (G.rankTwoMachine.run history.observations2) =
      G.informationRankTwo history := by
  obtain ⟨belief, hrun, hinvariant⟩ :=
    G.rankTwoMachine_run_witness_iff history
  rw [hrun]
  have hambiguous :=
    G.rankTwoBeliefAmbiguous_iff_not_oneDeterminesTwoAt
      hhier history belief hinvariant
  unfold rankTwoMachine informationRankTwo
  by_cases hdetermines : G.OneDeterminesTwoAt history
  · have : ¬ G.rankTwoBeliefAmbiguous belief := by
      simpa [hambiguous] using hdetermines
    simp [hdetermines, this]
  · have : G.rankTwoBeliefAmbiguous belief := hambiguous.mpr hdetermines
    simp [hdetermines, this]

/-- Two-player finite-state form of the rank-signal conclusion of Lemma 11:
both local Moore observers implement the same complementary, tie-broken global
information order. -/
theorem exists_finite_informationRank_machines
    (hhier : G.DynamicHierarchy) :
    ∃ (machineOne : MooreController.{u, 0, u} G.Observation1 (Fin 2))
      (machineTwo : MooreController.{u, 0, u} G.Observation2 (Fin 2)),
      (∀ history : G.PlayHistory,
        machineOne.output (machineOne.run history.observations1) =
          G.informationRankOne history) ∧
      (∀ history : G.PlayHistory,
        machineTwo.output (machineTwo.run history.observations2) =
          G.informationRankTwo history) ∧
      (∀ history : G.PlayHistory,
        (machineOne.output (machineOne.run history.observations1) = 0 ∧
          machineTwo.output (machineTwo.run history.observations2) = 1) ∨
        (machineOne.output (machineOne.run history.observations1) = 1 ∧
          machineTwo.output (machineTwo.run history.observations2) = 0)) := by
  refine ⟨G.rankOneMachine, G.rankTwoMachine,
    G.rankOneMachine_output_run, G.rankTwoMachine_output_run hhier, ?_⟩
  intro history
  rw [G.rankOneMachine_output_run, G.rankTwoMachine_output_run hhier]
  exact G.informationRank_complementary history

end FiniteConcurrentGame

end DistributedSynthesis
