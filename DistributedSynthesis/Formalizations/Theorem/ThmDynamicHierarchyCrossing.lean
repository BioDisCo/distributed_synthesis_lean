/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyRankTwoAutomaton
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset

/-!
# Finite knowledge signals for crossing elimination

This develops the first concrete component of Berwanger--Mathew--van den
Bogaard Lemma 12.  The signal `knowledgeTwoOfOneAt` is the set of player-one
observations that player two considers possible now; its mirror is
`knowledgeOneOfTwoAt`.  Both are implemented by finite Moore machines, using
the exact belief invariants already proved for the rank observers.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

/-- Player one is strictly more informed at this history. -/
def OneStrictlyMoreInformedAt (history : G.PlayHistory) : Prop :=
  G.OneDeterminesTwoAt history ∧ ¬ G.TwoDeterminesOneAt history

/-- Player two is strictly more informed at this history. -/
def TwoStrictlyMoreInformedAt (history : G.PlayHistory) : Prop :=
  G.TwoDeterminesOneAt history ∧ ¬ G.OneDeterminesTwoAt history

/-- The two players cross on one generated move when their strict information
order reverses. -/
def CrossOnStep (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) : Prop :=
  (G.OneStrictlyMoreInformedAt history ∧
      G.TwoStrictlyMoreInformedAt
        (history.step actionOne actionTwo nature)) ∨
    (G.TwoStrictlyMoreInformedAt history ∧
      G.OneStrictlyMoreInformedAt
        (history.step actionOne actionTwo nature))

def CrossFree : Prop :=
  ∀ (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature),
    ¬ G.CrossOnStep history actionOne actionTwo nature

/-- Under hierarchy, failure of player one's preorder is exactly strict
superiority of player two. -/
theorem twoStrictlyMoreInformedAt_iff_not_oneDetermines
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.TwoStrictlyMoreInformedAt history ↔
      ¬ G.OneDeterminesTwoAt history := by
  constructor
  · exact fun h => h.2
  · intro hnot
    exact ⟨(hhier history).resolve_left hnot, hnot⟩

/-- The semantic finite-valued signal: current player-one observations that
remain possible in player two's perfect-recall information class. -/
noncomputable def knowledgeTwoOfOneAt
    (history : G.PlayHistory) : Finset G.Observation1 := by
  classical
  exact Finset.univ.filter fun observation =>
    ∃ alternative : G.PlayHistory,
      alternative.observations2 = history.observations2 ∧
        G.observe1 alternative.lastState = observation

/-- The mirror signal: current player-two observations that player one still
considers possible. -/
noncomputable def knowledgeOneOfTwoAt
    (history : G.PlayHistory) : Finset G.Observation2 := by
  classical
  exact Finset.univ.filter fun observation =>
    ∃ alternative : G.PlayHistory,
      alternative.observations1 = history.observations1 ∧
        G.observe2 alternative.lastState = observation

theorem knowledgeTwoOfOneAt_congr_observations2
    (history alternative : G.PlayHistory)
    (heq : history.observations2 = alternative.observations2) :
    G.knowledgeTwoOfOneAt history = G.knowledgeTwoOfOneAt alternative := by
  classical
  unfold knowledgeTwoOfOneAt
  rw [heq]

theorem knowledgeOneOfTwoAt_congr_observations1
    (history alternative : G.PlayHistory)
    (heq : history.observations1 = alternative.observations1) :
    G.knowledgeOneOfTwoAt history = G.knowledgeOneOfTwoAt alternative := by
  classical
  unfold knowledgeOneOfTwoAt
  rw [heq]

/-- When player one is at least as informed, player two's knowledge signal is
already determined by player one's own view, so revealing it adds no power. -/
theorem knowledgeTwoOfOneAt_consistent_to_one
    (history alternative : G.PlayHistory)
    (hdetermines : G.OneDeterminesTwoAt history)
    (heq : history.observations1 = alternative.observations1) :
    G.knowledgeTwoOfOneAt history = G.knowledgeTwoOfOneAt alternative := by
  apply G.knowledgeTwoOfOneAt_congr_observations2
  exact (hdetermines alternative heq.symm).symm

/-- Mirror no-information-gain property for revealing player one's knowledge
signal to an at-least-as-informed player two. -/
theorem knowledgeOneOfTwoAt_consistent_to_two
    (history alternative : G.PlayHistory)
    (hdetermines : G.TwoDeterminesOneAt history)
    (heq : history.observations2 = alternative.observations2) :
    G.knowledgeOneOfTwoAt history = G.knowledgeOneOfTwoAt alternative := by
  apply G.knowledgeOneOfTwoAt_congr_observations1
  exact (hdetermines alternative heq.symm).symm

theorem currentObservation_mem_knowledgeTwoOfOneAt
    (history : G.PlayHistory) :
    G.observe1 history.lastState ∈ G.knowledgeTwoOfOneAt history := by
  classical
  simp only [knowledgeTwoOfOneAt, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨history, rfl, rfl⟩

theorem currentObservation_mem_knowledgeOneOfTwoAt
    (history : G.PlayHistory) :
    G.observe2 history.lastState ∈ G.knowledgeOneOfTwoAt history := by
  classical
  simp only [knowledgeOneOfTwoAt, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨history, rfl, rfl⟩

/-- The conditionally visible half-step letters, stated already on original
histories. -/
noncomputable def bridgeSignalOneAt
    (history : G.PlayHistory) : Option (Finset G.Observation1) :=
  if G.informationRankOne history = 0 then
    some (G.knowledgeTwoOfOneAt history)
  else none

noncomputable def bridgeSignalTwoAt
    (history : G.PlayHistory) : Option (Finset G.Observation2) :=
  if G.informationRankTwo history = 0 then
    some (G.knowledgeOneOfTwoAt history)
  else none

theorem informationRankOne_eq_zero_iff (history : G.PlayHistory) :
    G.informationRankOne history = 0 ↔ G.OneDeterminesTwoAt history := by
  classical
  unfold informationRankOne
  by_cases hdet : G.OneDeterminesTwoAt history <;> simp [hdet]

theorem informationRankTwo_eq_zero_iff (history : G.PlayHistory) :
    G.informationRankTwo history = 0 ↔ ¬ G.OneDeterminesTwoAt history := by
  classical
  unfold informationRankTwo
  by_cases hdet : G.OneDeterminesTwoAt history <;> simp [hdet]

/-- Although the bridge letter mentions player two's knowledge, its guarded
form is a legitimate player-one signal. -/
theorem bridgeSignalOneAt_consistent
    (history alternative : G.PlayHistory)
    (heq : history.observations1 = alternative.observations1) :
    G.bridgeSignalOneAt history = G.bridgeSignalOneAt alternative := by
  classical
  have hrank := G.informationRankOne_consistent history alternative heq
  unfold bridgeSignalOneAt
  by_cases hzero : G.informationRankOne history = 0
  · have hzeroAlt : G.informationRankOne alternative = 0 := by
      rwa [← hrank]
    simp only [hzero, hzeroAlt, if_true, Option.some.injEq]
    apply G.knowledgeTwoOfOneAt_consistent_to_one history alternative
    · exact (G.informationRankOne_eq_zero_iff history).mp hzero
    · exact heq
  · have hzeroAlt : G.informationRankOne alternative ≠ 0 := by
      rwa [← hrank]
    simp [hzero, hzeroAlt]

/-- Under dynamic hierarchy, the guarded mirror letter is a legitimate
player-two signal. -/
theorem bridgeSignalTwoAt_consistent
    (hhier : G.DynamicHierarchy) (history alternative : G.PlayHistory)
    (heq : history.observations2 = alternative.observations2) :
    G.bridgeSignalTwoAt history = G.bridgeSignalTwoAt alternative := by
  classical
  have hrank := G.informationRankTwo_consistent hhier history alternative heq
  unfold bridgeSignalTwoAt
  by_cases hzero : G.informationRankTwo history = 0
  · have hzeroAlt : G.informationRankTwo alternative = 0 := by
      rwa [← hrank]
    simp only [hzero, hzeroAlt, if_true, Option.some.injEq]
    apply G.knowledgeOneOfTwoAt_consistent_to_two history alternative
    · have hnot := (G.informationRankTwo_eq_zero_iff history).mp hzero
      exact (hhier history).resolve_left hnot
    · exact heq
  · have hzeroAlt : G.informationRankTwo alternative ≠ 0 := by
      rwa [← hrank]
    simp [hzero, hzeroAlt]

/-! ## A local finite observer for player two's bridge letter -/

/-- Project the counterexample component of player two's pair belief. -/
noncomputable def rankTwoBridgeKnowledgeOutput
    (belief : G.RankTwoBelief) : Finset G.Observation2 := by
  classical
  exact Finset.univ.filter fun observation =>
    ∃ pair : G.RankPairState,
      belief pair = true ∧ G.observe2 pair.2.1 = observation

noncomputable def rankTwoBridgeLetterOutput
    (belief : G.RankTwoBelief) : Option (Finset G.Observation2) :=
  if G.rankTwoBeliefAmbiguous belief then
    some (G.rankTwoBridgeKnowledgeOutput belief)
  else none

/-- The bridge letter is computed from the same finite memory as player two's
rank machine. -/
noncomputable def bridgeSignalTwoMachine :
    MooreController.{u, u, u} G.Observation2
      (Option (Finset G.Observation2)) where
  Memory := G.RankTwoMachineMemory
  memoryFinite := G.rankTwoMachine.memoryFinite
  initial := G.rankTwoMachine.initial
  update := G.rankTwoMachine.update
  output memory :=
    match memory with
    | none => none
    | some belief => G.rankTwoBridgeLetterOutput belief

@[simp]
theorem bridgeSignalTwoMachine_run (observations : List G.Observation2) :
    G.bridgeSignalTwoMachine.run observations =
      G.rankTwoMachine.run observations := by
  rfl

theorem rankTwoBridgeKnowledgeOutput_eq
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory)
    (belief : G.RankTwoBelief)
    (hinvariant : ∀ target, belief target = true ↔
      G.RankTwoPairWitness history.observations2 target)
    (hnot : ¬ G.OneDeterminesTwoAt history) :
    G.rankTwoBridgeKnowledgeOutput belief =
      G.knowledgeOneOfTwoAt history := by
  classical
  have htwo : G.TwoDeterminesOneAt history :=
    (hhier history).resolve_left hnot
  ext observation
  simp only [rankTwoBridgeKnowledgeOutput, knowledgeOneOfTwoAt,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨pair, hpair, hobserve⟩
    obtain ⟨left, right, hleftObs, hsameOne, hleftState,
      hrightState, hflag⟩ := (hinvariant pair).mp hpair
    refine ⟨right, ?_, ?_⟩
    · exact hsameOne.trans (htwo left hleftObs)
    · rw [hrightState]
      exact hobserve
  · rintro ⟨alternative, halternativeObs, hobserve⟩
    let pair : G.RankPairState :=
      (history.lastState, alternative.lastState,
        G.historiesTwoDiffer history alternative)
    refine ⟨pair, (hinvariant pair).mpr ?_, ?_⟩
    · exact ⟨history, alternative, rfl, halternativeObs, rfl, rfl, rfl⟩
    · simpa [pair] using hobserve

/-- Exact finite-state reconstruction of player two's guarded bridge signal. -/
theorem bridgeSignalTwoMachine_output_run
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.bridgeSignalTwoMachine.output
        (G.bridgeSignalTwoMachine.run history.observations2) =
      G.bridgeSignalTwoAt history := by
  obtain ⟨belief, hrun, hinvariant⟩ :=
    G.rankTwoMachine_run_witness_iff history
  rw [G.bridgeSignalTwoMachine_run, hrun]
  have hambiguous :=
    G.rankTwoBeliefAmbiguous_iff_not_oneDeterminesTwoAt
      hhier history belief hinvariant
  unfold bridgeSignalTwoMachine rankTwoBridgeLetterOutput bridgeSignalTwoAt
  change
    (if G.rankTwoBeliefAmbiguous belief then
      some (G.rankTwoBridgeKnowledgeOutput belief)
    else none) =
      (if G.informationRankTwo history = 0 then
        some (G.knowledgeOneOfTwoAt history)
      else none)
  by_cases hnot : ¬ G.OneDeterminesTwoAt history
  · have hamb : G.rankTwoBeliefAmbiguous belief := hambiguous.mpr hnot
    have hrank : G.informationRankTwo history = 0 :=
      (G.informationRankTwo_eq_zero_iff history).mpr hnot
    rw [if_pos hamb, if_pos hrank]
    congr 1
    exact G.rankTwoBridgeKnowledgeOutput_eq hhier history belief hinvariant hnot
  · have hamb : ¬ G.rankTwoBeliefAmbiguous belief := by
      exact fun h => hnot (hambiguous.mp h)
    have hrank : G.informationRankTwo history ≠ 0 := by
      intro hzero
      exact hnot ((G.informationRankTwo_eq_zero_iff history).mp hzero)
    simp [hamb, hrank]

noncomputable def rankTwoKnowledgeOutput
    (belief : G.RankTwoBelief) : Finset G.Observation1 := by
  classical
  exact Finset.univ.filter fun observation =>
    ∃ pair : G.RankPairState,
      belief pair = true ∧ G.observe1 pair.1 = observation

noncomputable def rankOneKnowledgeOutput
    (belief : G.RankBelief) : Finset G.Observation2 := by
  classical
  exact Finset.univ.filter fun observation =>
    ∃ pair : G.RankPairState,
      belief pair = true ∧ G.observe2 pair.1 = observation

/-- Finite Moore implementation of `knowledgeTwoOfOneAt`. -/
noncomputable def knowledgeTwoOfOneMachine :
    MooreController.{u, u, u} G.Observation2 (Finset G.Observation1) where
  Memory := G.RankTwoMachineMemory
  memoryFinite := G.rankTwoMachine.memoryFinite
  initial := G.rankTwoMachine.initial
  update := G.rankTwoMachine.update
  output memory :=
    match memory with
    | none => ∅
    | some belief => G.rankTwoKnowledgeOutput belief

/-- Finite Moore implementation of `knowledgeOneOfTwoAt`. -/
noncomputable def knowledgeOneOfTwoMachine :
    MooreController.{u, u, u} G.Observation1 (Finset G.Observation2) where
  Memory := G.RankMachineMemory
  memoryFinite := G.rankOneMachine.memoryFinite
  initial := G.rankOneMachine.initial
  update := G.rankOneMachine.update
  output memory :=
    match memory with
    | none => ∅
    | some belief => G.rankOneKnowledgeOutput belief

@[simp]
theorem knowledgeTwoOfOneMachine_run (observations : List G.Observation2) :
    G.knowledgeTwoOfOneMachine.run observations =
      G.rankTwoMachine.run observations := by
  rfl

@[simp]
theorem knowledgeOneOfTwoMachine_run (observations : List G.Observation1) :
    G.knowledgeOneOfTwoMachine.run observations =
      G.rankOneMachine.run observations := by
  rfl

theorem rankTwoKnowledgeOutput_eq
    (history : G.PlayHistory) (belief : G.RankTwoBelief)
    (hinvariant : ∀ target, belief target = true ↔
      G.RankTwoPairWitness history.observations2 target) :
    G.rankTwoKnowledgeOutput belief = G.knowledgeTwoOfOneAt history := by
  classical
  ext observation
  simp only [rankTwoKnowledgeOutput, knowledgeTwoOfOneAt,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨pair, hpair, hobserve⟩
    obtain ⟨left, right, hleftObs, hsameOne, hleftState,
      hrightState, hflag⟩ := (hinvariant pair).mp hpair
    refine ⟨left, hleftObs, ?_⟩
    rw [hleftState]
    exact hobserve
  · rintro ⟨alternative, halternativeObs, hobserve⟩
    let pair : G.RankPairState :=
      (alternative.lastState, alternative.lastState, false)
    refine ⟨pair, (hinvariant pair).mpr ?_, ?_⟩
    · exact ⟨alternative, alternative, halternativeObs, rfl, rfl, rfl,
        by simp [pair, historiesTwoDiffer]⟩
    · simpa [pair] using hobserve

theorem rankOneKnowledgeOutput_eq
    (history : G.PlayHistory) (belief : G.RankBelief)
    (hinvariant : ∀ target, belief target = true ↔
      G.RankPairWitness history.observations1 target) :
    G.rankOneKnowledgeOutput belief = G.knowledgeOneOfTwoAt history := by
  classical
  ext observation
  simp only [rankOneKnowledgeOutput, knowledgeOneOfTwoAt,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨pair, hpair, hobserve⟩
    obtain ⟨left, right, hleftObs, hrightObs, hleftState,
      hrightState, hflag⟩ := (hinvariant pair).mp hpair
    refine ⟨left, hleftObs, ?_⟩
    rw [hleftState]
    exact hobserve
  · rintro ⟨alternative, halternativeObs, hobserve⟩
    let pair : G.RankPairState :=
      (alternative.lastState, alternative.lastState, false)
    refine ⟨pair, (hinvariant pair).mpr ?_, ?_⟩
    · exact ⟨alternative, alternative, halternativeObs, halternativeObs,
        rfl, rfl, by simp [pair, historiesTwoDiffer]⟩
    · simpa [pair] using hobserve

/-- Correct finite-state implementation of player two's knowledge about the
current player-one observation. -/
theorem knowledgeTwoOfOneMachine_output_run (history : G.PlayHistory) :
    G.knowledgeTwoOfOneMachine.output
        (G.knowledgeTwoOfOneMachine.run history.observations2) =
      G.knowledgeTwoOfOneAt history := by
  obtain ⟨belief, hrun, hinvariant⟩ :=
    G.rankTwoMachine_run_witness_iff history
  rw [G.knowledgeTwoOfOneMachine_run, hrun]
  exact G.rankTwoKnowledgeOutput_eq history belief hinvariant

/-- Correct finite-state implementation of player one's knowledge about the
current player-two observation. -/
theorem knowledgeOneOfTwoMachine_output_run (history : G.PlayHistory) :
    G.knowledgeOneOfTwoMachine.output
        (G.knowledgeOneOfTwoMachine.run history.observations1) =
      G.knowledgeOneOfTwoAt history := by
  obtain ⟨belief, hrun, hinvariant⟩ :=
    G.rankOneMachine_run_witness_iff history
  rw [G.knowledgeOneOfTwoMachine_run, hrun]
  exact G.rankOneKnowledgeOutput_eq history belief hinvariant

/-! ## Concrete doubled arena -/

/-- State synchronized with both belief monitors.  The Boolean phase is
`false` at an original position and `true` at the inserted intermediary
position. -/
abbrev CrossingState :=
  Bool × G.State × G.rankOneMachine.Memory × G.rankTwoMachine.Memory

/-- Synchronize both monitor memories with a newly reached original state. -/
noncomputable def crossingAdvance
    (state : G.CrossingState) (nextState : G.State) : G.CrossingState :=
  (true, nextState,
    G.rankOneMachine.update state.2.2.1 (G.observe1 nextState),
    G.rankTwoMachine.update state.2.2.2 (G.observe2 nextState))

/-- The concrete half-step arena of Lemma 12.  Original moves enter an
intermediary state carrying the updated finite signals; intermediary moves
ignore all choices and expose the same target as the next original state.
Duplicating the target priority preserves the parity condition. -/
noncomputable def crossingEliminationGame : FiniteConcurrentGame where
  State := G.CrossingState
  Action1 := G.Action1
  Action2 := G.Action2
  Nature := G.Nature
  Observation1 :=
    Sum (G.Observation1 × Fin 2) (Option (Finset G.Observation1))
  Observation2 :=
    Sum (G.Observation2 × Fin 2) (Option (Finset G.Observation2))
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
  initial :=
    (false, G.initial,
      G.rankOneMachine.update G.rankOneMachine.initial
        (G.observe1 G.initial),
      G.rankTwoMachine.update G.rankTwoMachine.initial
        (G.observe2 G.initial))
  next state actionOne actionTwo nature :=
    if state.1 then
      (false, state.2.1, state.2.2.1, state.2.2.2)
    else
      G.crossingAdvance state
        (G.next state.2.1 actionOne actionTwo nature)
  observe1 state :=
    if state.1 then
      Sum.inr <|
        if G.rankOneMachine.output state.2.2.1 = 0 then
          some (G.knowledgeTwoOfOneMachine.output state.2.2.2)
        else none
    else
      Sum.inl
        (G.observe1 state.2.1, G.rankOneMachine.output state.2.2.1)
  observe2 state :=
    if state.1 then
      Sum.inr <|
        if G.rankTwoMachine.output state.2.2.2 = 0 then
          some (G.knowledgeOneOfTwoMachine.output state.2.2.1)
        else none
    else
      Sum.inl
        (G.observe2 state.2.1, G.rankTwoMachine.output state.2.2.2)
  priority state := G.priority state.2.1

@[simp]
theorem crossingEliminationGame_initial_phase :
    G.crossingEliminationGame.initial.1 = false := rfl

@[simp]
theorem crossingEliminationGame_next_original
    (state : G.CrossingState) (hphase : state.1 = false)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    G.crossingEliminationGame.next state actionOne actionTwo nature =
      G.crossingAdvance state
        (G.next state.2.1 actionOne actionTwo nature) := by
  simp [crossingEliminationGame, hphase]

@[simp]
theorem crossingEliminationGame_next_intermediary
    (state : G.CrossingState) (hphase : state.1 = true)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    G.crossingEliminationGame.next state actionOne actionTwo nature =
      (false, state.2.1, state.2.2.1, state.2.2.2) := by
  simp [crossingEliminationGame, hphase]

@[simp]
theorem crossingAdvance_phase (state : G.CrossingState) (nextState : G.State) :
    (G.crossingAdvance state nextState).1 = true := rfl

@[simp]
theorem crossingEliminationGame_priority (state : G.CrossingState) :
    G.crossingEliminationGame.priority state = G.priority state.2.1 := rfl

/-! ## Exact history embedding -/

/-- Embed an original history at an original-phase position of the doubled
arena.  Each original transition is followed by one forced intermediary
transition; the repeated witnesses are harmless because that transition
ignores all choices. -/
noncomputable def crossingLift :
    G.PlayHistory -> G.crossingEliminationGame.PlayHistory
  | .initial => .initial
  | .step previous actionOne actionTwo nature =>
      (((crossingLift previous).step actionOne actionTwo nature)).step
        actionOne actionTwo nature

/-- The intermediary history belonging to one original transition. -/
noncomputable def crossingBridgeLift
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.crossingEliminationGame.PlayHistory :=
  (G.crossingLift history).step actionOne actionTwo nature

/-- Every lifted original history ends in the original state synchronized with
the exact memories reached by the two rank observers. -/
theorem crossingLift_lastState (history : G.PlayHistory) :
    (G.crossingLift history).lastState =
      (false, history.lastState,
        G.rankOneMachine.run history.observations1,
        G.rankTwoMachine.run history.observations2) := by
  induction history with
  | initial =>
      simp [crossingLift, PlayHistory.lastState,
        crossingEliminationGame, MooreController.run]
  | step previous actionOne actionTwo nature ih =>
      rw [crossingLift]
      change G.crossingEliminationGame.next
        (G.crossingEliminationGame.next
          (G.crossingLift previous).lastState actionOne actionTwo nature)
        actionOne actionTwo nature = _
      rw [ih]
      simp [crossingEliminationGame, crossingAdvance,
        PlayHistory.lastState, PlayHistory.observations1_step,
        PlayHistory.observations2_step]

/-- The first half of a lifted move ends at the synchronized intermediary
state for the original target history. -/
theorem crossingBridgeLift_lastState
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    (G.crossingBridgeLift history actionOne actionTwo nature).lastState =
      (true, (history.step actionOne actionTwo nature).lastState,
        G.rankOneMachine.run
          (history.step actionOne actionTwo nature).observations1,
        G.rankTwoMachine.run
          (history.step actionOne actionTwo nature).observations2) := by
  unfold crossingBridgeLift
  change G.crossingEliminationGame.next (G.crossingLift history).lastState
    actionOne actionTwo nature = _
  rw [G.crossingLift_lastState]
  simp [crossingEliminationGame, crossingAdvance,
    PlayHistory.lastState, PlayHistory.observations1_step,
    PlayHistory.observations2_step]

/-- Projection of a lifted original history recovers its original last state. -/
theorem crossingLift_project_state (history : G.PlayHistory) :
    (G.crossingLift history).lastState.2.1 = history.lastState := by
  rw [G.crossingLift_lastState]

theorem crossingLift_observe1 (history : G.PlayHistory) :
    G.crossingEliminationGame.observe1 (G.crossingLift history).lastState =
      Sum.inl
        (G.observe1 history.lastState, G.informationRankOne history) := by
  rw [G.crossingLift_lastState]
  simp [crossingEliminationGame, G.rankOneMachine_output_run]

theorem crossingLift_observe2
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.crossingEliminationGame.observe2 (G.crossingLift history).lastState =
      Sum.inl
        (G.observe2 history.lastState, G.informationRankTwo history) := by
  rw [G.crossingLift_lastState]
  simp [crossingEliminationGame, G.rankTwoMachine_output_run hhier]

/-- Exact half-step signal seen by player one: player two's knowledge is
revealed precisely when player one is at least as informed at the target. -/
theorem crossingBridgeLift_observe1
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    let target := history.step actionOne actionTwo nature
    G.crossingEliminationGame.observe1
        (G.crossingBridgeLift history actionOne actionTwo nature).lastState =
      Sum.inr
        (if G.informationRankOne target = 0 then
          some (G.knowledgeTwoOfOneAt target)
        else none) := by
  dsimp only
  rw [G.crossingBridgeLift_lastState]
  simp only [crossingEliminationGame, if_true]
  rw [G.rankOneMachine_output_run]
  have hknowledge := G.knowledgeTwoOfOneMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeTwoOfOneMachine_run] at hknowledge
  rw [hknowledge]

/-- Exact half-step signal seen by player two: the mirror signal is exposed
precisely in the strict-player-two case selected by the global tie-break. -/
theorem crossingBridgeLift_observe2
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    let target := history.step actionOne actionTwo nature
    G.crossingEliminationGame.observe2
        (G.crossingBridgeLift history actionOne actionTwo nature).lastState =
      Sum.inr
        (if G.informationRankTwo target = 0 then
          some (G.knowledgeOneOfTwoAt target)
        else none) := by
  dsimp only
  rw [G.crossingBridgeLift_lastState]
  simp only [crossingEliminationGame, if_true]
  rw [G.rankTwoMachine_output_run hhier]
  have hknowledge := G.knowledgeOneOfTwoMachine_output_run
    (history.step actionOne actionTwo nature)
  rw [G.knowledgeOneOfTwoMachine_run] at hknowledge
  rw [hknowledge]

/-! ## Forward transport of finite controllers -/

/-- Run an original player-one controller on the doubled arena: consume the
original observation component and ignore the non-actionable bridge signal. -/
def liftControllerOne
    (controller : MooreController.{u, u, u} G.Observation1 G.Action1) :
    MooreController.{u, u, u}
      G.crossingEliminationGame.Observation1 G.Action1 where
  Memory := controller.Memory
  memoryFinite := controller.memoryFinite
  initial := controller.initial
  update memory observation :=
    match observation with
    | Sum.inl original => controller.update memory original.1
    | Sum.inr _ => memory
  output := controller.output

/-- Mirror forward transport for player two. -/
def liftControllerTwo
    (controller : MooreController.{u, u, u} G.Observation2 G.Action2) :
    MooreController.{u, u, u}
      G.crossingEliminationGame.Observation2 G.Action2 where
  Memory := controller.Memory
  memoryFinite := controller.memoryFinite
  initial := controller.initial
  update memory observation :=
    match observation with
    | Sum.inl original => controller.update memory original.1
    | Sum.inr _ => memory
  output := controller.output

theorem liftControllerOne_run_crossingLift
    (controller : MooreController.{u, u, u} G.Observation1 G.Action1)
    (history : G.PlayHistory) :
    (G.liftControllerOne controller).run
        (G.crossingLift history).observations1 =
      controller.run history.observations1 := by
  induction history with
  | initial =>
      simp [crossingLift, liftControllerOne, MooreController.run,
        crossingEliminationGame]
  | step previous actionOne actionTwo nature ih =>
      rw [crossingLift]
      rw [PlayHistory.observations1_step, PlayHistory.observations1_step]
      rw [MooreController.run_append_singleton,
        MooreController.run_append_singleton]
      rw [ih]
      rw [PlayHistory.observations1_step,
        MooreController.run_append_singleton]
      change (G.liftControllerOne controller).update
        ((G.liftControllerOne controller).update
          (controller.run previous.observations1)
          (G.crossingEliminationGame.observe1
            (G.crossingBridgeLift previous actionOne actionTwo nature).lastState))
        (G.crossingEliminationGame.observe1
          (G.crossingLift
            (previous.step actionOne actionTwo nature)).lastState) = _
      rw [G.crossingBridgeLift_observe1, G.crossingLift_observe1]
      simp [liftControllerOne, PlayHistory.lastState]

theorem liftControllerTwo_run_crossingLift
    (controller : MooreController.{u, u, u} G.Observation2 G.Action2)
    (history : G.PlayHistory) :
    (G.liftControllerTwo controller).run
        (G.crossingLift history).observations2 =
      controller.run history.observations2 := by
  induction history with
  | initial =>
      simp [crossingLift, liftControllerTwo, MooreController.run,
        crossingEliminationGame]
  | step previous actionOne actionTwo nature ih =>
      rw [crossingLift]
      rw [PlayHistory.observations2_step, PlayHistory.observations2_step]
      rw [MooreController.run_append_singleton,
        MooreController.run_append_singleton]
      rw [ih]
      rw [PlayHistory.observations2_step,
        MooreController.run_append_singleton]
      change (G.liftControllerTwo controller).update
        ((G.liftControllerTwo controller).update
          (controller.run previous.observations2)
          (G.crossingEliminationGame.observe2
            (G.crossingBridgeLift previous actionOne actionTwo nature).lastState))
        (G.crossingEliminationGame.observe2
          (G.crossingLift
            (previous.step actionOne actionTwo nature)).lastState) = _
      rw [G.crossingBridgeLift_lastState,
        G.crossingLift_lastState]
      simp [liftControllerTwo, crossingEliminationGame,
        PlayHistory.lastState]

theorem liftControllerOne_strategy_crossingLift
    (controller : MooreController.{u, u, u} G.Observation1 G.Action1)
    (history : G.PlayHistory) :
    (G.liftControllerOne controller).strategy
        (G.crossingLift history).observations1 =
      controller.strategy history.observations1 := by
  unfold MooreController.strategy
  rw [G.liftControllerOne_run_crossingLift]
  rfl

theorem liftControllerTwo_strategy_crossingLift
    (controller : MooreController.{u, u, u} G.Observation2 G.Action2)
    (history : G.PlayHistory) :
    (G.liftControllerTwo controller).strategy
        (G.crossingLift history).observations2 =
      controller.strategy history.observations2 := by
  unfold MooreController.strategy
  rw [G.liftControllerTwo_run_crossingLift]
  rfl

/-- Original and intermediary copies both carry exactly the corresponding
original priority. -/
theorem crossingLift_priority (history : G.PlayHistory) :
    G.crossingEliminationGame.priority (G.crossingLift history).lastState =
      G.priority history.lastState := by
  rw [G.crossingLift_lastState]
  rfl

theorem crossingBridgeLift_priority
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.crossingEliminationGame.priority
        (G.crossingBridgeLift history actionOne actionTwo nature).lastState =
      G.priority (history.step actionOne actionTwo nature).lastState := by
  rw [G.crossingBridgeLift_lastState]
  rfl

/-- Packaged forward finite-state strategy transport.  On every embedded
original history, both transported controllers choose exactly the original
actions, while the doubled priority trace only repeats target priorities. -/
theorem exists_forward_crossing_controller_transport
    (controllerOne : MooreController.{u, u, u} G.Observation1 G.Action1)
    (controllerTwo : MooreController.{u, u, u} G.Observation2 G.Action2) :
    ∃ (liftedOne : MooreController.{u, u, u}
        G.crossingEliminationGame.Observation1 G.Action1)
      (liftedTwo : MooreController.{u, u, u}
        G.crossingEliminationGame.Observation2 G.Action2),
      (∀ history : G.PlayHistory,
        liftedOne.strategy (G.crossingLift history).observations1 =
          controllerOne.strategy history.observations1) ∧
      (∀ history : G.PlayHistory,
        liftedTwo.strategy (G.crossingLift history).observations2 =
          controllerTwo.strategy history.observations2) := by
  exact ⟨G.liftControllerOne controllerOne, G.liftControllerTwo controllerTwo,
    G.liftControllerOne_strategy_crossingLift controllerOne,
    G.liftControllerTwo_strategy_crossingLift controllerTwo⟩

/-! ## Reverse controller transport for player two -/

abbrev ReverseControllerTwoMemory
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation2 G.Action2) :=
  Bool × controller.Memory × G.bridgeSignalTwoMachine.Memory

/-- Compile a doubled-arena player-two controller back to the original arena.
On the first observation it feeds only the original-position letter; later it
first reconstructs and feeds the bridge letter, then the target letter. -/
noncomputable def reverseControllerTwo
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation2 G.Action2) :
    MooreController.{u, u, u} G.Observation2 G.Action2 where
  Memory := G.ReverseControllerTwoMemory controller
  memoryFinite := by infer_instance
  initial := (false, controller.initial, G.bridgeSignalTwoMachine.initial)
  update memory observation :=
    let signalMemory :=
      G.bridgeSignalTwoMachine.update memory.2.2 observation
    let originalLetter : G.crossingEliminationGame.Observation2 :=
      Sum.inl
        (observation, G.rankTwoMachine.output signalMemory)
    let controllerMemory :=
      if memory.1 then
        controller.update
          (controller.update memory.2.1
            (Sum.inr (G.bridgeSignalTwoMachine.output signalMemory)))
          originalLetter
      else
        controller.update memory.2.1 originalLetter
    (true, controllerMemory, signalMemory)
  output memory := controller.output memory.2.1

theorem reverseControllerTwo_run
    (hhier : G.DynamicHierarchy)
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation2 G.Action2)
    (history : G.PlayHistory) :
    (G.reverseControllerTwo controller).run history.observations2 =
      (true,
        controller.run (G.crossingLift history).observations2,
        G.bridgeSignalTwoMachine.run history.observations2) := by
  induction history with
  | initial =>
      simp [reverseControllerTwo, MooreController.run, crossingLift,
        crossingEliminationGame, bridgeSignalTwoMachine, rankTwoMachine]
  | step previous actionOne actionTwo nature ih =>
      rw [PlayHistory.observations2_step,
        MooreController.run_append_singleton, ih]
      rw [crossingLift, PlayHistory.observations2_step,
        PlayHistory.observations2_step,
        MooreController.run_append_singleton,
        MooreController.run_append_singleton]
      have hrank := G.rankTwoMachine_output_run hhier
        (previous.step actionOne actionTwo nature)
      have hsignal := G.bridgeSignalTwoMachine_output_run hhier
        (previous.step actionOne actionTwo nature)
      have hbridge := G.crossingBridgeLift_observe2 hhier previous
        actionOne actionTwo nature
      have horiginal := G.crossingLift_observe2 hhier
        (previous.step actionOne actionTwo nature)
      have hbridge' :
          G.crossingEliminationGame.observe2
              (G.crossingBridgeLift previous actionOne actionTwo nature).lastState =
            Sum.inr
              (G.bridgeSignalTwoAt
                (previous.step actionOne actionTwo nature)) := by
        simpa [bridgeSignalTwoAt] using hbridge
      have hsignalMemory :
          G.bridgeSignalTwoMachine.update
              (G.bridgeSignalTwoMachine.run previous.observations2)
              (G.observe2
                (G.next previous.lastState actionOne actionTwo nature)) =
            G.bridgeSignalTwoMachine.run
              (previous.step actionOne actionTwo nature).observations2 := by
        rw [PlayHistory.observations2_step,
          MooreController.run_append_singleton]
      simp only [reverseControllerTwo]
      simp only [if_true]
      rw [hsignalMemory, hsignal]
      rw [G.bridgeSignalTwoMachine_run, hrank]
      have hfirst :
          G.crossingEliminationGame.observe2
              (G.crossingEliminationGame.next
                (G.crossingLift previous).lastState
                actionOne actionTwo nature) =
            Sum.inr
              (G.bridgeSignalTwoAt
                (previous.step actionOne actionTwo nature)) := by
        change G.crossingEliminationGame.observe2
          (G.crossingBridgeLift previous actionOne actionTwo nature).lastState = _
        exact hbridge'
      have hsecond :
          G.crossingEliminationGame.observe2
              (G.crossingEliminationGame.next
                ((G.crossingLift previous).step
                  actionOne actionTwo nature).lastState
                actionOne actionTwo nature) =
            Sum.inl
              (G.observe2
                  (previous.step actionOne actionTwo nature).lastState,
                G.informationRankTwo
                  (previous.step actionOne actionTwo nature)) := by
        change G.crossingEliminationGame.observe2
          (G.crossingLift
            (previous.step actionOne actionTwo nature)).lastState = _
        exact horiginal
      rw [hfirst, hsecond]
      simp [PlayHistory.lastState, PlayHistory.observations2_step,
        MooreController.run_append_singleton,
        G.bridgeSignalTwoMachine_run]

theorem reverseControllerTwo_strategy
    (hhier : G.DynamicHierarchy)
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation2 G.Action2)
    (history : G.PlayHistory) :
    (G.reverseControllerTwo controller).strategy history.observations2 =
      controller.strategy (G.crossingLift history).observations2 := by
  unfold MooreController.strategy
  rw [G.reverseControllerTwo_run hhier]
  rfl

/-! ## Player swap used by the reverse player-one compiler -/

/-- Exchange the two player interfaces without changing states, Nature, or
priorities. -/
def swapPlayers : FiniteConcurrentGame where
  State := G.State
  Action1 := G.Action2
  Action2 := G.Action1
  Nature := G.Nature
  Observation1 := G.Observation2
  Observation2 := G.Observation1
  stateFinite := G.stateFinite
  action1Finite := G.action2Finite
  action2Finite := G.action1Finite
  natureFinite := G.natureFinite
  observation1Finite := G.observation2Finite
  observation2Finite := G.observation1Finite
  initial := G.initial
  next state actionTwo actionOne nature :=
    G.next state actionOne actionTwo nature
  observe1 := G.observe2
  observe2 := G.observe1
  priority := G.priority

def swapHistory : G.PlayHistory -> G.swapPlayers.PlayHistory
  | .initial => .initial
  | .step previous actionOne actionTwo nature =>
      (swapHistory previous).step actionTwo actionOne nature

def unswapHistory : G.swapPlayers.PlayHistory -> G.PlayHistory
  | .initial => .initial
  | .step previous actionTwo actionOne nature =>
      (unswapHistory previous).step actionOne actionTwo nature

@[simp]
theorem unswapHistory_swapHistory (history : G.PlayHistory) :
    G.unswapHistory (G.swapHistory history) = history := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      simp [swapHistory, unswapHistory, ih]

@[simp]
theorem swapHistory_unswapHistory (history : G.swapPlayers.PlayHistory) :
    G.swapHistory (G.unswapHistory history) = history := by
  induction history with
  | initial => rfl
  | step previous actionTwo actionOne nature ih =>
      simp [swapHistory, unswapHistory, ih]

@[simp]
theorem swapHistory_lastState (history : G.PlayHistory) :
    (G.swapHistory history).lastState = history.lastState := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      simp only [swapHistory, PlayHistory.lastState, swapPlayers]
      exact congrArg
        (fun state => G.next state actionOne actionTwo nature) ih

@[simp]
theorem unswapHistory_lastState (history : G.swapPlayers.PlayHistory) :
    (G.unswapHistory history).lastState = history.lastState := by
  have h := G.swapHistory_lastState (G.unswapHistory history)
  simpa using h.symm

@[simp]
theorem swapHistory_observations1 (history : G.PlayHistory) :
    (G.swapHistory history).observations1 = history.observations2 := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      simp only [swapHistory, PlayHistory.observations1_step,
        PlayHistory.observations2_step, swapPlayers]
      have hnext := congrArg
        (fun state => G.next state actionOne actionTwo nature)
        (G.swapHistory_lastState previous)
      exact congrArg₂
        (fun observations state => observations ++ [G.observe2 state]) ih hnext

@[simp]
theorem swapHistory_observations2 (history : G.PlayHistory) :
    (G.swapHistory history).observations2 = history.observations1 := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      simp only [swapHistory, PlayHistory.observations1_step,
        PlayHistory.observations2_step, swapPlayers]
      have hnext := congrArg
        (fun state => G.next state actionOne actionTwo nature)
        (G.swapHistory_lastState previous)
      exact congrArg₂
        (fun observations state => observations ++ [G.observe1 state]) ih hnext

@[simp]
theorem unswapHistory_observations1
    (history : G.swapPlayers.PlayHistory) :
    (G.unswapHistory history).observations1 = history.observations2 := by
  have h := G.swapHistory_observations2 (G.unswapHistory history)
  simpa using h.symm

@[simp]
theorem unswapHistory_observations2
    (history : G.swapPlayers.PlayHistory) :
    (G.unswapHistory history).observations2 = history.observations1 := by
  have h := G.swapHistory_observations1 (G.unswapHistory history)
  simpa using h.symm

theorem swap_oneDeterminesTwoAt_iff
    (history : G.PlayHistory) :
    G.swapPlayers.OneDeterminesTwoAt (G.swapHistory history) ↔
      G.TwoDeterminesOneAt history := by
  constructor
  · intro hdet alternative heq
    have h := hdet (G.swapHistory alternative)
    have heq' :
        (G.swapHistory alternative).observations1 =
          (G.swapHistory history).observations1 := by
      simpa using heq
    simpa using h heq'
  · intro hdet alternative heq
    have h := hdet (G.unswapHistory alternative)
    have heq' :
        (G.unswapHistory alternative).observations2 =
          history.observations2 := by
      simpa using heq
    simpa using h heq'

theorem swap_twoDeterminesOneAt_iff
    (history : G.PlayHistory) :
    G.swapPlayers.TwoDeterminesOneAt (G.swapHistory history) ↔
      G.OneDeterminesTwoAt history := by
  constructor
  · intro hdet alternative heq
    have h := hdet (G.swapHistory alternative)
    have heq' :
        (G.swapHistory alternative).observations2 =
          (G.swapHistory history).observations2 := by
      simpa using heq
    simpa using h heq'
  · intro hdet alternative heq
    have h := hdet (G.unswapHistory alternative)
    have heq' :
        (G.unswapHistory alternative).observations1 =
          history.observations1 := by
      simpa using heq
    simpa using h heq'

theorem swap_dynamicHierarchy (hhier : G.DynamicHierarchy) :
    G.swapPlayers.DynamicHierarchy := by
  intro history
  let original := G.unswapHistory history
  have hrepr : G.swapHistory original = history := by
    simp [original]
  rw [← hrepr, G.swap_oneDeterminesTwoAt_iff,
    G.swap_twoDeterminesOneAt_iff]
  exact (hhier original).symm

theorem swap_knowledgeOneOfTwoAt (history : G.PlayHistory) :
    G.swapPlayers.knowledgeOneOfTwoAt (G.swapHistory history) =
      G.knowledgeTwoOfOneAt history := by
  classical
  ext observation
  constructor
  · intro hmem
    have hsemantic :
        ∃ alternative : G.swapPlayers.PlayHistory,
          alternative.observations1 =
              (G.swapHistory history).observations1 ∧
            G.swapPlayers.observe2 alternative.lastState = observation := by
      change observation ∈ Finset.univ.filter (fun observation =>
        ∃ alternative : G.swapPlayers.PlayHistory,
          alternative.observations1 =
              (G.swapHistory history).observations1 ∧
            G.swapPlayers.observe2 alternative.lastState = observation) at hmem
      exact (Finset.mem_filter.mp hmem).2
    obtain ⟨alternative, heq, hobserve⟩ := hsemantic
    change observation ∈ Finset.univ.filter (fun observation =>
      ∃ alternative : G.PlayHistory,
        alternative.observations2 = history.observations2 ∧
          G.observe1 alternative.lastState = observation)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ observation,
      G.unswapHistory alternative, ?_, ?_⟩
    · simpa using heq
    · change G.observe1 (G.unswapHistory alternative).lastState = observation
      rw [G.unswapHistory_lastState]
      exact hobserve
  · intro hmem
    have hsemantic :
        ∃ alternative : G.PlayHistory,
          alternative.observations2 = history.observations2 ∧
            G.observe1 alternative.lastState = observation := by
      change observation ∈ Finset.univ.filter (fun observation =>
        ∃ alternative : G.PlayHistory,
          alternative.observations2 = history.observations2 ∧
            G.observe1 alternative.lastState = observation) at hmem
      exact (Finset.mem_filter.mp hmem).2
    obtain ⟨alternative, heq, hobserve⟩ := hsemantic
    have htarget :
        ∃ alternative : G.swapPlayers.PlayHistory,
          alternative.observations1 =
              (G.swapHistory history).observations1 ∧
            G.swapPlayers.observe2 alternative.lastState = observation := by
      refine ⟨G.swapHistory alternative, ?_, ?_⟩
      · simpa using heq
      · change G.observe1 (G.swapHistory alternative).lastState = observation
        rw [G.swapHistory_lastState]
        exact hobserve
    change observation ∈ Finset.univ.filter (fun observation =>
      ∃ alternative : G.swapPlayers.PlayHistory,
        alternative.observations1 =
            (G.swapHistory history).observations1 ∧
          G.swapPlayers.observe2 alternative.lastState = observation)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ observation, htarget⟩

theorem observations1_getLast?_eq (history : G.PlayHistory) :
    history.observations1.getLast? =
      some (G.observe1 history.lastState) := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      rw [PlayHistory.observations1_step]
      simp [PlayHistory.lastState]

theorem currentObservation_eq_of_observations1_eq
    (left right : G.PlayHistory)
    (heq : left.observations1 = right.observations1) :
    G.observe1 left.lastState = G.observe1 right.lastState := by
  have h := congrArg List.getLast? heq
  rw [G.observations1_getLast?_eq, G.observations1_getLast?_eq] at h
  exact Option.some.inj h

theorem knowledgeTwoOfOneAt_eq_singleton_of_twoDetermines
    (history : G.PlayHistory) (hdet : G.TwoDeterminesOneAt history) :
    G.knowledgeTwoOfOneAt history =
      {G.observe1 history.lastState} := by
  classical
  ext observation
  simp only [knowledgeTwoOfOneAt, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨alternative, heq, hobserve⟩
    rw [← hobserve]
    exact G.currentObservation_eq_of_observations1_eq alternative history
      (hdet alternative heq)
  · rintro rfl
    exact ⟨history, rfl, rfl⟩

abbrev BridgeSignalOneMemory :=
  G.swapPlayers.bridgeSignalTwoMachine.Memory ×
    G.rankOneMachine.Memory × Option G.Observation1

/-- Player one's bridge observer reuses the swapped strict-order observer.  In
an information tie the desired knowledge set is the singleton current
observation, supplied by the third memory component. -/
noncomputable def bridgeSignalOneMachine :
    MooreController.{u, u, u} G.Observation1
      (Option (Finset G.Observation1)) where
  Memory := G.BridgeSignalOneMemory
  memoryFinite := by infer_instance
  initial :=
    (G.swapPlayers.bridgeSignalTwoMachine.initial,
      G.rankOneMachine.initial, none)
  update memory observation :=
    (G.swapPlayers.bridgeSignalTwoMachine.update memory.1 observation,
      G.rankOneMachine.update memory.2.1 observation, some observation)
  output memory :=
    match G.swapPlayers.bridgeSignalTwoMachine.output memory.1 with
    | some knowledge => some knowledge
    | none =>
        match memory.2.2 with
        | some observation =>
            if G.rankOneMachine.output memory.2.1 = 0 then
              some {observation}
            else none
        | none => none

theorem bridgeSignalOneMachine_run_state (history : G.PlayHistory) :
    G.bridgeSignalOneMachine.run history.observations1 =
      (G.swapPlayers.bridgeSignalTwoMachine.run
          (G.swapHistory history).observations2,
        G.rankOneMachine.run history.observations1,
        some (G.observe1 history.lastState)) := by
  induction history with
  | initial =>
      simp [bridgeSignalOneMachine, MooreController.run, swapHistory,
        swapPlayers, rankOneMachine, bridgeSignalTwoMachine,
        PlayHistory.lastState]
  | step previous actionOne actionTwo nature ih =>
      rw [PlayHistory.observations1_step,
        MooreController.run_append_singleton, ih]
      simp only [bridgeSignalOneMachine]
      have hrun :
          G.swapPlayers.bridgeSignalTwoMachine.run
              (G.swapHistory
                (previous.step actionOne actionTwo nature)).observations2 =
            G.swapPlayers.bridgeSignalTwoMachine.update
              (G.swapPlayers.bridgeSignalTwoMachine.run previous.observations1)
              (G.observe1
                (G.next previous.lastState actionOne actionTwo nature)) := by
        rw [G.swapHistory_observations2,
          PlayHistory.observations1_step]
        exact G.swapPlayers.bridgeSignalTwoMachine.run_append_singleton
          previous.observations1
          (G.observe1
            (G.next previous.lastState actionOne actionTwo nature))
      rw [hrun]
      simp [PlayHistory.lastState]

/-- Exact finite-state reconstruction of player one's guarded bridge signal. -/
theorem bridgeSignalOneMachine_output_run
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    G.bridgeSignalOneMachine.output
        (G.bridgeSignalOneMachine.run history.observations1) =
      G.bridgeSignalOneAt history := by
  rw [G.bridgeSignalOneMachine_run_state]
  have hswap :=
    G.swapPlayers.bridgeSignalTwoMachine_output_run
      (G.swap_dynamicHierarchy hhier) (G.swapHistory history)
  have hrank := G.rankOneMachine_output_run history
  unfold bridgeSignalOneMachine bridgeSignalOneAt
  change
    (match G.swapPlayers.bridgeSignalTwoMachine.output
        (G.swapPlayers.bridgeSignalTwoMachine.run
          (G.swapHistory history).observations2) with
      | some knowledge => some knowledge
      | none =>
          if G.rankOneMachine.output
              (G.rankOneMachine.run history.observations1) = 0 then
            some {G.observe1 history.lastState}
          else none) =
      (if G.informationRankOne history = 0 then
        some (G.knowledgeTwoOfOneAt history)
      else none)
  by_cases htwo : G.TwoDeterminesOneAt history
  · have hswapDet :
        G.swapPlayers.OneDeterminesTwoAt (G.swapHistory history) :=
      (G.swap_oneDeterminesTwoAt_iff history).mpr htwo
    have hswapRank :
        G.swapPlayers.informationRankTwo (G.swapHistory history) ≠ 0 := by
      intro hzero
      have hnot :=
        (G.swapPlayers.informationRankTwo_eq_zero_iff
          (G.swapHistory history)).mp hzero
      exact hnot hswapDet
    unfold bridgeSignalTwoAt at hswap
    rw [if_neg hswapRank] at hswap
    rw [hswap, hrank]
    by_cases hone : G.OneDeterminesTwoAt history
    · have hrankZero := (G.informationRankOne_eq_zero_iff history).mpr hone
      simp [hrankZero,
        G.knowledgeTwoOfOneAt_eq_singleton_of_twoDetermines history htwo]
    · have hrankZero : G.informationRankOne history ≠ 0 := by
        exact fun h => hone ((G.informationRankOne_eq_zero_iff history).mp h)
      simp [hrankZero]
  · have hone : G.OneDeterminesTwoAt history :=
      (hhier history).resolve_right htwo
    have hswapNot :
        ¬ G.swapPlayers.OneDeterminesTwoAt (G.swapHistory history) := by
      rwa [G.swap_oneDeterminesTwoAt_iff]
    have hswapRank :
        G.swapPlayers.informationRankTwo (G.swapHistory history) = 0 :=
      (G.swapPlayers.informationRankTwo_eq_zero_iff
        (G.swapHistory history)).mpr hswapNot
    unfold bridgeSignalTwoAt at hswap
    rw [if_pos hswapRank] at hswap
    rw [G.swap_knowledgeOneOfTwoAt] at hswap
    rw [hswap, hrank]
    have hrankZero := (G.informationRankOne_eq_zero_iff history).mpr hone
    simp [hrankZero]

abbrev ReverseControllerOneMemory
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation1 G.Action1) :=
  Bool × controller.Memory × G.bridgeSignalOneMachine.Memory

noncomputable def reverseControllerOne
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation1 G.Action1) :
    MooreController.{u, u, u} G.Observation1 G.Action1 where
  Memory := G.ReverseControllerOneMemory controller
  memoryFinite := by infer_instance
  initial := (false, controller.initial, G.bridgeSignalOneMachine.initial)
  update memory observation :=
    let signalMemory :=
      G.bridgeSignalOneMachine.update memory.2.2 observation
    let originalLetter : G.crossingEliminationGame.Observation1 :=
      Sum.inl (observation, G.rankOneMachine.output signalMemory.2.1)
    let controllerMemory :=
      if memory.1 then
        controller.update
          (controller.update memory.2.1
            (Sum.inr (G.bridgeSignalOneMachine.output signalMemory)))
          originalLetter
      else controller.update memory.2.1 originalLetter
    (true, controllerMemory, signalMemory)
  output memory := controller.output memory.2.1

theorem reverseControllerOne_run
    (hhier : G.DynamicHierarchy)
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation1 G.Action1)
    (history : G.PlayHistory) :
    (G.reverseControllerOne controller).run history.observations1 =
      (true, controller.run (G.crossingLift history).observations1,
        G.bridgeSignalOneMachine.run history.observations1) := by
  induction history with
  | initial =>
      simp [reverseControllerOne, MooreController.run, crossingLift,
        crossingEliminationGame, bridgeSignalOneMachine, rankOneMachine,
        swapPlayers, bridgeSignalTwoMachine]
  | step previous actionOne actionTwo nature ih =>
      rw [PlayHistory.observations1_step,
        MooreController.run_append_singleton, ih]
      rw [crossingLift, PlayHistory.observations1_step,
        PlayHistory.observations1_step,
        MooreController.run_append_singleton,
        MooreController.run_append_singleton]
      let target := previous.step actionOne actionTwo nature
      have hrank := G.rankOneMachine_output_run target
      have hsignal := G.bridgeSignalOneMachine_output_run hhier target
      have hsignalMemory :
          G.bridgeSignalOneMachine.update
              (G.bridgeSignalOneMachine.run previous.observations1)
              (G.observe1
                (G.next previous.lastState actionOne actionTwo nature)) =
            G.bridgeSignalOneMachine.run target.observations1 := by
        rw [show target.observations1 = previous.observations1 ++
          [G.observe1 (G.next previous.lastState actionOne actionTwo nature)] by
            simp [target, PlayHistory.observations1_step]]
        exact (G.bridgeSignalOneMachine.run_append_singleton _ _).symm
      simp only [reverseControllerOne, if_true]
      rw [hsignalMemory, hsignal]
      have hrankMemory :
          (G.bridgeSignalOneMachine.run target.observations1).2.1 =
            G.rankOneMachine.run target.observations1 := by
        rw [G.bridgeSignalOneMachine_run_state]
      rw [hrankMemory, hrank]
      have hbridge := G.crossingBridgeLift_observe1 previous
        actionOne actionTwo nature
      have hbridge' :
          G.crossingEliminationGame.observe1
              (G.crossingBridgeLift previous actionOne actionTwo nature).lastState =
            Sum.inr
              (G.bridgeSignalOneAt target) := by
        simpa [bridgeSignalOneAt, target] using hbridge
      have horiginal := G.crossingLift_observe1 target
      change
        (true,
          controller.update
            (controller.update
              (controller.run (G.crossingLift previous).observations1)
              (Sum.inr
                (G.bridgeSignalOneAt target)))
            (Sum.inl (G.observe1 target.lastState,
              G.informationRankOne target)), _) = _
      change _ =
        (true,
          controller.update
            (controller.update
              (controller.run (G.crossingLift previous).observations1)
              (G.crossingEliminationGame.observe1
                (G.crossingBridgeLift previous actionOne actionTwo nature).lastState))
            (G.crossingEliminationGame.observe1
              (G.crossingLift target).lastState), _)
      rw [hbridge', horiginal]
      simp [target, PlayHistory.observations1_step,
        MooreController.run_append_singleton]

theorem reverseControllerOne_strategy
    (hhier : G.DynamicHierarchy)
    (controller : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation1 G.Action1)
    (history : G.PlayHistory) :
    (G.reverseControllerOne controller).strategy history.observations1 =
      controller.strategy (G.crossingLift history).observations1 := by
  unfold MooreController.strategy
  rw [G.reverseControllerOne_run hhier]
  rfl

/-- Two-sided reverse finite-state controller transport from the doubled arena
back to the original arena. -/
theorem exists_reverse_crossing_controller_transport
    (hhier : G.DynamicHierarchy)
    (controllerOne : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation1 G.Action1)
    (controllerTwo : MooreController.{u, u, u}
      G.crossingEliminationGame.Observation2 G.Action2) :
    ∃ (originalOne : MooreController.{u, u, u} G.Observation1 G.Action1)
      (originalTwo : MooreController.{u, u, u} G.Observation2 G.Action2),
      (∀ history : G.PlayHistory,
        originalOne.strategy history.observations1 =
          controllerOne.strategy (G.crossingLift history).observations1) ∧
      (∀ history : G.PlayHistory,
        originalTwo.strategy history.observations2 =
          controllerTwo.strategy (G.crossingLift history).observations2) := by
  exact ⟨G.reverseControllerOne controllerOne,
    G.reverseControllerTwo controllerTwo,
    G.reverseControllerOne_strategy hhier controllerOne,
    G.reverseControllerTwo_strategy hhier controllerTwo⟩

/-! ## Normal form of arbitrary doubled histories -/

/-- Operational correspondence between an arbitrary doubled history and its
underlying original history.  The actions attached to a bridge-to-original
step are intentionally discarded. -/
inductive CrossingRep :
    G.crossingEliminationGame.PlayHistory -> Bool -> G.PlayHistory -> Prop
  | initial : CrossingRep PlayHistory.initial false PlayHistory.initial
  | toBridge {doubled : G.crossingEliminationGame.PlayHistory}
      {history : G.PlayHistory}
      (rep : CrossingRep doubled false history)
      (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
      CrossingRep (doubled.step actionOne actionTwo nature) true
        (history.step actionOne actionTwo nature)
  | toOriginal {doubled : G.crossingEliminationGame.PlayHistory}
      {history : G.PlayHistory}
      (rep : CrossingRep doubled true history)
      (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
      CrossingRep (doubled.step actionOne actionTwo nature) false history

theorem crossingRep_phase_lastState
    {doubled : G.crossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (rep : G.CrossingRep doubled phase history) :
    doubled.lastState =
      (phase, history.lastState,
        G.rankOneMachine.run history.observations1,
        G.rankTwoMachine.run history.observations2) := by
  induction rep with
  | initial =>
      simp [crossingEliminationGame, MooreController.run,
        rankOneMachine, rankTwoMachine, PlayHistory.lastState,
        initialRankTwoBelief]
  | toBridge rep actionOne actionTwo nature ih =>
      change G.crossingEliminationGame.next _ actionOne actionTwo nature = _
      rw [ih]
      simp [crossingEliminationGame, crossingAdvance,
        PlayHistory.lastState, PlayHistory.observations1_step,
        PlayHistory.observations2_step]
  | toOriginal rep actionOne actionTwo nature ih =>
      change G.crossingEliminationGame.next _ actionOne actionTwo nature = _
      rw [ih]
      simp [crossingEliminationGame]

/-- Every generated doubled history has an original-history representation
and the phase is forced by its last state. -/
theorem exists_crossingRep
    (doubled : G.crossingEliminationGame.PlayHistory) :
    ∃ (phase : Bool) (history : G.PlayHistory),
      G.CrossingRep doubled phase history := by
  induction doubled with
  | initial => exact ⟨false, PlayHistory.initial, CrossingRep.initial⟩
  | step previous actionOne actionTwo nature ih =>
      obtain ⟨phase, history, rep⟩ := ih
      cases phase with
      | false =>
          exact ⟨true, history.step actionOne actionTwo nature,
            CrossingRep.toBridge rep actionOne actionTwo nature⟩
      | true =>
          exact ⟨false, history,
            CrossingRep.toOriginal rep actionOne actionTwo nature⟩

theorem crossingRep_phase_eq_lastState
    {doubled : G.crossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (rep : G.CrossingRep doubled phase history) :
    doubled.lastState.1 = phase := by
  rw [G.crossingRep_phase_lastState rep]

/-- Observation-history normal form corresponding to `CrossingRep`. -/
def CrossingRepObservationNormal
    {doubled : G.crossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (_rep : G.CrossingRep doubled phase history) : Prop :=
  if phase then
    ∃ (previous : G.PlayHistory) (actionOne : G.Action1)
      (actionTwo : G.Action2) (nature : G.Nature),
      history = previous.step actionOne actionTwo nature ∧
        doubled.observations1 =
          (G.crossingBridgeLift previous actionOne actionTwo nature).observations1 ∧
        doubled.observations2 =
          (G.crossingBridgeLift previous actionOne actionTwo nature).observations2
  else
    doubled.observations1 = (G.crossingLift history).observations1 ∧
      doubled.observations2 = (G.crossingLift history).observations2

theorem crossingRep_observation_normal
    {doubled : G.crossingEliminationGame.PlayHistory}
    {phase : Bool} {history : G.PlayHistory}
    (rep : G.CrossingRep doubled phase history) :
    G.CrossingRepObservationNormal rep := by
  induction rep with
  | initial =>
      simp [CrossingRepObservationNormal, crossingLift]
  | toBridge rep actionOne actionTwo nature ih =>
      simp only [CrossingRepObservationNormal, if_true]
      simp only [CrossingRepObservationNormal, Bool.false_eq_true,
        if_false] at ih
      refine ⟨_, actionOne, actionTwo, nature, rfl, ?_, ?_⟩
      · rw [PlayHistory.observations1_step, ih.1]
        rw [crossingBridgeLift, PlayHistory.observations1_step]
        congr 1
        rw [G.crossingRep_phase_lastState rep,
          G.crossingLift_lastState]
      · rw [PlayHistory.observations2_step, ih.2]
        rw [crossingBridgeLift, PlayHistory.observations2_step]
        congr 1
        rw [G.crossingRep_phase_lastState rep,
          G.crossingLift_lastState]
  | toOriginal rep actionOne actionTwo nature ih =>
      simp only [CrossingRepObservationNormal, if_true] at ih
      simp only [CrossingRepObservationNormal, Bool.false_eq_true, if_false]
      obtain ⟨previous, originalOne, originalTwo, originalNature,
        hhistory, hobsOne, hobsTwo⟩ := ih
      constructor
      · rw [PlayHistory.observations1_step, hobsOne]
        rw [hhistory, crossingLift, PlayHistory.observations1_step,
          PlayHistory.observations1_step]
        rw [crossingBridgeLift, PlayHistory.observations1_step]
        congr 2
        rw [G.crossingRep_phase_lastState rep]
        change _ = G.crossingEliminationGame.observe1
          (G.crossingEliminationGame.next
            (G.crossingBridgeLift previous originalOne originalTwo
              originalNature).lastState originalOne originalTwo originalNature)
        rw [G.crossingBridgeLift_lastState, hhistory]
        simp [crossingEliminationGame]
      · rw [PlayHistory.observations2_step, hobsTwo]
        rw [hhistory, crossingLift, PlayHistory.observations2_step,
          PlayHistory.observations2_step]
        rw [crossingBridgeLift, PlayHistory.observations2_step]
        congr 2
        rw [G.crossingRep_phase_lastState rep]
        change _ = G.crossingEliminationGame.observe2
          (G.crossingEliminationGame.next
            (G.crossingBridgeLift previous originalOne originalTwo
              originalNature).lastState originalOne originalTwo originalNature)
        rw [G.crossingBridgeLift_lastState, hhistory]
        simp [crossingEliminationGame]

theorem crossingRep_original_observations
    {doubled : G.crossingEliminationGame.PlayHistory}
    {history : G.PlayHistory}
    (rep : G.CrossingRep doubled false history) :
    doubled.observations1 = (G.crossingLift history).observations1 ∧
      doubled.observations2 = (G.crossingLift history).observations2 := by
  simpa [CrossingRepObservationNormal] using
    G.crossingRep_observation_normal rep

theorem crossingLift_rep (history : G.PlayHistory) :
    G.CrossingRep (G.crossingLift history) false history := by
  induction history with
  | initial => exact CrossingRep.initial
  | step previous actionOne actionTwo nature ih =>
      exact CrossingRep.toOriginal
        (CrossingRep.toBridge ih actionOne actionTwo nature)
        actionOne actionTwo nature

theorem crossingBridgeLift_rep
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.CrossingRep
      (G.crossingBridgeLift history actionOne actionTwo nature) true
      (history.step actionOne actionTwo nature) := by
  exact CrossingRep.toBridge (G.crossingLift_rep history)
    actionOne actionTwo nature

end FiniteConcurrentGame

end DistributedSynthesis
