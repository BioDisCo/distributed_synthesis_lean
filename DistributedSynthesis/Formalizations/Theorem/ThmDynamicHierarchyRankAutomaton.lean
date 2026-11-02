/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyRankSignals
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Finite powerset automaton for the two-player information rank

This is the finite-state half of Lemma 11 in Berwanger--Mathew--van den
Bogaard.  On player one's observation history, the machine tracks all pairs of
legal histories with that observation history, together with a flag recording
whether their player-two observation histories have diverged.  Player one
determines player two exactly when no flagged pair remains reachable.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

/-- Every one-round successor of `state`, over all joint actions and Nature
choices. -/
noncomputable def allSuccessors (state : G.State) : Finset G.State := by
  classical
  exact Finset.univ.biUnion fun actionOne : G.Action1 =>
    Finset.univ.biUnion fun actionTwo : G.Action2 =>
      Finset.univ.image fun nature : G.Nature =>
        G.next state actionOne actionTwo nature

theorem mem_allSuccessors_iff {state nextState : G.State} :
    nextState ∈ G.allSuccessors state ↔
      ∃ (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature),
        nextState = G.next state actionOne actionTwo nature := by
  classical
  simp [allSuccessors, eq_comm]

/-- A pair of possible current states and whether player-two observations
have diverged somewhere along their histories. -/
abbrev RankPairState := G.State × G.State × Bool

/-- Determinized ambiguity state, represented by its finite characteristic
function. -/
abbrev RankBelief := G.RankPairState -> Bool

/-- Boolean divergence test for player-two observations. -/
noncomputable def observationTwoDiffers (left right : G.State) : Bool := by
  classical
  exact decide (G.observe2 left ≠ G.observe2 right)

/-- Initial pair after reading the common initial player-one observation. -/
noncomputable def initialRankBelief : G.RankBelief :=
  by
    classical
    exact fun pair => decide (pair = (G.initial, G.initial, false))

/-- Advance every pair through every pair of legal successors showing the
same supplied player-one observation; remember any player-two divergence. -/
noncomputable def rankBeliefStep
    (belief : G.RankBelief) (observation : G.Observation1) : G.RankBelief := by
  classical
  exact fun target => decide <|
    ∃ pair : G.RankPairState,
      belief pair = true ∧
        target.1 ∈ G.allSuccessors pair.1 ∧
        target.2.1 ∈ G.allSuccessors pair.2.1 ∧
        G.observe1 target.1 = observation ∧
        G.observe1 target.2.1 = observation ∧
        target.2.2 =
          (pair.2.2 || G.observationTwoDiffers target.1 target.2.1)

/-- Exact one-step semantics of the determinized pair automaton. -/
theorem rankBeliefStep_eq_true_iff
    (belief : G.RankBelief) (observation : G.Observation1)
    (target : G.RankPairState) :
    G.rankBeliefStep belief observation target = true ↔
      ∃ pair : G.RankPairState,
        belief pair = true ∧
          target.1 ∈ G.allSuccessors pair.1 ∧
          target.2.1 ∈ G.allSuccessors pair.2.1 ∧
          G.observe1 target.1 = observation ∧
          G.observe1 target.2.1 = observation ∧
          target.2.2 =
            (pair.2.2 ||
              G.observationTwoDiffers target.1 target.2.1) := by
  classical
  simp [rankBeliefStep]

@[simp]
theorem initialRankBelief_eq_true_iff (target : G.RankPairState) :
    G.initialRankBelief target = true ↔
      target = (G.initial, G.initial, false) := by
  classical
  simp [initialRankBelief]

/-- A determinized belief witnesses ambiguity once it contains a pair whose
player-two histories have diverged. -/
def rankBeliefAmbiguous (belief : G.RankBelief) : Prop :=
  ∃ pair, belief pair = true ∧ pair.2.2 = true

noncomputable instance (belief : G.RankBelief) :
    Decidable (G.rankBeliefAmbiguous belief) :=
  Classical.propDecidable _

/-- Memory of the rank machine: `none` before the first observation, then the
determinized pair belief. -/
abbrev RankMachineMemory := Option G.RankBelief

/-- The finite Moore machine computing player one's tie-broken information
rank.  The correctness theorem relating its output to `informationRankOne`
is proved after the pair-history invariant. -/
noncomputable def rankOneMachine :
    MooreController.{u, 0, u} G.Observation1 (Fin 2) where
  Memory := G.RankMachineMemory
  memoryFinite := by
    classical
    letI : DecidableEq G.State := Classical.decEq _
    letI : Fintype G.RankPairState := inferInstance
    letI : Fintype G.RankBelief := Pi.instFintype
    infer_instance
  initial := none
  update memory observation :=
    letI := Classical.decEq G.Observation1
    match memory with
    | none =>
        if observation = G.observe1 G.initial then some G.initialRankBelief
        else some (fun _ => false)
    | some belief => some (G.rankBeliefStep belief observation)
  output memory :=
    match memory with
    | none => 0
    | some belief => if G.rankBeliefAmbiguous belief then 1 else 0

@[simp]
theorem rankOneMachine_run_singleton_initial :
    G.rankOneMachine.run [G.observe1 G.initial] =
      some G.initialRankBelief := by
  simp [rankOneMachine, MooreController.run]

/-! ## Semantic invariant of the pair automaton -/

/-- Appending one observation to equal-length histories preserves the expected
Boolean divergence recurrence. -/
theorem decide_append_singleton_ne
    {X : Type*} [DecidableEq X]
    (left right : List X) (leftLast rightLast : X)
    (hlength : left.length = right.length) :
    decide (left ++ [leftLast] ≠ right ++ [rightLast]) =
      (decide (left ≠ right) || decide (leftLast ≠ rightLast)) := by
  classical
  by_cases hpast : left = right
  · subst right
    by_cases hlast : leftLast = rightLast <;> simp [hlast]
  · have happend : left ++ [leftLast] ≠ right ++ [rightLast] := by
      intro heq
      have hparts := List.append_inj' heq (by simp)
      exact hpast hparts.1
    simp [hpast, happend]

/-- The two observation histories of one generated play have the same
length. -/
theorem observations_length_eq (history : G.PlayHistory) :
    history.observations1.length = history.observations2.length := by
  simp [PlayHistory.observations1, PlayHistory.observations2]

theorem observations1_length_pos (history : G.PlayHistory) :
    0 < history.observations1.length := by
  cases history <;> simp [PlayHistory.observations1, PlayHistory.states]

/-- Boolean divergence of the two player-two observation histories carried by
a pair of generated histories. -/
noncomputable def historiesTwoDiffer
    (left right : G.PlayHistory) : Bool := by
  classical
  exact decide (left.observations2 ≠ right.observations2)

/-- The divergence bit carried by a pair of histories has exactly the same
one-step recurrence as `rankBeliefStep`. -/
theorem historiesTwoDiffer_step
    (left right : G.PlayHistory)
    (leftActionOne rightActionOne : G.Action1)
    (leftActionTwo rightActionTwo : G.Action2)
    (leftNature rightNature : G.Nature)
    (hlength : left.observations1.length = right.observations1.length) :
    G.historiesTwoDiffer
        (left.step leftActionOne leftActionTwo leftNature)
        (right.step rightActionOne rightActionTwo rightNature) =
      (G.historiesTwoDiffer left right ||
        G.observationTwoDiffers
          (G.next left.lastState leftActionOne leftActionTwo leftNature)
          (G.next right.lastState rightActionOne rightActionTwo rightNature)) := by
  classical
  unfold historiesTwoDiffer observationTwoDiffers
  rw [PlayHistory.observations2_step, PlayHistory.observations2_step]
  exact decide_append_singleton_ne left.observations2 right.observations2
    (G.observe2 (G.next left.lastState leftActionOne leftActionTwo leftNature))
    (G.observe2 (G.next right.lastState rightActionOne rightActionTwo rightNature))
    (by
      rw [← G.observations_length_eq left, ← G.observations_length_eq right]
      exact hlength)

/-- Semantic meaning of one reachable pair-automaton state after reading a
player-one observation word. -/
def RankPairWitness (observations : List G.Observation1)
    (pair : G.RankPairState) : Prop :=
  ∃ left right : G.PlayHistory,
    left.observations1 = observations ∧
      right.observations1 = observations ∧
      left.lastState = pair.1 ∧
      right.lastState = pair.2.1 ∧
      pair.2.2 = G.historiesTwoDiffer left right

/-- Soundness of one determinized transition with respect to the pair-history
semantics. -/
theorem rankBeliefStep_witness_forward
    (belief : G.RankBelief) (observations : List G.Observation1)
    (observation : G.Observation1)
    (hinvariant : ∀ pair, belief pair = true ->
      G.RankPairWitness observations pair)
    (target : G.RankPairState)
    (htarget : G.rankBeliefStep belief observation target = true) :
    G.RankPairWitness (observations ++ [observation]) target := by
  classical
  obtain ⟨pair, hpair, hsuccOne, hsuccTwo, hobsOne, hobsTwo, hflag⟩ :=
    (G.rankBeliefStep_eq_true_iff belief observation target).mp htarget
  obtain ⟨left, right, hleftObs, hrightObs, hleftState,
    hrightState, hpairFlag⟩ := hinvariant pair hpair
  obtain ⟨leftActionOne, leftActionTwo, leftNature, hleftSucc⟩ :=
    (G.mem_allSuccessors_iff).mp hsuccOne
  obtain ⟨rightActionOne, rightActionTwo, rightNature, hrightSucc⟩ :=
    (G.mem_allSuccessors_iff).mp hsuccTwo
  refine
    ⟨left.step leftActionOne leftActionTwo leftNature,
      right.step rightActionOne rightActionTwo rightNature, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PlayHistory.observations1_step, hleftObs]
    congr 1
    rw [hleftState, ← hleftSucc]
    exact congrArg (fun x => [x]) hobsOne
  · rw [PlayHistory.observations1_step, hrightObs]
    congr 1
    rw [hrightState, ← hrightSucc]
    exact congrArg (fun x => [x]) hobsTwo
  · change G.next left.lastState leftActionOne leftActionTwo leftNature = target.1
    rw [hleftState, ← hleftSucc]
  · change
      G.next right.lastState rightActionOne rightActionTwo rightNature = target.2.1
    rw [hrightState, ← hrightSucc]
  · calc
      target.2.2 = (pair.2.2 ||
          G.observationTwoDiffers target.1 target.2.1) := hflag
      _ = (pair.2.2 ||
          G.observationTwoDiffers
            (G.next left.lastState leftActionOne leftActionTwo leftNature)
            (G.next right.lastState rightActionOne rightActionTwo rightNature)) := by
            rw [hleftState, hrightState, ← hleftSucc, ← hrightSucc]
      _ = (G.historiesTwoDiffer left right ||
          G.observationTwoDiffers
            (G.next left.lastState leftActionOne leftActionTwo leftNature)
            (G.next right.lastState rightActionOne rightActionTwo rightNature)) := by
            rw [hpairFlag]
      _ = G.historiesTwoDiffer
          (left.step leftActionOne leftActionTwo leftNature)
          (right.step rightActionOne rightActionTwo rightNature) :=
            (G.historiesTwoDiffer_step left right leftActionOne rightActionOne
              leftActionTwo rightActionTwo leftNature rightNature
              (by rw [hleftObs, hrightObs])).symm

/-- A history whose observation word is a nonempty word extended by one symbol
has a unique last generated step at the level needed by the automaton
invariant. -/
theorem exists_step_of_observations1_eq_append
    (history : G.PlayHistory) (observations : List G.Observation1)
    (observation : G.Observation1) (hnonempty : 0 < observations.length)
    (hobs : history.observations1 = observations ++ [observation]) :
    ∃ (previous : G.PlayHistory) (actionOne : G.Action1)
      (actionTwo : G.Action2) (nature : G.Nature),
      history = previous.step actionOne actionTwo nature ∧
        previous.observations1 = observations ∧
        G.observe1 (G.next previous.lastState actionOne actionTwo nature) =
          observation := by
  cases history with
  | initial =>
      exfalso
      have hlen := congrArg List.length hobs
      simp only [PlayHistory.observations1_initial, List.length_singleton,
        List.length_append] at hlen
      omega
  | step previous actionOne actionTwo nature =>
      have hobs' := hobs
      rw [PlayHistory.observations1_step] at hobs'
      obtain ⟨hprevious, hlast⟩ := List.append_inj' hobs' (by simp)
      refine ⟨previous, actionOne, actionTwo, nature, rfl, hprevious, ?_⟩
      simpa using hlast

/-- Completeness of one determinized transition with respect to the
pair-history semantics. -/
theorem rankBeliefStep_witness_backward
    (belief : G.RankBelief) (observations : List G.Observation1)
    (observation : G.Observation1) (hnonempty : 0 < observations.length)
    (hinvariant : ∀ pair, G.RankPairWitness observations pair ->
      belief pair = true)
    (target : G.RankPairState)
    (htarget : G.RankPairWitness (observations ++ [observation]) target) :
    G.rankBeliefStep belief observation target = true := by
  classical
  obtain ⟨left, right, hleftObs, hrightObs, hleftState,
    hrightState, hflag⟩ := htarget
  obtain ⟨leftPrevious, leftActionOne, leftActionTwo, leftNature,
    rfl, hleftPreviousObs, hleftLastObs⟩ :=
      G.exists_step_of_observations1_eq_append left observations observation
        hnonempty hleftObs
  obtain ⟨rightPrevious, rightActionOne, rightActionTwo, rightNature,
    rfl, hrightPreviousObs, hrightLastObs⟩ :=
      G.exists_step_of_observations1_eq_append right observations observation
        hnonempty hrightObs
  let predecessor : G.RankPairState :=
    (leftPrevious.lastState, rightPrevious.lastState,
      G.historiesTwoDiffer leftPrevious rightPrevious)
  apply (G.rankBeliefStep_eq_true_iff belief observation target).mpr
  refine ⟨predecessor, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hinvariant predecessor
    exact
      ⟨leftPrevious, rightPrevious, hleftPreviousObs, hrightPreviousObs,
        rfl, rfl, rfl⟩
  · apply (G.mem_allSuccessors_iff).mpr
    exact ⟨leftActionOne, leftActionTwo, leftNature, hleftState.symm⟩
  · apply (G.mem_allSuccessors_iff).mpr
    exact ⟨rightActionOne, rightActionTwo, rightNature, hrightState.symm⟩
  · rw [← hleftState]
    exact hleftLastObs
  · rw [← hrightState]
    exact hrightLastObs
  · change target.2.2 =
      (G.historiesTwoDiffer leftPrevious rightPrevious ||
        G.observationTwoDiffers target.1 target.2.1)
    have hleftNext :
        G.next leftPrevious.lastState leftActionOne leftActionTwo leftNature =
          target.1 := by
      exact hleftState
    have hrightNext :
        G.next rightPrevious.lastState rightActionOne rightActionTwo rightNature =
          target.2.1 := by
      exact hrightState
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
            leftNature rightNature
            (by rw [hleftPreviousObs, hrightPreviousObs])
      _ = (G.historiesTwoDiffer leftPrevious rightPrevious ||
          G.observationTwoDiffers target.1 target.2.1) := by
            rw [hleftNext, hrightNext]

/-- Exact preservation of the pair-history invariant by one observation. -/
theorem rankBeliefStep_witness_iff
    (belief : G.RankBelief) (observations : List G.Observation1)
    (observation : G.Observation1) (hnonempty : 0 < observations.length)
    (hinvariant : ∀ pair, belief pair = true ↔
      G.RankPairWitness observations pair)
    (target : G.RankPairState) :
    G.rankBeliefStep belief observation target = true ↔
      G.RankPairWitness (observations ++ [observation]) target := by
  constructor
  · exact G.rankBeliefStep_witness_forward belief observations observation
      (fun pair h => (hinvariant pair).mp h) target
  · exact G.rankBeliefStep_witness_backward belief observations observation
      hnonempty (fun pair h => (hinvariant pair).mpr h) target

/-- Iterating the determinized transition preserves the exact pair-history
semantics over an arbitrary suffix of observations. -/
theorem rankBelief_fold_witness_iff
    (belief : G.RankBelief) (observations suffix : List G.Observation1)
    (hnonempty : 0 < observations.length)
    (hinvariant : ∀ pair, belief pair = true ↔
      G.RankPairWitness observations pair)
    (target : G.RankPairState) :
    (suffix.foldl G.rankBeliefStep belief) target = true ↔
      G.RankPairWitness (observations ++ suffix) target := by
  induction suffix generalizing belief observations with
  | nil => simpa using hinvariant target
  | cons observation suffix ih =>
      rw [List.foldl_cons]
      have hstep := G.rankBeliefStep_witness_iff belief observations observation
        hnonempty hinvariant
      have hnonempty' : 0 < (observations ++ [observation]).length := by
        simp
      have htail := ih (G.rankBeliefStep belief observation)
        (observations ++ [observation]) hnonempty' hstep
      simpa [List.append_assoc] using htail

/-- At the one-symbol initial observation word, the characteristic initial
belief has exactly the intended pair-history semantics. -/
theorem initialRankBelief_witness_iff (target : G.RankPairState) :
    G.initialRankBelief target = true ↔
      G.RankPairWitness [G.observe1 G.initial] target := by
  rw [G.initialRankBelief_eq_true_iff]
  constructor
  · rintro rfl
    refine
      ⟨PlayHistory.initial, PlayHistory.initial, rfl, rfl, rfl, rfl, ?_⟩
    simp [historiesTwoDiffer]
  · rintro ⟨left, right, hleftObs, hrightObs, hleftState,
      hrightState, hflag⟩
    have hleftInitial : left = PlayHistory.initial := by
      cases left with
      | initial => rfl
      | step previous actionOne actionTwo nature =>
          exfalso
          have hobs := hleftObs
          rw [PlayHistory.observations1_step] at hobs
          have hpos := G.observations1_length_pos previous
          have hlen : previous.observations1.length + 1 = 1 := by
            calc
              previous.observations1.length + 1 =
                  (previous.observations1 ++
                    [G.observe1
                      (G.next previous.lastState actionOne actionTwo nature)]).length := by
                    simp
              _ = [G.observe1 G.initial].length :=
                congrArg List.length hobs
              _ = 1 := rfl
          omega
    have hrightInitial : right = PlayHistory.initial := by
      cases right with
      | initial => rfl
      | step previous actionOne actionTwo nature =>
          exfalso
          have hobs := hrightObs
          rw [PlayHistory.observations1_step] at hobs
          have hpos := G.observations1_length_pos previous
          have hlen : previous.observations1.length + 1 = 1 := by
            calc
              previous.observations1.length + 1 =
                  (previous.observations1 ++
                    [G.observe1
                      (G.next previous.lastState actionOne actionTwo nature)]).length := by
                    simp
              _ = [G.observe1 G.initial].length :=
                congrArg List.length hobs
              _ = 1 := rfl
          omega
    subst left
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

/-- Folding the rank machine from an already initialized belief is just the
fold of `rankBeliefStep`, wrapped in `some`. -/
theorem rankOneMachine_foldl_some
    (suffix : List G.Observation1) (belief : G.RankBelief) :
    suffix.foldl G.rankOneMachine.update (some belief) =
      some (suffix.foldl G.rankBeliefStep belief) := by
  induction suffix generalizing belief with
  | nil => rfl
  | cons observation suffix ih =>
      simp only [List.foldl_cons]
      change suffix.foldl G.rankOneMachine.update
          (some (G.rankBeliefStep belief observation)) = _
      exact ih (G.rankBeliefStep belief observation)

/-- Exact rank-machine memory after an observation word beginning with the
mandatory initial observation. -/
theorem rankOneMachine_run_initial_cons (suffix : List G.Observation1) :
    G.rankOneMachine.run (G.observe1 G.initial :: suffix) =
      some (suffix.foldl G.rankBeliefStep G.initialRankBelief) := by
  rw [MooreController.run_eq_foldl]
  simp only [List.foldl_cons]
  have hinitial :
      G.rankOneMachine.update G.rankOneMachine.initial
          (G.observe1 G.initial) = some G.initialRankBelief := by
    simp [rankOneMachine]
  rw [hinitial]
  exact G.rankOneMachine_foldl_some suffix G.initialRankBelief

/-- Every generated observation history begins with the initial state's
observation. -/
theorem exists_observations1_tail (history : G.PlayHistory) :
    ∃ suffix, history.observations1 = G.observe1 G.initial :: suffix := by
  induction history with
  | initial => exact ⟨[], rfl⟩
  | step previous actionOne actionTwo nature ih =>
      obtain ⟨suffix, hsuffix⟩ := ih
      refine
        ⟨suffix ++
          [G.observe1 (G.next previous.lastState actionOne actionTwo nature)], ?_⟩
      rw [PlayHistory.observations1_step, hsuffix]
      simp

/-- Full run invariant: after any generated history, the Moore memory is the
characteristic set of exactly the pairs of legal histories in player one's
information class, with the correct player-two divergence flag. -/
theorem rankOneMachine_run_witness_iff (history : G.PlayHistory) :
    ∃ belief : G.RankBelief,
      G.rankOneMachine.run history.observations1 = some belief ∧
        ∀ target, belief target = true ↔
          G.RankPairWitness history.observations1 target := by
  obtain ⟨suffix, hsuffix⟩ := G.exists_observations1_tail history
  let belief := suffix.foldl G.rankBeliefStep G.initialRankBelief
  refine ⟨belief, ?_, fun target => ?_⟩
  · rw [hsuffix]
    exact G.rankOneMachine_run_initial_cons suffix
  · have hfold := G.rankBelief_fold_witness_iff G.initialRankBelief
      [G.observe1 G.initial] suffix (by simp)
      (fun pair => initialRankBelief_witness_iff (G := G) pair) target
    simpa [belief, hsuffix] using hfold

/-- A belief satisfying the pair-history invariant is ambiguous exactly when
player one does not determine player two at the represented history. -/
theorem rankBeliefAmbiguous_iff_not_oneDeterminesTwoAt
    (history : G.PlayHistory) (belief : G.RankBelief)
    (hinvariant : ∀ target, belief target = true ↔
      G.RankPairWitness history.observations1 target) :
    G.rankBeliefAmbiguous belief ↔ ¬ G.OneDeterminesTwoAt history := by
  classical
  constructor
  · rintro ⟨pair, hpair, hflag⟩ hdetermines
    obtain ⟨left, right, hleftObs, hrightObs, -, -, hpairFlag⟩ :=
      (hinvariant pair).mp hpair
    have hleftTwo := hdetermines left hleftObs
    have hrightTwo := hdetermines right hrightObs
    have hdifferent : left.observations2 ≠ right.observations2 := by
      have : G.historiesTwoDiffer left right = true := by
        rw [← hpairFlag]
        exact hflag
      simpa [historiesTwoDiffer] using this
    exact hdifferent (hleftTwo.trans hrightTwo.symm)
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
    refine ⟨history, alternative, rfl, hsameOne, rfl, rfl, ?_⟩
    simp [target, historiesTwoDiffer, hdifferentTwo']

/-- The finite Moore machine computes player one's semantic tie-broken rank
on every generated play history. -/
theorem rankOneMachine_output_run (history : G.PlayHistory) :
    G.rankOneMachine.output
        (G.rankOneMachine.run history.observations1) =
      G.informationRankOne history := by
  obtain ⟨belief, hrun, hinvariant⟩ :=
    G.rankOneMachine_run_witness_iff history
  rw [hrun]
  have hambiguous :=
    G.rankBeliefAmbiguous_iff_not_oneDeterminesTwoAt history belief hinvariant
  unfold rankOneMachine informationRankOne
  by_cases hdetermines : G.OneDeterminesTwoAt history
  · have : ¬ G.rankBeliefAmbiguous belief := by
      simpa [hambiguous] using hdetermines
    simp [hdetermines, this]
  · have : G.rankBeliefAmbiguous belief := hambiguous.mpr hdetermines
    simp [hdetermines, this]

end FiniteConcurrentGame

end DistributedSynthesis
