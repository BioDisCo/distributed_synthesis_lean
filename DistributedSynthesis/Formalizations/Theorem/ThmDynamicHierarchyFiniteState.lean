/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Fintype.Basic

/-!
# Dynamic hierarchy and finite-state distributed strategies

This file states the game-theoretic boundary used by Theorem 10 of
Berwanger--Mathew--van den Bogaard in the form needed by the paper.

The important distinctions are explicit:

* hierarchy is a property of perfect-recall observation histories, not a
  pointwise refinement between two observation letters;
* the determining player may change with the history;
* the finite-state conclusion produces Moore controllers, not memoryless
  functions on the original observation alphabet;
* a bounded-delay hierarchy only determines a settled prefix and cannot be
  passed to the strict theorem.  A model application must first split off a
  finite current fringe, retain a strictly hierarchical non-fringe core, and
  compile the fringe into contingent actions.

The definitions below are independent of a particular solution algorithm.
`FiniteStateSynthesisCertificate` is the exact interface that a formalisation
of the cited shadow-player construction must construct.
-/

namespace DistributedSynthesis

universe u v w

/-- A finite Moore controller.  It updates its private memory with each new
observation and chooses its action from the resulting memory state. -/
structure MooreController (Observation : Type u) (Action : Type v) where
  Memory : Type w
  memoryFinite : Fintype Memory
  initial : Memory
  update : Memory -> Observation -> Memory
  output : Memory -> Action

attribute [instance] MooreController.memoryFinite

namespace MooreController

variable {Observation : Type u} {Action : Type v}
  (C : MooreController.{u, v, w} Observation Action)

/-- Memory reached after reading a finite observation history. -/
def run : List Observation -> C.Memory
  | [] => C.initial
  | observation :: observations =>
      (observations.foldl C.update) (C.update C.initial observation)

@[simp]
theorem run_nil : C.run [] = C.initial := rfl

/-- `run` is the ordinary left fold of the update function. -/
theorem run_eq_foldl (observations : List Observation) :
    C.run observations = observations.foldl C.update C.initial := by
  cases observations with
  | nil => rfl
  | cons observation observations => rfl

@[simp]
theorem run_append_singleton (observations : List Observation)
    (observation : Observation) :
    C.run (observations ++ [observation]) = C.update (C.run observations) observation := by
  simp [run_eq_foldl, List.foldl_append]

/-- The perfect-recall strategy implemented by the Moore controller. -/
def strategy (observations : List Observation) : Action :=
  C.output (C.run observations)

end MooreController

/-- A finite concurrent game for two cooperating players against Nature.
Nature is made explicit so that `next` is deterministic. -/
structure FiniteConcurrentGame where
  State : Type u
  Action1 : Type u
  Action2 : Type u
  Nature : Type u
  Observation1 : Type u
  Observation2 : Type u
  stateFinite : Fintype State
  action1Finite : Fintype Action1
  action2Finite : Fintype Action2
  natureFinite : Fintype Nature
  observation1Finite : Fintype Observation1
  observation2Finite : Fintype Observation2
  initial : State
  next : State -> Action1 -> Action2 -> Nature -> State
  observe1 : State -> Observation1
  observe2 : State -> Observation2
  priority : State -> Nat

attribute [instance]
  FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite
  FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite
  FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame)

/-- A legal finite history.  Action and Nature witnesses are retained only to
generate legal successor states; information equivalence below observes the
state sequence and deliberately ignores those witnesses. -/
inductive PlayHistory where
  | initial : PlayHistory
  | step : PlayHistory -> G.Action1 -> G.Action2 -> G.Nature -> PlayHistory

namespace PlayHistory

variable {G}

/-- Last state of a generated history. -/
def lastState : G.PlayHistory -> G.State
  | .initial => G.initial
  | .step history action1 action2 nature =>
      G.next history.lastState action1 action2 nature

/-- Position sequence of a generated history. -/
def states : G.PlayHistory -> List G.State
  | .initial => [G.initial]
  | .step history action1 action2 nature =>
      history.states ++ [G.next history.lastState action1 action2 nature]

/-- Player 1's perfect-recall observation sequence. -/
def observations1 (history : G.PlayHistory) : List G.Observation1 :=
  history.states.map G.observe1

/-- Player 2's perfect-recall observation sequence. -/
def observations2 (history : G.PlayHistory) : List G.Observation2 :=
  history.states.map G.observe2

@[simp]
theorem observations1_initial :
    (PlayHistory.initial (G := G)).observations1 = [G.observe1 G.initial] := rfl

@[simp]
theorem observations2_initial :
    (PlayHistory.initial (G := G)).observations2 = [G.observe2 G.initial] := rfl

@[simp]
theorem observations1_step (history : G.PlayHistory)
    (action1 : G.Action1) (action2 : G.Action2) (nature : G.Nature) :
    (history.step action1 action2 nature).observations1 =
      history.observations1 ++
        [G.observe1 (G.next history.lastState action1 action2 nature)] := by
  simp [observations1, states]

@[simp]
theorem observations2_step (history : G.PlayHistory)
    (action1 : G.Action1) (action2 : G.Action2) (nature : G.Nature) :
    (history.step action1 action2 nature).observations2 =
      history.observations2 ++
        [G.observe2 (G.next history.lastState action1 action2 nature)] := by
  simp [observations2, states]

end PlayHistory

/-- Player 1 has at least as much information as player 2 at `history` when
player 1's observation history determines player 2's observation history over
all legal histories.  Equivalently, player 1's information set is included in
player 2's. -/
def OneDeterminesTwoAt (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    alternative.observations1 = history.observations1 ->
      alternative.observations2 = history.observations2

/-- The symmetric information preorder at a history. -/
def TwoDeterminesOneAt (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    alternative.observations2 = history.observations2 ->
      alternative.observations1 = history.observations1

/-- Dynamic hierarchical information: after every legal history the two
perfect-recall information sets are comparable.  The direction may depend on
the history. -/
def DynamicHierarchy : Prop :=
  ∀ history : G.PlayHistory,
    G.OneDeterminesTwoAt history ∨ G.TwoDeterminesOneAt history

/-- The prefix outside a delay window. -/
def settledPrefix {α : Type u} (delay : Nat) (trace : List α) : List α :=
  trace.take (trace.length - delay)

@[simp]
theorem settledPrefix_zero {α : Type u} (trace : List α) :
    settledPrefix 0 trace = trace := by
  simp [settledPrefix]

/-- Player 1 determines player 2's observations outside the final `delay`
rounds. -/
def OneDeterminesTwoWithDelayAt (delay : Nat) (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    alternative.observations1 = history.observations1 ->
      settledPrefix delay alternative.observations2 =
        settledPrefix delay history.observations2

/-- Player 2 determines player 1's observations outside the final `delay`
rounds. -/
def TwoDeterminesOneWithDelayAt (delay : Nat) (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    alternative.observations2 = history.observations2 ->
      settledPrefix delay alternative.observations1 =
        settledPrefix delay history.observations1

/-- A bounded-delay hierarchy.  This does not itself imply dynamic hierarchy:
the unresolved suffix must first be represented by a finite fringe and removed
by contingent actions. -/
def BoundedDelayHierarchy (delay : Nat) : Prop :=
  ∀ history : G.PlayHistory,
    G.OneDeterminesTwoWithDelayAt delay history ∨
      G.TwoDeterminesOneWithDelayAt delay history

theorem boundedDelayHierarchy_zero_iff :
    G.BoundedDelayHierarchy 0 ↔ G.DynamicHierarchy := by
  simp only [BoundedDelayHierarchy, OneDeterminesTwoWithDelayAt,
    TwoDeterminesOneWithDelayAt, settledPrefix_zero, DynamicHierarchy,
    OneDeterminesTwoAt, TwoDeterminesOneAt]

/-- A general perfect-recall distributed strategy. -/
abbrev HistoryProductStrategy :=
  (List G.Observation1 -> G.Action1) ×
    (List G.Observation2 -> G.Action2)

/-- A pair of finite Moore controllers. -/
structure FiniteStateProductStrategy where
  one : MooreController.{u, u, u} G.Observation1 G.Action1
  two : MooreController.{u, u, u} G.Observation2 G.Action2

/-- Forget the finite implementation and expose the perfect-recall strategies
implemented by the two controllers. -/
def FiniteStateProductStrategy.toHistory
    (controller : G.FiniteStateProductStrategy) : G.HistoryProductStrategy :=
  (controller.one.strategy, controller.two.strategy)

/-- State and local observation histories reached after `n` rounds. -/
def strategyState (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : Nat ->
      G.State × List G.Observation1 × List G.Observation2
  | 0 => (G.initial, [G.observe1 G.initial], [G.observe2 G.initial])
  | n + 1 =>
      let previous := strategyState strategy nature n
      let nextState :=
        G.next previous.1 (strategy.1 previous.2.1)
          (strategy.2 previous.2.2) (nature n)
      (nextState, previous.2.1 ++ [G.observe1 nextState],
        previous.2.2 ++ [G.observe2 nextState])

/-- Priority `p` occurs infinitely often in a sequence. -/
def PriorityInfinitelyOften (priorities : Nat -> Nat) (p : Nat) : Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ priorities k = p

/-- The minimum priority occurring infinitely often is even. -/
def ParityAccepts (priorities : Nat -> Nat) : Prop :=
  ∃ p : Nat,
    p % 2 = 0 ∧ PriorityInfinitelyOften priorities p ∧
      ∀ q : Nat, PriorityInfinitelyOften priorities q -> p ≤ q

/-- A history strategy wins against every Nature sequence. -/
def HistoryStrategyWins (strategy : G.HistoryProductStrategy) : Prop :=
  ∀ nature : Nat -> G.Nature,
    ParityAccepts (fun n => G.priority (@strategyState G strategy nature n).1)

/-- A finite-state strategy wins through its induced perfect-recall strategy. -/
def FiniteStateStrategyWins (controller : G.FiniteStateProductStrategy) : Prop :=
  G.HistoryStrategyWins controller.toHistory

/-- Realizability by arbitrary perfect-recall distributed strategies. -/
def HistoryRealizable : Prop :=
  ∃ strategy : G.HistoryProductStrategy, G.HistoryStrategyWins strategy

/-- Realizability by finite Moore controllers. -/
def FiniteStateRealizable : Prop :=
  ∃ controller : G.FiniteStateProductStrategy,
    G.FiniteStateStrategyWins controller

theorem historyRealizable_of_finiteStateRealizable
    (hfinite : G.FiniteStateRealizable) : G.HistoryRealizable := by
  obtain ⟨controller, hcontroller⟩ := hfinite
  exact ⟨controller.toHistory, hcontroller⟩

/-- Exact output boundary of a constructive dynamic-hierarchy synthesis
formalisation.  `complete` is the finite-memory extraction; `decision` is the
effective synthesis result. -/
structure FiniteStateSynthesisCertificate where
  complete : G.HistoryRealizable -> G.FiniteStateRealizable
  decision : Decidable G.HistoryRealizable

attribute [instance] FiniteStateSynthesisCertificate.decision

theorem historyRealizable_iff_finiteStateRealizable
    (certificate : G.FiniteStateSynthesisCertificate) :
    G.HistoryRealizable ↔ G.FiniteStateRealizable := by
  constructor
  · exact certificate.complete
  · exact G.historyRealizable_of_finiteStateRealizable

end FiniteConcurrentGame

end DistributedSynthesis
