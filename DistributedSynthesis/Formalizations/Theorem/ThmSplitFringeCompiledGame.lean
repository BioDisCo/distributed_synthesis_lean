/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmFringeCompiledGame

/-!
# Split-fringe compilation

This is the finite-fringe reduction that must precede an application of the
strict dynamic-hierarchy theorem.  It is deliberately different from delaying
an entire observation stream.

An observation is split into a current **core** and a finite **fringe**.  The
compiled game keeps the current core as the player's ordinary observation and
moves only the fringe into a contingent action `Fringe -> Action`.  Past fringe
values must be recoverable from the current core history and the current fringe;
this is the non-accumulation hypothesis of finite-fringe elimination.  The
resulting game is finite, has exactly the core perfect-recall information, and
is realizability-equivalent to the original game.

Consequently Berwanger--Mathew--van den Bogaard Theorem 10 is used only after
`CoreHierarchy` has proved strict hierarchy of the compiled game.  Neither a
delay hierarchy nor a delayed observation is passed to that theorem.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

/-- A finite observation projection with non-accumulating fringe.  The split
need not be onto a Cartesian product: the model's core/receipt pairs have
unreachable combinations.  The recovery laws are required only on legal game
histories, which is exactly what strategy transport uses. -/
structure FringeDecomposition where
  Core1 : Type u
  Core2 : Type u
  Fringe1 : Type u
  Fringe2 : Type u
  core1Finite : Fintype Core1
  core2Finite : Fintype Core2
  fringe1Finite : Fintype Fringe1
  fringe2Finite : Fintype Fringe2
  split1 : G.Observation1 → Core1 × Fringe1
  split2 : G.Observation2 → Core2 × Fringe2
  recover1 : List Core1 -> Fringe1 -> List G.Observation1
  recover2 : List Core2 -> Fringe2 -> List G.Observation2
  recover1_correct : ∀ history : G.PlayHistory,
    recover1 (history.observations1.map fun o => (split1 o).1)
        (split1 (G.observe1 history.lastState)).2 = history.observations1
  recover2_correct : ∀ history : G.PlayHistory,
    recover2 (history.observations2.map fun o => (split2 o).1)
        (split2 (G.observe2 history.lastState)).2 = history.observations2

namespace FringeDecomposition

variable {G} (D : G.FringeDecomposition)

instance : Fintype D.Core1 := D.core1Finite
instance : Fintype D.Core2 := D.core2Finite
instance : Fintype D.Fringe1 := D.fringe1Finite
instance : Fintype D.Fringe2 := D.fringe2Finite

/-- The core component of player one's observation. -/
def core1 (observation : G.Observation1) : D.Core1 := (D.split1 observation).1

/-- The fringe component of player one's observation. -/
def fringe1 (observation : G.Observation1) : D.Fringe1 := (D.split1 observation).2

/-- Player two's core component. -/
def core2 (observation : G.Observation2) : D.Core2 := (D.split2 observation).1

/-- Player two's fringe component. -/
def fringe2 (observation : G.Observation2) : D.Fringe2 := (D.split2 observation).2

/-- The compiled game observes current non-fringe cores and commits a response
for every possible current fringe value. -/
noncomputable def compiled : FiniteConcurrentGame.{u} where
  State := G.State
  Action1 := D.Fringe1 -> G.Action1
  Action2 := D.Fringe2 -> G.Action2
  Nature := G.Nature
  Observation1 := D.Core1
  Observation2 := D.Core2
  stateFinite := G.stateFinite
  action1Finite := @Pi.instFintype _ _ (Classical.decEq _) D.fringe1Finite
    (fun _ => G.action1Finite)
  action2Finite := @Pi.instFintype _ _ (Classical.decEq _) D.fringe2Finite
    (fun _ => G.action2Finite)
  natureFinite := G.natureFinite
  observation1Finite := D.core1Finite
  observation2Finite := D.core2Finite
  initial := G.initial
  next state action1 action2 nature :=
    G.next state
      (action1 (D.fringe1 (G.observe1 state)))
      (action2 (D.fringe2 (G.observe2 state))) nature
  observe1 state := D.core1 (G.observe1 state)
  observe2 state := D.core2 (G.observe2 state)
  priority := G.priority

@[simp] theorem compiled_initial : D.compiled.initial = G.initial := rfl

@[simp] theorem compiled_next (state : D.compiled.State)
    (action1 : D.compiled.Action1) (action2 : D.compiled.Action2)
    (nature : D.compiled.Nature) :
    D.compiled.next state action1 action2 nature =
      G.next state
        (action1 (D.fringe1 (G.observe1 state)))
        (action2 (D.fringe2 (G.observe2 state))) nature := rfl

@[simp] theorem compiled_observe1 (state : D.compiled.State) :
    D.compiled.observe1 state = D.core1 (G.observe1 state) := rfl

@[simp] theorem compiled_observe2 (state : D.compiled.State) :
    D.compiled.observe2 state = D.core2 (G.observe2 state) := rfl

@[simp] theorem compiled_priority (state : D.compiled.State) :
    D.compiled.priority state = G.priority state := rfl

/-- Resolve every contingent move at the fringe of the current state. -/
def toBase (D : G.FringeDecomposition) : D.compiled.PlayHistory -> G.PlayHistory
  | .initial => .initial
  | .step history action1 action2 nature =>
      .step (D.toBase history)
        (action1 (D.fringe1 (G.observe1 (D.toBase history).lastState)))
        (action2 (D.fringe2 (G.observe2 (D.toBase history).lastState))) nature

/-- Embed a base history using constant contingent tables. -/
def ofBase (D : G.FringeDecomposition) : G.PlayHistory -> D.compiled.PlayHistory
  | .initial => .initial
  | .step history action1 action2 nature =>
      .step (D.ofBase history) (fun _ => action1) (fun _ => action2) nature

@[simp] theorem toBase_ofBase (history : G.PlayHistory) :
    D.toBase (D.ofBase history) = history := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      simp [ofBase, toBase, ih]

/-- The compiled and resolved histories have the same last state. -/
theorem toBase_lastState (history : D.compiled.PlayHistory) :
    history.lastState = (D.toBase history).lastState := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      show D.compiled.next history.lastState action1 action2 nature = _
      simp only [compiled_next, toBase, PlayHistory.lastState, ih]

/-- Compiled observations are exactly the core projection of base observations. -/
theorem compiled_observations1 (history : D.compiled.PlayHistory) :
    history.observations1 =
      (D.toBase history).observations1.map D.core1 := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      rw [PlayHistory.observations1_step, ih]
      simp only [toBase, PlayHistory.observations1_step, List.map_append]
      simp [D.toBase_lastState history]
      rfl

/-- Mirror of `compiled_observations1`. -/
theorem compiled_observations2 (history : D.compiled.PlayHistory) :
    history.observations2 =
      (D.toBase history).observations2.map D.core2 := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      rw [PlayHistory.observations2_step, ih]
      simp only [toBase, PlayHistory.observations2_step, List.map_append]
      simp [D.toBase_lastState history]
      rfl

/-- Strict determination on the non-fringe core histories. -/
def OneCoreDeterminesTwoAt (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    alternative.observations1.map D.core1 = history.observations1.map D.core1 ->
      alternative.observations2.map D.core2 = history.observations2.map D.core2

/-- Mirror core determination. -/
def TwoCoreDeterminesOneAt (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    alternative.observations2.map D.core2 = history.observations2.map D.core2 ->
      alternative.observations1.map D.core1 = history.observations1.map D.core1

/-- Dynamic hierarchy of the accumulated non-fringe core histories. -/
def CoreHierarchy : Prop :=
  ∀ history : G.PlayHistory,
    D.OneCoreDeterminesTwoAt history ∨ D.TwoCoreDeterminesOneAt history

theorem compiled_oneDeterminesTwoAt_iff (history : D.compiled.PlayHistory) :
    D.compiled.OneDeterminesTwoAt history ↔
      D.OneCoreDeterminesTwoAt (D.toBase history) := by
  constructor
  · intro hdet alternative halt
    have hobs : (D.ofBase alternative).observations1 = history.observations1 := by
      rw [D.compiled_observations1, D.compiled_observations1,
        D.toBase_ofBase, halt]
    have := hdet (D.ofBase alternative) hobs
    rw [D.compiled_observations2, D.compiled_observations2,
      D.toBase_ofBase] at this
    exact this
  · intro hdet alternative halt
    rw [D.compiled_observations1, D.compiled_observations1] at halt
    have hcore := hdet (D.toBase alternative) halt
    rw [D.compiled_observations2, D.compiled_observations2, hcore]

theorem compiled_twoDeterminesOneAt_iff (history : D.compiled.PlayHistory) :
    D.compiled.TwoDeterminesOneAt history ↔
      D.TwoCoreDeterminesOneAt (D.toBase history) := by
  constructor
  · intro hdet alternative halt
    have hobs : (D.ofBase alternative).observations2 = history.observations2 := by
      rw [D.compiled_observations2, D.compiled_observations2,
        D.toBase_ofBase, halt]
    have := hdet (D.ofBase alternative) hobs
    rw [D.compiled_observations1, D.compiled_observations1,
      D.toBase_ofBase] at this
    exact this
  · intro hdet alternative halt
    rw [D.compiled_observations2, D.compiled_observations2] at halt
    have hcore := hdet (D.toBase alternative) halt
    rw [D.compiled_observations1, D.compiled_observations1, hcore]

/-- The compiled game is strictly dynamically hierarchical exactly when the
accumulated core histories are. -/
theorem compiled_dynamicHierarchy_iff :
    D.compiled.DynamicHierarchy ↔ D.CoreHierarchy := by
  constructor
  · intro hhier history
    rcases hhier (D.ofBase history) with hone | htwo
    · left
      simpa using (D.compiled_oneDeterminesTwoAt_iff (D.ofBase history)).mp hone
    · right
      simpa using (D.compiled_twoDeterminesOneAt_iff (D.ofBase history)).mp htwo
  · intro hhier history
    rcases hhier (D.toBase history) with hone | htwo
    · exact Or.inl ((D.compiled_oneDeterminesTwoAt_iff history).mpr hone)
    · exact Or.inr ((D.compiled_twoDeterminesOneAt_iff history).mpr htwo)

/-- A base strategy is simulated when its action on every legal observation
history is the compiled table evaluated at the actual current fringe. -/
def Simulates (strategy : G.HistoryProductStrategy)
    (compiled : D.compiled.HistoryProductStrategy) : Prop :=
  (∀ history : G.PlayHistory,
      strategy.1 history.observations1 =
        compiled.1 (history.observations1.map D.core1)
          (D.fringe1 (G.observe1 history.lastState))) ∧
    (∀ history : G.PlayHistory,
      strategy.2 history.observations2 =
        compiled.2 (history.observations2.map D.core2)
          (D.fringe2 (G.observe2 history.lastState)))

/-- Compile a base perfect-recall strategy using past-fringe recovery. -/
def contingentifyStrategy (strategy : G.HistoryProductStrategy) :
    D.compiled.HistoryProductStrategy :=
  (fun cores fringe => strategy.1 (D.recover1 cores fringe),
    fun cores fringe => strategy.2 (D.recover2 cores fringe))

/-- Read a compiled contingent strategy back on full observations. -/
def realizeStrategy (compiled : D.compiled.HistoryProductStrategy) :
    G.HistoryProductStrategy :=
  (fun observations =>
      let current := observations.getLastD (G.observe1 G.initial)
      compiled.1 (observations.map D.core1) (D.fringe1 current),
    fun observations =>
      let current := observations.getLastD (G.observe2 G.initial)
      compiled.2 (observations.map D.core2) (D.fringe2 current))

theorem simulates_contingentify (strategy : G.HistoryProductStrategy) :
    D.Simulates strategy (D.contingentifyStrategy strategy) := by
  constructor <;> intro history
  · exact congrArg strategy.1 (D.recover1_correct history).symm
  · exact congrArg strategy.2 (D.recover2_correct history).symm

theorem observations1_getLastD (history : G.PlayHistory) :
    history.observations1.getLastD (G.observe1 G.initial) =
      G.observe1 history.lastState := by
  rw [G.observations1_settled_concat history]
  simp

theorem observations2_getLastD (history : G.PlayHistory) :
    history.observations2.getLastD (G.observe2 G.initial) =
      G.observe2 history.lastState := by
  rw [G.observations2_settled_concat history]
  simp

theorem simulates_realize (compiled : D.compiled.HistoryProductStrategy) :
    D.Simulates (D.realizeStrategy compiled) compiled := by
  constructor <;> intro history
  · unfold realizeStrategy
    change compiled.1 (history.observations1.map D.core1)
      (D.fringe1 (history.observations1.getLastD (G.observe1 G.initial))) = _
    rw [observations1_getLastD (G := G) history]
  · unfold realizeStrategy
    change compiled.2 (history.observations2.map D.core2)
      (D.fringe2 (history.observations2.getLastD (G.observe2 G.initial))) = _
    rw [observations2_getLastD (G := G) history]

/-- The legal history generated by a strategy and a Nature word. -/
def strategyHistory (D : G.FringeDecomposition)
    (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : Nat -> G.PlayHistory
  | 0 => .initial
  | n + 1 =>
      let history := D.strategyHistory strategy nature n
      .step history (strategy.1 history.observations1)
        (strategy.2 history.observations2) (nature n)

theorem strategyHistory_data (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (D.strategyHistory strategy nature n).lastState =
        (G.strategyState strategy nature n).1 ∧
      (D.strategyHistory strategy nature n).observations1 =
        (G.strategyState strategy nature n).2.1 ∧
      (D.strategyHistory strategy nature n).observations2 =
        (G.strategyState strategy nature n).2.2 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      obtain ⟨hstate, hone, htwo⟩ := ih
      simp only [strategyHistory, strategyState, PlayHistory.lastState,
        PlayHistory.observations1_step, PlayHistory.observations2_step]
      rw [hstate, hone, htwo]
      exact ⟨rfl, rfl, rfl⟩

/-- Simulating strategies produce the same state sequence; the compiled
observation histories are the core projections. -/
theorem compiled_strategyState (strategy : G.HistoryProductStrategy)
    (compiled : D.compiled.HistoryProductStrategy)
    (hsim : D.Simulates strategy compiled)
    (nature : Nat -> G.Nature) (n : Nat) :
    (D.compiled.strategyState compiled nature n).1 =
        (G.strategyState strategy nature n).1 ∧
      (D.compiled.strategyState compiled nature n).2.1 =
        (G.strategyState strategy nature n).2.1.map D.core1 ∧
      (D.compiled.strategyState compiled nature n).2.2 =
        (G.strategyState strategy nature n).2.2.map D.core2 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      obtain ⟨hstate, hone, htwo⟩ := ih
      let history := D.strategyHistory strategy nature n
      obtain ⟨hhstate, hhone, hhtwo⟩ := D.strategyHistory_data strategy nature n
      have hact1 :
          compiled.1 (D.compiled.strategyState compiled nature n).2.1
              (D.fringe1 (G.observe1 (G.strategyState strategy nature n).1)) =
            strategy.1 (G.strategyState strategy nature n).2.1 := by
        rw [hone, ← hhone, ← hhstate]
        exact (hsim.1 history).symm
      have hact2 :
          compiled.2 (D.compiled.strategyState compiled nature n).2.2
              (D.fringe2 (G.observe2 (G.strategyState strategy nature n).1)) =
            strategy.2 (G.strategyState strategy nature n).2.2 := by
        rw [htwo, ← hhtwo, ← hhstate]
        exact (hsim.2 history).symm
      simp only [strategyState]
      rw [compiled_next, hstate, hact1, hact2, hone, htwo, List.map_append]
      constructor
      · rfl
      constructor
      · rfl
      · simp [compiled_observe2, List.map_append]
        rfl

/-- Simulating strategy pairs have identical priority words. -/
theorem historyStrategyWins_iff (strategy : G.HistoryProductStrategy)
    (compiled : D.compiled.HistoryProductStrategy)
    (hsim : D.Simulates strategy compiled) :
    D.compiled.HistoryStrategyWins compiled ↔ G.HistoryStrategyWins strategy := by
  have hpriority : ∀ nature : Nat -> G.Nature,
      (fun n => D.compiled.priority
        (D.compiled.strategyState compiled nature n).1) =
      fun n => G.priority (G.strategyState strategy nature n).1 := by
    intro nature
    funext n
    exact congrArg G.priority (D.compiled_strategyState strategy compiled hsim nature n).1
  constructor <;> intro hwins nature
  · have h := hwins nature
    rw [hpriority nature] at h
    exact h
  · have h := hwins nature
    rw [← hpriority nature] at h
    exact h

/-- Finite-fringe elimination preserves perfect-recall realizability. -/
theorem historyRealizable_iff :
    D.compiled.HistoryRealizable ↔ G.HistoryRealizable := by
  constructor
  · rintro ⟨compiled, hwins⟩
    exact ⟨D.realizeStrategy compiled,
      (D.historyStrategyWins_iff _ compiled (D.simulates_realize compiled)).mp hwins⟩
  · rintro ⟨strategy, hwins⟩
    exact ⟨D.contingentifyStrategy strategy,
      (D.historyStrategyWins_iff strategy _ (D.simulates_contingentify strategy)).mpr hwins⟩

end FringeDecomposition

end FiniteConcurrentGame

namespace MooreController

/-- Read a contingent core controller on full split observations.  The current
fringe is buffered only so that the controller's output table can be resolved. -/
def realizeSplit {Obs Core Fringe Act : Type u} [Fintype Fringe]
    (split : Obs -> Core × Fringe)
    (C : MooreController.{u, u, u} Core (Fringe -> Act))
    (initialFringe : Fringe) : MooreController.{u, u, u} Obs Act where
  Memory := C.Memory × Fringe
  memoryFinite := inferInstance
  initial := (C.initial, initialFringe)
  update memory observation := (C.update memory.1 (split observation).1,
    (split observation).2)
  output memory := C.output memory.1 memory.2

theorem realizeSplit_run_append {Obs Core Fringe Act : Type u} [Fintype Fringe]
    (split : Obs -> Core × Fringe)
    (C : MooreController.{u, u, u} Core (Fringe -> Act))
    (initialFringe : Fringe) (observations : List Obs) (letter : Obs) :
    (realizeSplit split C initialFringe).run (observations ++ [letter]) =
      (C.run ((observations ++ [letter]).map fun o => (split o).1),
        (split letter).2) := by
  induction observations using List.reverseRecOn generalizing letter with
  | nil => rfl
  | append_singleton observations last ih =>
      rw [MooreController.run_append_singleton, ih]
      simp only [realizeSplit, List.map_append, List.map_singleton]
      simp only [MooreController.run_append_singleton]

theorem realizeSplit_strategy {Obs Core Fringe Act : Type u} [Fintype Fringe]
    (split : Obs -> Core × Fringe)
    (C : MooreController.{u, u, u} Core (Fringe -> Act))
    (initialFringe : Fringe) (observations : List Obs) (letter : Obs) :
    (realizeSplit split C initialFringe).strategy (observations ++ [letter]) =
      C.strategy ((observations ++ [letter]).map fun o => (split o).1)
        (split letter).2 := by
  rw [MooreController.strategy, realizeSplit_run_append]
  rfl

end MooreController

namespace FiniteConcurrentGame.FringeDecomposition

variable {G : FiniteConcurrentGame.{u}} (D : G.FringeDecomposition)

/-- A finite-state winner of the strict core game reads back to a finite-state
winner of the original split-fringe game. -/
theorem finiteStateRealizable_of_compiled
    (hfinite : D.compiled.FiniteStateRealizable) : G.FiniteStateRealizable := by
  obtain ⟨⟨C1, C2⟩, hwins⟩ := hfinite
  let R1 := MooreController.realizeSplit D.split1 C1
    (D.fringe1 (G.observe1 G.initial))
  let R2 := MooreController.realizeSplit D.split2 C2
    (D.fringe2 (G.observe2 G.initial))
  refine ⟨⟨R1, R2⟩, ?_⟩
  exact (D.historyStrategyWins_iff (R1.strategy, R2.strategy)
    (C1.strategy, C2.strategy)
    ⟨fun history => by
        rw [G.observations1_settled_concat history]
        exact MooreController.realizeSplit_strategy D.split1 C1 _ _ _,
      fun history => by
        rw [G.observations2_settled_concat history]
        exact MooreController.realizeSplit_strategy D.split2 C2 _ _ _⟩).mp hwins

/-- Transport the full finite-state synthesis certificate back across the
unconditional split-fringe reduction. -/
noncomputable def finiteStateSynthesisCertificate_of_compiled
    (certificate : D.compiled.FiniteStateSynthesisCertificate) :
    G.FiniteStateSynthesisCertificate where
  complete hrealizable :=
    D.finiteStateRealizable_of_compiled
      (certificate.complete (D.historyRealizable_iff.mpr hrealizable))
  decision := by
    letI := certificate.decision
    exact decidable_of_iff _ D.historyRealizable_iff

end FiniteConcurrentGame.FringeDecomposition

end DistributedSynthesis
