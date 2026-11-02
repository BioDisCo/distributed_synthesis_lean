/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSummaryGameHierarchy

/-!
# Whole-observation delay adapter

This file studies a generic adapter that delays both complete observation
streams by one round.  It was originally proposed as the interface between the proved delay-one
view-granularity hierarchy of the summary hierarchical game
(`Lemma/LemSummaryGameHierarchy.lean`, the arena transport of
`lem:delayonehierarchy` under the `thm:onebitfringe` fringe) and the
strict-hierarchy input format of the finite-state engine of
`ThmDynamicHierarchyFiniteState.lean` (the Berwanger--Mathew--van den Bogaard
Theorem 10 boundary used by paper `prop:starcomplete`).  That proposed model
application is not valid: the proved delay-one order does not imply the
settled-in/settled-out hierarchy required below.  The correct paper reduction
is `ThmSplitFringeCompiledGame.lean`: retain the current non-fringe core and
compile only the finite current fringe into contingent actions.

## The compilation

`FiniteConcurrentGame.fringeCompiled G` delays each player's observation by
one round and moves the missing current letter into the action structure, the
arena form of the staged/contingent discipline of `lem:fringeelim`
(`Lemma/LemFringeelim.lean`, `Lemma/LemDelayedhierarchywinning.lean`): a
compiled action is a finite table from the player's current, not yet
observed, letter to an original action, and the dynamics resolve the table at
the true letter.  The compiled per-history observation lists are exactly the
settled prefixes of the original ones
(`fringeCompiled_observations1/2`): the one-round delayed suffix that
`summaryGame_viewOne_determines_settledTwo` cannot control has been removed
from the observations.  Everything stays `Fintype`; the contingent action
spaces use classical decidable equality, in line with the platform arena
being noncomputable already.

## What is proved

* Realizability transfer, both directions and at both strategy granularities:
  `fringeCompiled_historyRealizable_iff` via the
  `contingentifyStrategy`/`realizeContingentStrategy` retraction (the
  `contingentify`/`realizeContingent` pattern of `lem:fringeelim`, mirrored
  at the arena because the arena plays are infinite parity plays rather than
  the finite traces of `Lemma/LemFringeelim.lean`), and
  `finiteStateRealizable_of_fringeCompiled`: a Moore pair for the compiled
  game yields a Moore pair for the original game with one fringe-buffer
  factor (`MooreController.settleController`).  Consequently
  `finiteStateSynthesisCertificate_of_fringeCompiled` moves the entire
  Theorem 10 output boundary from the compiled game back to the original.

* The exact hierarchy content of the compilation:
  `fringeCompiled_dynamicHierarchy_iff` identifies the compiled game's STRICT
  per-history `DynamicHierarchy` with the settled (delay-one, settled-in
  settled-out) hierarchy `SettledHierarchy` of the original game.  The
  compilation removes precisely the fringe/delay obstruction, no more.

* At the platform arena (`ThmSummaryHierarchicalGame.lean`), the
  unconditional transport of `summaryGameDelayOneViewHierarchy_holds`:
  `summaryFringeCompiledGame_pendingView_hierarchy`.  On the compiled game
  the delay is gone from the conclusions: at every compiled history the
  pending round's receiver's view determines BOTH players' FULL compiled
  observation lists (on the platform game itself only the settled prefix of
  the sender's list was determined).  This is the precise sense in which the
  delayed suffix was moved out of the observations.  This fact does **not**
  prove strict dynamic hierarchy, because its hypothesis is equality of a
  pending full view rather than equality of a compiled observation history.

## What is deliberately an interface, and why

`(A.summaryFringeCompiledGame M).DynamicHierarchy` itself -- equivalently, by
`summaryFringeCompiledGame_dynamicHierarchy_iff`, the settled hierarchy
`SummaryGameSettledHierarchy A M` of the platform game -- is NOT provable for
arbitrary `M`, and this file does not claim it.  It is refutable by the
summary-merging mechanism (mechanism (ii) of the
`Lemma/LemSummaryGameHierarchy.lean` docstring).  Concrete countermodel
inside the actual `LocalSummaryAutomaton` interface: take
`Summary one := In₁` tracking only the last own input
(`stepNoRecv`/`stepRecv` both return the own-input component) and
`Summary two := In₂ × Bool` tracking the last own input and receipt flag.
At the arena history that installs `left` with inputs `(a, x)` and then any
further rounds, the alternative varying `x` has equal player-one observation
lists at every granularity derived from these summaries (process one's
summary chain never mentions `x`) but different player-two lists, and the
alternative varying `a` is symmetric; both determinations fail at one
history, at any observation delay, compiled or not.  The residual is
therefore exactly the summary-design obligation of the paper (the summaries
must preserve the `prop:dynhier` sub-tuple map, the content of
`prop:epochhierarchical`), stated here at the smallest possible interface:
`SummaryGameSettledHierarchy A M`.  The rank-machine engine should target
`FringeCompiledFiniteStateCertificate A M`; the checked implication
`summaryGameFiniteStateCertificate_of_fringeCompiled` closes the platform
residual `SummaryGameFiniteStateCertificate A M` from it.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

/--
The fringe compilation of a finite concurrent game.  The state buffers the
previous state's two observations; players observe the buffer, so each
observation stream is the original stream delayed by one round.  An action is
a finite contingent table from the player's current, hidden letter to an
original action; `next` resolves the table at the true current letter.
-/
noncomputable def fringeCompiled : FiniteConcurrentGame.{u} where
  State := G.Observation1 × G.Observation2 × G.State
  Action1 := G.Observation1 -> G.Action1
  Action2 := G.Observation2 -> G.Action2
  Nature := G.Nature
  Observation1 := G.Observation1
  Observation2 := G.Observation2
  stateFinite := inferInstance
  action1Finite := @Pi.instFintype _ _ (Classical.decEq _) _ _
  action2Finite := @Pi.instFintype _ _ (Classical.decEq _) _ _
  natureFinite := G.natureFinite
  observation1Finite := G.observation1Finite
  observation2Finite := G.observation2Finite
  initial := (G.observe1 G.initial, G.observe2 G.initial, G.initial)
  next state action1 action2 nature :=
    (G.observe1 state.2.2, G.observe2 state.2.2,
      G.next state.2.2 (action1 (G.observe1 state.2.2))
        (action2 (G.observe2 state.2.2)) nature)
  observe1 state := state.1
  observe2 state := state.2.1
  priority state := G.priority state.2.2

@[simp]
theorem fringeCompiled_initial :
    G.fringeCompiled.initial =
      (G.observe1 G.initial, G.observe2 G.initial, G.initial) := rfl

@[simp]
theorem fringeCompiled_next (state : G.fringeCompiled.State)
    (action1 : G.fringeCompiled.Action1) (action2 : G.fringeCompiled.Action2)
    (nature : G.Nature) :
    G.fringeCompiled.next state action1 action2 nature =
      (G.observe1 state.2.2, G.observe2 state.2.2,
        G.next state.2.2 (action1 (G.observe1 state.2.2))
          (action2 (G.observe2 state.2.2)) nature) := rfl

@[simp]
theorem fringeCompiled_observe1 (state : G.fringeCompiled.State) :
    G.fringeCompiled.observe1 state = state.1 := rfl

@[simp]
theorem fringeCompiled_observe2 (state : G.fringeCompiled.State) :
    G.fringeCompiled.observe2 state = state.2.1 := rfl

@[simp]
theorem fringeCompiled_priority (state : G.fringeCompiled.State) :
    G.fringeCompiled.priority state = G.priority state.2.2 := rfl

variable {G}

/-- Resolve a compiled history to the original history it simulates: each
contingent table is evaluated at the true current letter. -/
def fringeToBase : G.fringeCompiled.PlayHistory -> G.PlayHistory
  | .initial => .initial
  | .step history action1 action2 nature =>
      .step (fringeToBase history)
        (action1 (G.observe1 (fringeToBase history).lastState))
        (action2 (G.observe2 (fringeToBase history).lastState)) nature

/-- Embed an original history as a compiled history with constant tables. -/
def fringeOfBase : G.PlayHistory -> G.fringeCompiled.PlayHistory
  | .initial => .initial
  | .step history action1 action2 nature =>
      .step (fringeOfBase history) (fun _ => action1) (fun _ => action2) nature

@[simp]
theorem fringeToBase_fringeOfBase (history : G.PlayHistory) :
    fringeToBase (fringeOfBase history) = history := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      simp [fringeOfBase, fringeToBase, ih]

/-- The third state component of a compiled play is the simulated original
play. -/
theorem fringeToBase_lastState (history : G.fringeCompiled.PlayHistory) :
    history.lastState.2.2 = (fringeToBase history).lastState := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      show (G.fringeCompiled.next history.lastState action1 action2
        nature).2.2 = _
      rw [fringeCompiled_next]
      simp only [fringeToBase, PlayHistory.lastState, ih]

variable (G)

/-- Every original observation list is its settled prefix extended by the
observation of the last state. -/
theorem observations1_settled_concat (history : G.PlayHistory) :
    history.observations1 =
      settledPrefix 1 history.observations1 ++
        [G.observe1 history.lastState] := by
  cases history with
  | initial => simp [settledPrefix, PlayHistory.lastState]
  | step history action1 action2 nature =>
      rw [PlayHistory.observations1_step, settledPrefix_one_append]
      rfl

/-- Mirror of `observations1_settled_concat`. -/
theorem observations2_settled_concat (history : G.PlayHistory) :
    history.observations2 =
      settledPrefix 1 history.observations2 ++
        [G.observe2 history.lastState] := by
  cases history with
  | initial => simp [settledPrefix, PlayHistory.lastState]
  | step history action1 action2 nature =>
      rw [PlayHistory.observations2_step, settledPrefix_one_append]
      rfl

/-- **Compiled observations are the settled prefixes**: player one's compiled
observation list is the initial letter followed by the settled prefix of the
simulated original list. -/
theorem fringeCompiled_observations1
    (history : G.fringeCompiled.PlayHistory) :
    history.observations1 =
      G.observe1 G.initial ::
        settledPrefix 1 (fringeToBase history).observations1 := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      rw [PlayHistory.observations1_step, ih]
      have hlast :
          G.fringeCompiled.observe1
              (G.fringeCompiled.next history.lastState action1 action2
                nature) =
            G.observe1 (fringeToBase history).lastState := by
        rw [fringeCompiled_next, fringeCompiled_observe1,
          fringeToBase_lastState]
      rw [hlast,
        show fringeToBase (history.step action1 action2 nature) =
          PlayHistory.step (fringeToBase history) _ _ nature from rfl,
        PlayHistory.observations1_step, settledPrefix_one_append]
      conv_rhs => rw [G.observations1_settled_concat (fringeToBase history)]
      rfl

/-- Mirror of `fringeCompiled_observations1`. -/
theorem fringeCompiled_observations2
    (history : G.fringeCompiled.PlayHistory) :
    history.observations2 =
      G.observe2 G.initial ::
        settledPrefix 1 (fringeToBase history).observations2 := by
  induction history with
  | initial => rfl
  | step history action1 action2 nature ih =>
      rw [PlayHistory.observations2_step, ih]
      have hlast :
          G.fringeCompiled.observe2
              (G.fringeCompiled.next history.lastState action1 action2
                nature) =
            G.observe2 (fringeToBase history).lastState := by
        rw [fringeCompiled_next, fringeCompiled_observe2,
          fringeToBase_lastState]
      rw [hlast,
        show fringeToBase (history.step action1 action2 nature) =
          PlayHistory.step (fringeToBase history) _ _ nature from rfl,
        PlayHistory.observations2_step, settledPrefix_one_append]
      conv_rhs => rw [G.observations2_settled_concat (fringeToBase history)]
      rfl

/-- Delay-one settled determination, settled hypotheses and settled
conclusions: player one's settled observation prefix determines player two's
settled observation prefix.  This is strictly weaker in hypothesis (and
therefore stronger as a claim) than `OneDeterminesTwoWithDelayAt 1`. -/
def OneDeterminesTwoSettledAt (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    settledPrefix 1 alternative.observations1 =
        settledPrefix 1 history.observations1 ->
      settledPrefix 1 alternative.observations2 =
        settledPrefix 1 history.observations2

/-- Mirror of `OneDeterminesTwoSettledAt`. -/
def TwoDeterminesOneSettledAt (history : G.PlayHistory) : Prop :=
  ∀ alternative : G.PlayHistory,
    settledPrefix 1 alternative.observations2 =
        settledPrefix 1 history.observations2 ->
      settledPrefix 1 alternative.observations1 =
        settledPrefix 1 history.observations1

/-- The settled hierarchy: at every history the two settled observation
prefixes are comparable.  By `fringeCompiled_dynamicHierarchy_iff` this is
exactly the strict `DynamicHierarchy` of the fringe-compiled game. -/
def SettledHierarchy : Prop :=
  ∀ history : G.PlayHistory,
    G.OneDeterminesTwoSettledAt history ∨ G.TwoDeterminesOneSettledAt history

theorem fringeCompiled_oneDeterminesTwoAt_iff
    (history : G.fringeCompiled.PlayHistory) :
    G.fringeCompiled.OneDeterminesTwoAt history ↔
      G.OneDeterminesTwoSettledAt (fringeToBase history) := by
  constructor
  · intro hdet alternative halt
    have hobs :
        (fringeOfBase alternative).observations1 = history.observations1 := by
      rw [fringeCompiled_observations1, fringeCompiled_observations1,
        fringeToBase_fringeOfBase, halt]
    have := hdet (fringeOfBase alternative) hobs
    rw [fringeCompiled_observations2, fringeCompiled_observations2,
      fringeToBase_fringeOfBase] at this
    exact List.cons_injective.eq_iff.mp this
  · intro hdet alternative halt
    rw [fringeCompiled_observations1, fringeCompiled_observations1] at halt
    have hsettled :=
      hdet (fringeToBase alternative) (List.cons_injective.eq_iff.mp halt)
    rw [fringeCompiled_observations2, fringeCompiled_observations2, hsettled]

theorem fringeCompiled_twoDeterminesOneAt_iff
    (history : G.fringeCompiled.PlayHistory) :
    G.fringeCompiled.TwoDeterminesOneAt history ↔
      G.TwoDeterminesOneSettledAt (fringeToBase history) := by
  constructor
  · intro hdet alternative halt
    have hobs :
        (fringeOfBase alternative).observations2 = history.observations2 := by
      rw [fringeCompiled_observations2, fringeCompiled_observations2,
        fringeToBase_fringeOfBase, halt]
    have := hdet (fringeOfBase alternative) hobs
    rw [fringeCompiled_observations1, fringeCompiled_observations1,
      fringeToBase_fringeOfBase] at this
    exact List.cons_injective.eq_iff.mp this
  · intro hdet alternative halt
    rw [fringeCompiled_observations2, fringeCompiled_observations2] at halt
    have hsettled :=
      hdet (fringeToBase alternative) (List.cons_injective.eq_iff.mp halt)
    rw [fringeCompiled_observations1, fringeCompiled_observations1, hsettled]

/-- **The exact hierarchy content of the fringe compilation**: the compiled
game satisfies the strict per-history dynamic hierarchy exactly when the
original game satisfies the settled (delay-one) hierarchy.  The compilation
removes precisely the one-round fringe from the observations, no more. -/
theorem fringeCompiled_dynamicHierarchy_iff :
    G.fringeCompiled.DynamicHierarchy ↔ G.SettledHierarchy := by
  constructor
  · intro hdyn history
    rcases hdyn (fringeOfBase history) with hone | htwo
    · left
      have := (G.fringeCompiled_oneDeterminesTwoAt_iff _).mp hone
      rwa [fringeToBase_fringeOfBase] at this
    · right
      have := (G.fringeCompiled_twoDeterminesOneAt_iff _).mp htwo
      rwa [fringeToBase_fringeOfBase] at this
  · intro hsettled history
    rcases hsettled (fringeToBase history) with hone | htwo
    · exact Or.inl ((G.fringeCompiled_oneDeterminesTwoAt_iff _).mpr hone)
    · exact Or.inr ((G.fringeCompiled_twoDeterminesOneAt_iff _).mpr htwo)

/-- Contingentify a perfect-recall strategy pair: the compiled table at a
compiled (settled) history maps the current letter to the original action at
the correspondingly extended original history.  Arena form of
`contingentify` from `lem:fringeelim`. -/
def contingentifyStrategy (strategy : G.HistoryProductStrategy) :
    G.fringeCompiled.HistoryProductStrategy :=
  (fun (observations : List G.fringeCompiled.Observation1)
      (letter : G.fringeCompiled.Observation1) =>
      strategy.1 (observations.drop 1 ++ [letter]),
    fun (observations : List G.fringeCompiled.Observation2)
      (letter : G.fringeCompiled.Observation2) =>
      strategy.2 (observations.drop 1 ++ [letter]))

/-- Realize a compiled strategy pair as an original one: read the settled
prefix off the own history and evaluate the table at the current letter.
Arena form of `realizeContingent` from `lem:fringeelim`. -/
def realizeContingentStrategy
    (strategy : G.fringeCompiled.HistoryProductStrategy) :
    G.HistoryProductStrategy :=
  (fun observations =>
      strategy.1 (G.observe1 G.initial :: observations.dropLast)
        (observations.getLastD (G.observe1 G.initial)),
    fun observations =>
      strategy.2 (G.observe2 G.initial :: observations.dropLast)
        (observations.getLastD (G.observe2 G.initial)))

/-- The simulation relation between an original strategy pair and a compiled
one: on every nonempty observation history the original action is the
compiled table evaluated at the current letter. -/
def FringeSimulates (strategy : G.HistoryProductStrategy)
    (compiled : G.fringeCompiled.HistoryProductStrategy) : Prop :=
  (∀ (observations : List G.Observation1) (letter : G.Observation1),
      strategy.1 (observations ++ [letter]) =
        compiled.1 (G.observe1 G.initial :: observations) letter) ∧
    (∀ (observations : List G.Observation2) (letter : G.Observation2),
      strategy.2 (observations ++ [letter]) =
        compiled.2 (G.observe2 G.initial :: observations) letter)

theorem fringeSimulates_contingentify (strategy : G.HistoryProductStrategy) :
    G.FringeSimulates strategy (G.contingentifyStrategy strategy) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem fringeSimulates_realizeContingent
    (strategy : G.fringeCompiled.HistoryProductStrategy) :
    G.FringeSimulates (G.realizeContingentStrategy strategy) strategy :=
  ⟨fun observations letter => by
      simp [realizeContingentStrategy, List.dropLast_concat,
        List.getLastD_concat],
    fun observations letter => by
      simp [realizeContingentStrategy, List.dropLast_concat,
        List.getLastD_concat]⟩

/-- An original observation history generated by a play is its settled prefix
extended by the observation of the current state (player one). -/
theorem strategyState_obs1_concat (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).2.1 =
      settledPrefix 1 (G.strategyState strategy nature n).2.1 ++
        [G.observe1 (G.strategyState strategy nature n).1] := by
  cases n with
  | zero => simp [strategyState, settledPrefix]
  | succ n => simp [strategyState, settledPrefix_one_append]

/-- Mirror of `strategyState_obs1_concat`. -/
theorem strategyState_obs2_concat (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).2.2 =
      settledPrefix 1 (G.strategyState strategy nature n).2.2 ++
        [G.observe2 (G.strategyState strategy nature n).1] := by
  cases n with
  | zero => simp [strategyState, settledPrefix]
  | succ n => simp [strategyState, settledPrefix_one_append]

/-- **Play correspondence**: a simulating pair generates, against every
Nature sequence, the same original states, with the compiled observation
histories being the initial letter followed by the settled prefixes. -/
theorem fringeCompiled_strategyState (strategy : G.HistoryProductStrategy)
    (compiled : G.fringeCompiled.HistoryProductStrategy)
    (hsim : G.FringeSimulates strategy compiled)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.fringeCompiled.strategyState compiled nature n).1.2.2 =
        (G.strategyState strategy nature n).1 ∧
      (G.fringeCompiled.strategyState compiled nature n).2.1 =
        G.observe1 G.initial ::
          settledPrefix 1 (G.strategyState strategy nature n).2.1 ∧
      (G.fringeCompiled.strategyState compiled nature n).2.2 =
        G.observe2 G.initial ::
          settledPrefix 1 (G.strategyState strategy nature n).2.2 := by
  induction n with
  | zero =>
      exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      obtain ⟨ihstate, ihone, ihtwo⟩ := ih
      have hact1 :
          compiled.1 (G.fringeCompiled.strategyState compiled nature n).2.1
              (G.observe1 (G.strategyState strategy nature n).1) =
            strategy.1 (G.strategyState strategy nature n).2.1 := by
        rw [ihone]
        exact (hsim.1 (settledPrefix 1 (G.strategyState strategy nature n).2.1)
            (G.observe1 (G.strategyState strategy nature n).1)).symm.trans
          (congrArg strategy.1 (G.strategyState_obs1_concat strategy nature n).symm)
      have hact2 :
          compiled.2 (G.fringeCompiled.strategyState compiled nature n).2.2
              (G.observe2 (G.strategyState strategy nature n).1) =
            strategy.2 (G.strategyState strategy nature n).2.2 := by
        rw [ihtwo]
        exact (hsim.2 (settledPrefix 1 (G.strategyState strategy nature n).2.2)
            (G.observe2 (G.strategyState strategy nature n).1)).symm.trans
          (congrArg strategy.2 (G.strategyState_obs2_concat strategy nature n).symm)
      have hnext :
          (G.fringeCompiled.strategyState compiled nature (n + 1)).1 =
            (G.observe1 (G.strategyState strategy nature n).1,
              G.observe2 (G.strategyState strategy nature n).1,
              (G.strategyState strategy nature (n + 1)).1) := by
        show G.fringeCompiled.next
            (G.fringeCompiled.strategyState compiled nature n).1
            (compiled.1 (G.fringeCompiled.strategyState compiled nature n).2.1)
            (compiled.2 (G.fringeCompiled.strategyState compiled nature n).2.2)
            (nature n) = _
        rw [fringeCompiled_next, ihstate, hact1, hact2]
        rfl
      refine ⟨by rw [hnext], ?_, ?_⟩
      · show (G.fringeCompiled.strategyState compiled nature n).2.1 ++
            [G.fringeCompiled.observe1
              (G.fringeCompiled.strategyState compiled nature (n + 1)).1] = _
        rw [hnext, fringeCompiled_observe1, ihone,
          show (G.strategyState strategy nature (n + 1)).2.1 =
            (G.strategyState strategy nature n).2.1 ++
              [G.observe1 (G.strategyState strategy nature (n + 1)).1]
            from rfl,
          settledPrefix_one_append]
        conv_rhs => rw [G.strategyState_obs1_concat strategy nature n]
        rfl
      · show (G.fringeCompiled.strategyState compiled nature n).2.2 ++
            [G.fringeCompiled.observe2
              (G.fringeCompiled.strategyState compiled nature (n + 1)).1] = _
        rw [hnext, fringeCompiled_observe2, ihtwo,
          show (G.strategyState strategy nature (n + 1)).2.2 =
            (G.strategyState strategy nature n).2.2 ++
              [G.observe2 (G.strategyState strategy nature (n + 1)).1]
            from rfl,
          settledPrefix_one_append]
        conv_rhs => rw [G.strategyState_obs2_concat strategy nature n]
        rfl

/-- Simulating pairs produce identical priority streams; winning transfers in
both directions. -/
theorem fringeCompiled_historyStrategyWins_iff
    (strategy : G.HistoryProductStrategy)
    (compiled : G.fringeCompiled.HistoryProductStrategy)
    (hsim : G.FringeSimulates strategy compiled) :
    G.fringeCompiled.HistoryStrategyWins compiled ↔
      G.HistoryStrategyWins strategy := by
  have hpriority : ∀ (nature : Nat -> G.Nature),
      (fun n => G.fringeCompiled.priority
        (G.fringeCompiled.strategyState compiled nature n).1) =
        fun n => G.priority (G.strategyState strategy nature n).1 := by
    intro nature
    funext n
    rw [fringeCompiled_priority]
    exact congrArg G.priority
      (G.fringeCompiled_strategyState strategy compiled hsim nature n).1
  constructor
  · intro hwins nature
    have := hwins nature
    rwa [hpriority nature] at this
  · intro hwins nature
    have := hwins nature
    rw [hpriority nature]
    exact this

/-- **Realizability transfer** for the fringe compilation, both directions:
the arena form of the `lem:fringeelim` equivalence
(`fringeElim_winning_iff`). -/
theorem fringeCompiled_historyRealizable_iff :
    G.fringeCompiled.HistoryRealizable ↔ G.HistoryRealizable := by
  constructor
  · rintro ⟨compiled, hwins⟩
    exact ⟨G.realizeContingentStrategy compiled,
      (G.fringeCompiled_historyStrategyWins_iff _ compiled
        (G.fringeSimulates_realizeContingent compiled)).mp hwins⟩
  · rintro ⟨strategy, hwins⟩
    exact ⟨G.contingentifyStrategy strategy,
      (G.fringeCompiled_historyStrategyWins_iff strategy _
        (G.fringeSimulates_contingentify strategy)).mpr hwins⟩

end FiniteConcurrentGame

namespace MooreController

/-- Compile a Moore controller of the fringe-compiled game (whose outputs are
contingent tables) into a Moore controller of the original game.  The extra
memory factor buffers the last observation letter; the table computed from
the settled past is evaluated at that buffered current letter. -/
def settleController {Obs Act : Type u} [Fintype Obs]
    (C : MooreController.{u, u, u} Obs (Obs -> Act)) (base : Obs) :
    MooreController.{u, u, u} Obs Act where
  Memory := C.Memory × Obs
  memoryFinite := inferInstance
  initial := (C.initial, base)
  update memory observation := (C.update memory.1 memory.2, observation)
  output memory := C.output memory.1 memory.2

theorem settleController_run {Obs Act : Type u} [Fintype Obs]
    (C : MooreController.{u, u, u} Obs (Obs -> Act)) (base : Obs)
    (observations : List Obs) :
    ∀ letter : Obs,
      (settleController C base).run (observations ++ [letter]) =
        (C.run (base :: observations), letter) := by
  induction observations using List.reverseRecOn with
  | nil => intro letter; rfl
  | append_singleton observations last ih =>
      intro letter
      rw [MooreController.run_append_singleton, ih last]
      show (C.update (C.run (base :: observations)) last, letter) = _
      rw [← List.cons_append, MooreController.run_append_singleton]

/-- On every nonempty observation history the compiled-and-settled controller
plays the compiled controller's table at the current letter: exactly the
`FringeSimulates` equation. -/
theorem settleController_strategy {Obs Act : Type u} [Fintype Obs]
    (C : MooreController.{u, u, u} Obs (Obs -> Act)) (base : Obs)
    (observations : List Obs) (letter : Obs) :
    (settleController C base).strategy (observations ++ [letter]) =
      C.strategy (base :: observations) letter := by
  rw [MooreController.strategy, settleController_run]
  rfl

end MooreController

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

/-- **Finite-state transfer**: a winning Moore pair for the fringe-compiled
game yields a winning Moore pair for the original game, each with one
fringe-buffer memory factor. -/
theorem finiteStateRealizable_of_fringeCompiled
    (hfinite : G.fringeCompiled.FiniteStateRealizable) :
    G.FiniteStateRealizable := by
  obtain ⟨⟨C₁, C₂⟩, hwins⟩ := hfinite
  refine ⟨⟨MooreController.settleController C₁ (G.observe1 G.initial),
    MooreController.settleController C₂ (G.observe2 G.initial)⟩, ?_⟩
  exact (G.fringeCompiled_historyStrategyWins_iff _ (C₁.strategy, C₂.strategy)
    ⟨fun observations letter =>
        MooreController.settleController_strategy C₁ _ observations letter,
      fun observations letter =>
        MooreController.settleController_strategy C₂ _ observations letter⟩).mp
    hwins

/-- **Certificate transfer**: the full Theorem 10 output boundary moves from
the fringe-compiled game back to the original game.  This is the implication
the rank-machine engine should feed. -/
def finiteStateSynthesisCertificate_of_fringeCompiled
    (certificate : G.fringeCompiled.FiniteStateSynthesisCertificate) :
    G.FiniteStateSynthesisCertificate where
  complete hrealizable :=
    G.finiteStateRealizable_of_fringeCompiled
      (certificate.complete
        ((G.fringeCompiled_historyRealizable_iff).mpr hrealizable))
  decision :=
    haveI := certificate.decision
    decidable_of_iff _ (G.fringeCompiled_historyRealizable_iff)

end FiniteConcurrentGame

namespace DetParityAutomaton

open FiniteEpochTransformer FiniteConcurrentGame

variable {In₁ In₂ Out₁ Out₂ : Type u}
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)

/-- The fringe-compiled adapter arena of the concrete Theorem-10 platform. -/
noncomputable abbrev summaryFringeCompiledGame : FiniteConcurrentGame.{u} :=
  (A.summaryHierarchicalGame M).fringeCompiled

omit [Inhabited In₁] [Inhabited In₂] in
/--
**The unconditional strict transport of the delay-one view hierarchy**: at
every history of the fringe-compiled arena, the pending round's receiver's
view determines BOTH players' FULL compiled observation lists; the direction
is the pending graph.  On the platform game itself the receiver's view only
determined the sender's settled prefix (`summaryGameDelayOneViewHierarchy`);
after the compilation the delay is gone from the conclusions, because the
compiled observations are exactly the settled prefixes.  This is the
fringe/delay half of the strict hierarchy, discharged with no assumption on
`M` from `summaryGameDelayOneViewHierarchy_holds` (`prop:dynhier`,
`lem:delayonehierarchy`, `thm:onebitfringe`).
-/
theorem summaryFringeCompiledGame_pendingView_hierarchy
    (history : (A.summaryFringeCompiledGame M).PlayHistory) :
    (∀ alternative : (A.summaryFringeCompiledGame M).PlayHistory,
        summaryGamePendingView A M Proc.one (fringeToBase alternative) =
            summaryGamePendingView A M Proc.one (fringeToBase history) ->
          alternative.observations1 = history.observations1 ∧
            alternative.observations2 = history.observations2) ∨
      (∀ alternative : (A.summaryFringeCompiledGame M).PlayHistory,
          summaryGamePendingView A M Proc.two (fringeToBase alternative) =
              summaryGamePendingView A M Proc.two (fringeToBase history) ->
            alternative.observations2 = history.observations2 ∧
              alternative.observations1 = history.observations1) := by
  rcases summaryGameDelayOneViewHierarchy_holds A M (fringeToBase history)
    with hone | htwo
  · left
    intro alternative hview
    obtain ⟨hobs1, hsettled2⟩ := hone (fringeToBase alternative) hview
    constructor
    · rw [fringeCompiled_observations1, fringeCompiled_observations1, hobs1]
    · rw [fringeCompiled_observations2, fringeCompiled_observations2,
        hsettled2]
  · right
    intro alternative hview
    obtain ⟨hobs2, hsettled1⟩ := htwo (fringeToBase alternative) hview
    constructor
    · rw [fringeCompiled_observations2, fringeCompiled_observations2, hobs2]
    · rw [fringeCompiled_observations1, fringeCompiled_observations1,
        hsettled1]

/--
The remaining hierarchy residual at the platform arena, in its smallest
form: the settled (delay-one, settled-in settled-out) hierarchy of the
summary hierarchical game.  By
`summaryFringeCompiledGame_dynamicHierarchy_iff` this is EXACTLY the strict
`DynamicHierarchy` of the fringe-compiled adapter game.

This is deliberately an interface, not a theorem: it is refutable for
arbitrary `M` by the summary-merging mechanism (see the module docstring for
a two-line countermodel inside `LocalSummaryAutomaton`), so it must be
supplied by the eventual summary instantiation -- it is the arena transport
of the `prop:epochhierarchical` obligation that the constructed summaries
preserve the `prop:dynhier` sub-tuple map.  The fringe/delay half is already
discharged unconditionally by
`summaryFringeCompiledGame_pendingView_hierarchy`.
-/
abbrev SummaryGameSettledHierarchy : Prop :=
  (A.summaryHierarchicalGame M).SettledHierarchy

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The strict dynamic hierarchy of the fringe-compiled adapter game is
exactly the settled-hierarchy residual of the platform. -/
theorem summaryFringeCompiledGame_dynamicHierarchy_iff :
    (A.summaryFringeCompiledGame M).DynamicHierarchy ↔
      A.SummaryGameSettledHierarchy M :=
  (A.summaryHierarchicalGame M).fringeCompiled_dynamicHierarchy_iff

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Realizability of the fringe-compiled adapter game is realizability of the
platform game. -/
theorem summaryFringeCompiledGame_historyRealizable_iff :
    (A.summaryFringeCompiledGame M).HistoryRealizable ↔
      (A.summaryHierarchicalGame M).HistoryRealizable :=
  (A.summaryHierarchicalGame M).fringeCompiled_historyRealizable_iff

/--
**The exact engine target**: Berwanger--Mathew--van den Bogaard Theorem 10 at
the fringe-compiled (strictly hierarchical) adapter arena.  Its hierarchy
input `(A.summaryFringeCompiledGame M).DynamicHierarchy` is equivalent to
`SummaryGameSettledHierarchy A M`; the fringe/delay half of that input is
already proved (`summaryFringeCompiledGame_pendingView_hierarchy`), the
summary-design half is the `M`-instantiation obligation.  By
`summaryGameFiniteStateCertificate_of_fringeCompiled` this certificate closes
the platform residual `SummaryGameFiniteStateCertificate A M`, whose Moore
controllers the platform compilation chain
(`withSummaryGameControllers`) already consumes.
-/
abbrev FringeCompiledFiniteStateCertificate :=
  (A.summaryFringeCompiledGame M).FiniteStateSynthesisCertificate

/-- A Theorem-10 certificate at the fringe-compiled adapter arena yields the
platform's certificate: the residual of `ThmSummaryHierarchicalGame.lean`
follows from the compiled one. -/
noncomputable def summaryGameFiniteStateCertificate_of_fringeCompiled
    (certificate : A.FringeCompiledFiniteStateCertificate M) :
    A.SummaryGameFiniteStateCertificate M :=
  (A.summaryHierarchicalGame M).finiteStateSynthesisCertificate_of_fringeCompiled
    certificate

end DetParityAutomaton

end DistributedSynthesis
