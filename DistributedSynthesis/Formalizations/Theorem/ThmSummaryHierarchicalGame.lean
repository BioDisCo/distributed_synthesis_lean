/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyFiniteState
import DistributedSynthesis.Formalizations.Theorem.ThmEpochArenaAnchor
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteStateSummaryCompilation
import DistributedSynthesis.Formalizations.Theorem.ThmSummaryMeasurableTransfer

/-!
# The concrete finite hierarchical game of the full model

This file gives the model-specific finite concurrent game to which the
Berwanger--Mathew--van den Bogaard finite-state theorem must be applied.  It
corrects the too-flat `InformedAnnotationAutomaton` route: each player observes
its complete finite local summary after the current environment round has been
revealed, so received partner information is present.

Timing is represented faithfully.  The distinguished initial state lets
Nature choose the first environment round.  A pending state `(state, round)`
then exposes the two post-round local summaries; the processes choose their
separate outputs, the epoch transformer absorbs that round, and Nature chooses
the next round.  The initial dummy priority occurs only once and therefore
does not affect the parity objective.
-/

namespace DistributedSynthesis

universe u

namespace DetParityAutomaton

open FiniteEpochTransformer

variable {In₁ In₂ Out₁ Out₂ : Type u}
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)

/-- The journal-shape epoch transformer used by the concrete game. -/
abbrev summaryGameTransformer :=
  A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M

/-- A pending environment round, preceded by one initial Nature-choice state. -/
abbrev SummaryGameState :=
  Unit ⊕
    (GameState (A.summaryGameTransformer M) × EnvironmentRound In₁ In₂)

/-- The summary tracking carried by the journal-shape transformer. -/
abbrev summaryGameTracking :=
  A.summaryEpochTransformerTracking (Out₁ := Out₁) (Out₂ := Out₂) M

/-- The objective-state tracking carried by the first product component. -/
abbrev summaryGameDPATracking :
    DPATracking (A.summaryGameTransformer M) A :=
  A.epochTransformerTracking.prodFst (M.carrier A)

/-- The local observation in a pending state is the player's summary after
reading the pending environment round. -/
def summaryGameObserve (d : Proc) : A.SummaryGameState M -> M.Summary d
  | Sum.inl _ => M.initial d
  | Sum.inr (state, round) =>
      (A.summaryGameTracking M).fringeDecoder d state round

/-- Absorb the pending round using the two separately chosen outputs. -/
def summaryGameAbsorb
    (state : GameState (A.summaryGameTransformer M))
    (round : EnvironmentRound In₁ In₂)
    (outputOne : Out₁) (outputTwo : Out₂) :
    GameState (A.summaryGameTransformer M) :=
  recordTransition (A.summaryGameTransformer M) state
    { inputOne := round.inputOne
      inputTwo := round.inputTwo
      graph := round.graph
      outputOne := outputOne
      outputTwo := outputTwo }

/--
The actual finite two-process game.  Actions are local outputs and Nature is
the environment round.  At the initial dummy state actions are ignored while
Nature supplies round zero; subsequently the pending round is absorbed and
the Nature argument becomes the next pending round.
-/
noncomputable def summaryHierarchicalGame : FiniteConcurrentGame.{u} where
  State := A.SummaryGameState M
  Action1 := Out₁
  Action2 := Out₂
  Nature := EnvironmentRound In₁ In₂
  Observation1 := M.Summary Proc.one
  Observation2 := M.Summary Proc.two
  stateFinite := inferInstance
  action1Finite := inferInstance
  action2Finite := inferInstance
  natureFinite := inferInstance
  observation1Finite := M.finite Proc.one
  observation2Finite := M.finite Proc.two
  initial := Sum.inl Unit.unit
  next state outputOne outputTwo nextRound :=
    match state with
    | Sum.inl _ =>
        Sum.inr (Sum.inl (A.summaryInitialBoundary M), nextRound)
    | Sum.inr (epochState, currentRound) =>
        Sum.inr
          (A.summaryGameAbsorb M epochState currentRound outputOne outputTwo,
            nextRound)
  observe1 := A.summaryGameObserve M Proc.one
  observe2 := A.summaryGameObserve M Proc.two
  priority
    | Sum.inl _ => 0
    | Sum.inr (state, _) => (A.summaryGameDPATracking M).stateOf state |> A.priority

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp]
theorem summaryHierarchicalGame_initial :
    (A.summaryHierarchicalGame M).initial = Sum.inl Unit.unit :=
  rfl

@[simp]
theorem summaryHierarchicalGame_next_initial
    (outputOne : Out₁) (outputTwo : Out₂)
    (round : EnvironmentRound In₁ In₂) :
    (A.summaryHierarchicalGame M).next (Sum.inl Unit.unit)
        outputOne outputTwo round =
      Sum.inr (Sum.inl (A.summaryInitialBoundary M), round) :=
  rfl

@[simp]
theorem summaryHierarchicalGame_next_pending
    (state : GameState (A.summaryGameTransformer M))
    (currentRound nextRound : EnvironmentRound In₁ In₂)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (A.summaryHierarchicalGame M).next
        (Sum.inr (state, currentRound)) outputOne outputTwo nextRound =
      Sum.inr
        (A.summaryGameAbsorb M state currentRound outputOne outputTwo,
          nextRound) :=
  rfl

@[simp]
theorem summaryHierarchicalGame_observeOne_pending
    (state : GameState (A.summaryGameTransformer M))
    (round : EnvironmentRound In₁ In₂) :
    (A.summaryHierarchicalGame M).observe1 (Sum.inr (state, round)) =
      (A.summaryGameTracking M).fringeDecoder Proc.one state round :=
  rfl

@[simp]
theorem summaryHierarchicalGame_observeTwo_pending
    (state : GameState (A.summaryGameTransformer M))
    (round : EnvironmentRound In₁ In₂) :
    (A.summaryHierarchicalGame M).observe2 (Sum.inr (state, round)) =
      (A.summaryGameTracking M).fringeDecoder Proc.two state round :=
  rfl

end

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- Absorption advances the carried joint summaries by exactly the pending
environment round; outputs do not affect local information. -/
theorem summaryOf_summaryGameAbsorb
    (state : GameState (A.summaryGameTransformer M))
    (round : EnvironmentRound In₁ In₂)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (A.summaryGameTracking M).summaryOf
        (A.summaryGameAbsorb M state round outputOne outputTwo) =
      M.advance ((A.summaryGameTracking M).summaryOf state)
        round.graph round.inputOne round.inputTwo := by
  exact (A.summaryGameTracking M).summaryOf_recordTransition _ _

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- Absorption advances the objective automaton by the emitted real record. -/
theorem stateOf_summaryGameAbsorb
    (state : GameState (A.summaryGameTransformer M))
    (round : EnvironmentRound In₁ In₂)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (A.summaryGameDPATracking M).stateOf
        (A.summaryGameAbsorb M state round outputOne outputTwo) =
      A.step ((A.summaryGameDPATracking M).stateOf state)
        { inputOne := round.inputOne
          inputTwo := round.inputTwo
          graph := round.graph
          outputOne := outputOne
          outputTwo := outputTwo } := by
  unfold summaryGameAbsorb
  exact
    FiniteEpochTransformer.DPATracking.stateOf_recordTransition
      (A.summaryGameTransformer M) (A.summaryGameDPATracking M) state
      { inputOne := round.inputOne
        inputTwo := round.inputTwo
        graph := round.graph
        outputOne := outputOne
        outputTwo := outputTwo }

/-- Remove the arena's one initial Nature-choice observation from a controller
by pre-consuming that observation in its initial memory.  Thereafter the same
update/output functions read the genuine per-round local summaries. -/
def afterInitialSummaryController {d : Proc} {Out : Type u}
    (C : MooreController.{u, u, u} (M.Summary d) Out) :
    MooreController.{u, u, u} (M.Summary d) Out where
  Memory := C.Memory
  memoryFinite := C.memoryFinite
  initial := C.update C.initial (M.initial d)
  update := C.update
  output := C.output

omit [Fintype In₁] [Fintype In₂] [Inhabited In₁] [Inhabited In₂] in
/-- Pre-consuming the dummy observation is exactly list-prefixing the real
summary history by `M.initial d`. -/
theorem afterInitialSummaryController_run {d : Proc} {Out : Type u}
    (C : MooreController.{u, u, u} (M.Summary d) Out)
    (observations : List (M.Summary d)) :
    (afterInitialSummaryController M C).run observations =
      C.run (M.initial d :: observations) := by
  simp [MooreController.run_eq_foldl, afterInitialSummaryController]

/-- The two extracted finite controllers, adjusted for the initial Nature
staging observation, can be compiled directly into the existing local-summary
product construction. -/
def withSummaryGameControllers
    (C₁ : MooreController.{u, u, u} (M.Summary Proc.one) Out₁)
    (C₂ : MooreController.{u, u, u} (M.Summary Proc.two) Out₂) :
    LocalSummaryAutomaton.{u, u, u} In₁ In₂ :=
  M.withMooreControllers (afterInitialSummaryController M C₁)
    (afterInitialSummaryController M C₂)

/-- The exact external mathematical engine at the concrete arena: arbitrary
perfect-recall realizability in the two-local-summary game is effectively
equivalent to realizability by finite Moore controllers. -/
abbrev SummaryGameFiniteStateCertificate :=
  (A.summaryHierarchicalGame M).FiniteStateSynthesisCertificate

/-- Dynamic hierarchy stated on the concrete arena's perfect-recall
observation histories.

**Do not attempt to prove this statement: it is refutable** for every summary
automaton `M` that distinguishes anything, and no bounded observation delay
repairs it (the `thm:onebitfringe` fork propagates through `right` rounds,
and finite summary folds merge distinct observation prefixes).  See the
module docstring of `LemSummaryGameHierarchy.lean` for the two counterexample
mechanisms.  The applicability fact the model actually provides -- and which
is proved there from `prop:dynhier` and `lem:delayonehierarchy` -- is the
delay-one view-granularity hierarchy
`SummaryGameDelayOneViewHierarchy`/`summaryGameDelayOneViewHierarchy_holds`:
the pending round's receiver's view determines its own full observation list
and the sender's settled observation prefix.  Per
`ThmDynamicHierarchyFiniteState.lean`, the finite-state engine must consume
that bounded-delay form through a finite-fringe compilation of the delayed
suffix before any strict-form argument applies. -/
abbrev SummaryGameDynamicHierarchy : Prop :=
  (A.summaryHierarchicalGame M).DynamicHierarchy

end DetParityAutomaton

end DistributedSynthesis
