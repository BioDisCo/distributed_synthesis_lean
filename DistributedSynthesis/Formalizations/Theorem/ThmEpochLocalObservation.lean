/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDPAEpochTransformer

/-!
# Local observations and the readback strategy

This file closes the generic part of the soundness direction of the
epoch-game certificate (`def:epochtransformer` and the finite-game
endpoints of `paper.tex`).

The epoch fold of a `FiniteEpochTransformer` is controller-free once the
outputs are recorded: `recordTransition` absorbs one recorded round, and
along a finite-game play the sequence-driven state equals the record
fold of the emitted prefix (`sequenceStateStream_eq_recordFold`).

A `LocalObservation` equips a transformer with one finite observation
per process and round, computed on the game side from the state and the
current environment round, and on the real side from the process view.
Adequacy states that the two computations agree over every recorded
history.  Views grow unboundedly while game states do not; adequacy is
satisfiable because the view side is a compression of the view, never a
reconstruction of the view from the state.

A controller whose outputs factor through the observations decodes to
the `readbackStrategy`.  Its real executions are exactly the emitted
words of the finite game (`execution_readbackStrategy`), so for tracked
transformers the certificate soundness field follows unconditionally
(`strategySound_of_localObservation`).  What remains for the concrete
journal transformer is to construct an adequate observation; that is
where the dominant-side knowledge (`prop:dynhier`) and the fringe
acknowledgement (`lem:fringeelim`) enter.
-/

namespace DistributedSynthesis

universe u v w a s z o

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace FiniteEpochTransformer

/--
The controller-free epoch fold over one recorded round: the outputs are
read from the record instead of a controller.
-/
def recordTransition
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (state : GameState T)
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    GameState T :=
  match state with
  | Sum.inl boundary =>
      match round.graph with
      | .left =>
          Sum.inr (Sum.inl
            (T.update Proc.one (T.init Proc.one boundary)
              round.inputOne round.inputTwo round.outputOne round.outputTwo))
      | .right =>
          Sum.inr (Sum.inr
            (T.update Proc.two (T.init Proc.two boundary)
              round.inputOne round.inputTwo round.outputOne round.outputTwo))
      | .both =>
          Sum.inl
            (T.close Proc.one (T.init Proc.one boundary) Graph.both
              (roundRecordClosingLetter round))
  | Sum.inr (Sum.inl withinOne) =>
      match round.graph with
      | .left =>
          Sum.inr (Sum.inl
            (T.update Proc.one withinOne
              round.inputOne round.inputTwo round.outputOne round.outputTwo))
      | graph =>
          Sum.inl
            (T.close Proc.one withinOne graph (roundRecordClosingLetter round))
  | Sum.inr (Sum.inr withinTwo) =>
      match round.graph with
      | .right =>
          Sum.inr (Sum.inr
            (T.update Proc.two withinTwo
              round.inputOne round.inputTwo round.outputOne round.outputTwo))
      | graph =>
          Sum.inl
            (T.close Proc.two withinTwo graph (roundRecordClosingLetter round))

/-- The controller-free epoch fold over a recorded history. -/
def recordFold
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    GameState T :=
  history.foldl (recordTransition T) (Sum.inl initialBoundary)

@[simp]
theorem recordFold_nil
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary) :
    recordFold T initialBoundary [] = Sum.inl initialBoundary :=
  rfl

@[simp]
theorem recordFold_append
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (history : History In₁ In₂ Graph Out₁ Out₂)
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    recordFold T initialBoundary (History.append history round) =
      recordTransition T (recordFold T initialBoundary history) round := by
  simp [recordFold, History.append]

/--
On the round it emits, the round-aware game transition is the record
transition.
-/
theorem recordTransition_emitted
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (controller : RoundAwareControllerCode T)
    (state : GameState T)
    (envRound : EnvironmentRound In₁ In₂) :
    recordTransition T state
        {
          inputOne := envRound.inputOne
          inputTwo := envRound.inputTwo
          graph := envRound.graph
          outputOne := (controller state envRound).1
          outputTwo := (controller state envRound).2
        } =
      roundAwareGameTransition T controller state envRound := by
  cases envRound with
  | mk inputOne inputTwo graph =>
      cases state with
      | inl boundary =>
          cases graph <;>
            simp [
              recordTransition,
              roundAwareGameTransition,
              roundRecordClosingLetter
            ]
      | inr side =>
          cases side with
          | inl withinOne =>
              cases graph <;>
                simp [
                  recordTransition,
                  roundAwareGameTransition,
                  roundRecordClosingLetter
                ]
          | inr withinTwo =>
              cases graph <;>
                simp [
                  recordTransition,
                  roundAwareGameTransition,
                  roundRecordClosingLetter
                ]

/--
Along a sequence-driven finite-game play, the game state is the record
fold of the emitted prefix.
-/
theorem sequenceStateStream_eq_recordFold
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (controller : RoundAwareControllerCode T)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    sequenceStateStream T initialBoundary controller env n =
      recordFold T initialBoundary
        (wordPrefix
          (roundAwareWordOfStateStream T controller
            (sequenceStateStream T initialBoundary controller env) env)
          n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [
        sequenceStateStream_succ,
        wordPrefix,
        recordFold_append,
        <- ih
      ]
      exact
        (recordTransition_emitted T controller
          (sequenceStateStream T initialBoundary controller env n)
          (env n)).symm

/--
A per-process finite observation of the epoch game, computable on the
game side from the state and current round and on the real side from
the process view, with both computations agreeing over every recorded
history.
-/
structure LocalObservation
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary) where
  Ω : Proc -> Type o
  obs :
    (d : Proc) -> GameState T -> EnvironmentRound In₁ In₂ -> Ω d
  read : (d : Proc) -> View In₁ In₂ d -> Ω d
  adequate :
    ∀ (d : Proc) (history : History In₁ In₂ Graph Out₁ Out₂)
      (envRound : EnvironmentRound In₁ In₂),
      read d (nextView d history envRound) =
        obs d (recordFold T initialBoundary history) envRound

namespace LocalObservation

variable
  {T :
    FiniteEpochTransformer
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂}
  {initialBoundary : T.boundary}
  (L : LocalObservation.{u, v, w, a, o} T initialBoundary)

/--
The distributed strategy decoding an observation-factored controller:
each process compresses its view to its observation and applies its
output table.
-/
def readbackStrategy
    (outputOne : L.Ω Proc.one -> Out₁)
    (outputTwo : L.Ω Proc.two -> Out₂) :
    StrategyPair In₁ In₂ Out₁ Out₂ where
  one := fun view => outputOne (L.read Proc.one view)
  two := fun view => outputTwo (L.read Proc.two view)

/--
The real execution prefixes of the readback strategy are the emitted
prefixes of the sequence-driven finite-game play.
-/
theorem executionPrefix_readbackStrategy
    (outputOne : L.Ω Proc.one -> Out₁)
    (outputTwo : L.Ω Proc.two -> Out₂)
    (controller : RoundAwareControllerCode T)
    (hfactor :
      ∀ (state : GameState T) (envRound : EnvironmentRound In₁ In₂),
        controller state envRound =
          (outputOne (L.obs Proc.one state envRound),
            outputTwo (L.obs Proc.two state envRound)))
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    executionPrefix (L.readbackStrategy outputOne outputTwo) env n =
      wordPrefix
        (roundAwareWordOfStateStream T controller
          (sequenceStateStream T initialBoundary controller env) env)
        n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [executionPrefix_succ, wordPrefix, ih]
      congr 1
      have hone :
          (L.readbackStrategy outputOne outputTwo).one
              (nextView Proc.one
                (wordPrefix
                  (roundAwareWordOfStateStream T controller
                    (sequenceStateStream T initialBoundary controller env)
                    env)
                  n)
                (env n)) =
            (controller
              (sequenceStateStream T initialBoundary controller env n)
              (env n)).1 := by
        simp only [readbackStrategy]
        rw [
          L.adequate,
          <- sequenceStateStream_eq_recordFold,
          hfactor
        ]
      have htwo :
          (L.readbackStrategy outputOne outputTwo).two
              (nextView Proc.two
                (wordPrefix
                  (roundAwareWordOfStateStream T controller
                    (sequenceStateStream T initialBoundary controller env)
                    env)
                  n)
                (env n)) =
            (controller
              (sequenceStateStream T initialBoundary controller env n)
              (env n)).2 := by
        simp only [readbackStrategy]
        rw [
          L.adequate,
          <- sequenceStateStream_eq_recordFold,
          hfactor
        ]
      simp [nextRound, roundAwareWordOfStateStream, hone, htwo]

/--
The real executions of the readback strategy are the emitted words of
the sequence-driven finite-game plays: the word-match invariant of the
soundness reduction.
-/
theorem execution_readbackStrategy
    (outputOne : L.Ω Proc.one -> Out₁)
    (outputTwo : L.Ω Proc.two -> Out₂)
    (controller : RoundAwareControllerCode T)
    (hfactor :
      ∀ (state : GameState T) (envRound : EnvironmentRound In₁ In₂),
        controller state envRound =
          (outputOne (L.obs Proc.one state envRound),
            outputTwo (L.obs Proc.two state envRound)))
    (env : EnvironmentSequence In₁ In₂) :
    execution (L.readbackStrategy outputOne outputTwo) env =
      roundAwareWordOfStateStream T controller
        (sequenceStateStream T initialBoundary controller env) env := by
  funext n
  rw [
    execution_apply,
    L.executionPrefix_readbackStrategy outputOne outputTwo controller
      hfactor env n
  ]
  have hone :
      (L.readbackStrategy outputOne outputTwo).one
          (nextView Proc.one
            (wordPrefix
              (roundAwareWordOfStateStream T controller
                (sequenceStateStream T initialBoundary controller env) env)
              n)
            (env n)) =
        (controller
          (sequenceStateStream T initialBoundary controller env n)
          (env n)).1 := by
    simp only [readbackStrategy]
    rw [
      L.adequate,
      <- sequenceStateStream_eq_recordFold,
      hfactor
    ]
  have htwo :
      (L.readbackStrategy outputOne outputTwo).two
          (nextView Proc.two
            (wordPrefix
              (roundAwareWordOfStateStream T controller
                (sequenceStateStream T initialBoundary controller env) env)
              n)
            (env n)) =
        (controller
          (sequenceStateStream T initialBoundary controller env n)
          (env n)).2 := by
    simp only [readbackStrategy]
    rw [
      L.adequate,
      <- sequenceStateStream_eq_recordFold,
      hfactor
    ]
  simp [nextRound, roundAwareWordOfStateStream, hone, htwo]

/--
Soundness of the readback strategy for tracked transformers: an
observation-factored controller winning against every finite
environment code decodes to a distributed strategy all of whose real
executions are accepted.  This is the certificate soundness field with
`controllerStrategy` instantiated by the readback.
-/
theorem strategySound_of_localObservation
    {A :
      DetParityAutomaton.{max u v w a, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (tracking : DPATracking T A)
    [Fintype (GameState T)]
    (hinitial : tracking.boundaryState initialBoundary = A.initial)
    (hautomaton :
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        T.automaton.Accepts word ↔ A.Accepts word)
    (outputOne : L.Ω Proc.one -> Out₁)
    (outputTwo : L.Ω Proc.two -> Out₂)
    (controller : RoundAwareControllerCode T)
    (hfactor :
      ∀ (state : GameState T) (envRound : EnvironmentRound In₁ In₂),
        controller state envRound =
          (outputOne (L.obs Proc.one state envRound),
            outputTwo (L.obs Proc.two state envRound)))
    (hwins :
      ∀ environment : EnvironmentCode T,
        roundAwareGameWins T initialBoundary controller environment) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (execution (L.readbackStrategy outputOne outputTwo) env) :=
  tracking.strategySound_of_executionWordEq initialBoundary hinitial
    hautomaton controller
    (L.readbackStrategy outputOne outputTwo)
    (fun env =>
      L.execution_readbackStrategy outputOne outputTwo controller
        hfactor env)
    hwins

end LocalObservation

end FiniteEpochTransformer

end DistributedSynthesis
