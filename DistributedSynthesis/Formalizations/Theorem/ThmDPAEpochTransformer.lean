/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmAutomataBackend

/-!
# DPA tracking for epoch transformers

This file develops the automaton-tracking layer of Definition
`def:epochtransformer` from `paper.tex`.

A `DPATracking` witness projects the states of a `FiniteEpochTransformer`
to the states of an objective deterministic parity automaton so that
every absorbed round applies the automaton step to the record the game
emits.  Along every finite-game play the projected state then carries
the automaton's run on the emitted word exactly
(`DPATracking.stateOf_stateStream_runFrom`).  Consequently the
certificate soundness field reduces to the word-match invariant alone
(`DPATracking.strategySound_of_executionWordEq`): if the decoded
strategy's real executions are the words emitted along the
sequence-driven finite-game plays, winning against every finite
environment code implies acceptance of every real execution, through
the checked loop-erasure lasso machinery.  The word-match invariant is
the local implementability content of the paper.

Two constructions provide witnesses:

* `DetParityAutomaton.epochTransformer` is the one-directional special
  case of the paper with boundary access states `M_A = S`, noted after
  `def:epochtransformer` to be the construction of Berard et al.; its
  witness is definitional.
* `FiniteEpochTransformer.prod` is the componentwise product of two
  transformers, and `DPATracking.prodFst` transports a witness through
  the first factor.  The journal transformer of the paper is such a
  product: the tracker enriched with regular-test, receipt, and fringe
  data, which decide local implementability but do not affect tracking.
-/

namespace DistributedSynthesis

universe u v w a s z

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace FiniteEpochTransformer

/--
The epoch-game state stream driven by a raw environment sequence rather
than a finite environment code.  This is the play a real environment
traces through the finite game arena.
-/
def sequenceStateStream
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (controller : RoundAwareControllerCode T)
    (env : EnvironmentSequence In₁ In₂) :
    Nat -> GameState T
  | 0 => Sum.inl initialBoundary
  | n + 1 =>
      roundAwareGameTransition T controller
        (sequenceStateStream T initialBoundary controller env n) (env n)

@[simp]
theorem sequenceStateStream_zero
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (controller : RoundAwareControllerCode T)
    (env : EnvironmentSequence In₁ In₂) :
    sequenceStateStream T initialBoundary controller env 0 =
      Sum.inl initialBoundary :=
  rfl

theorem sequenceStateStream_succ
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (controller : RoundAwareControllerCode T)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    sequenceStateStream T initialBoundary controller env (n + 1) =
      roundAwareGameTransition T controller
        (sequenceStateStream T initialBoundary controller env n) (env n) :=
  rfl

/--
A projection of transformer states to automaton states under which every
absorbed round steps the automaton on the emitted record.
-/
structure DPATracking
    (T :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (A :
      DetParityAutomaton.{max u v w a, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)) where
  boundaryState : T.boundary -> A.State
  withinState : (d : Proc) -> T.within d -> A.State
  init_track :
    ∀ (d : Proc) (boundary : T.boundary),
      withinState d (T.init d boundary) = boundaryState boundary
  update_track :
    ∀ (d : Proc) (state : T.within d)
      (inputOne : In₁) (inputTwo : In₂)
      (outputOne : Out₁) (outputTwo : Out₂),
      withinState d (T.update d state inputOne inputTwo outputOne outputTwo) =
        A.step (withinState d state)
          {
            inputOne := inputOne
            inputTwo := inputTwo
            graph := dominantGraph d
            outputOne := outputOne
            outputTwo := outputTwo
          }
  close_track :
    ∀ (d : Proc) (state : T.within d) (graph : Graph)
      (letter : ClosingLetter In₁ In₂ Out₁ Out₂),
      boundaryState (T.close d state graph letter) =
        A.step (withinState d state)
          {
            inputOne := letter.inputOne
            inputTwo := letter.inputTwo
            graph := graph
            outputOne := letter.outputOne
            outputTwo := letter.outputTwo
          }

namespace DPATracking

variable
  {T :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂}
  {A :
    DetParityAutomaton.{max u v w a, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
  (tracking : DPATracking T A)

/-- The automaton state carried by an epoch-game state. -/
def stateOf : GameState T -> A.State
  | Sum.inl boundary => tracking.boundaryState boundary
  | Sum.inr (Sum.inl withinOne) => tracking.withinState Proc.one withinOne
  | Sum.inr (Sum.inr withinTwo) => tracking.withinState Proc.two withinTwo

/--
One round-aware epoch-game transition steps the tracked automaton state
on the emitted round record.
-/
theorem stateOf_roundAwareGameTransition
    (controller : RoundAwareControllerCode T)
    (state : GameState T)
    (envRound : EnvironmentRound In₁ In₂) :
    tracking.stateOf
        (roundAwareGameTransition T controller state envRound) =
      A.step (tracking.stateOf state)
        {
          inputOne := envRound.inputOne
          inputTwo := envRound.inputTwo
          graph := envRound.graph
          outputOne := (controller state envRound).1
          outputTwo := (controller state envRound).2
        } := by
  cases envRound with
  | mk inputOne inputTwo graph =>
      cases state with
      | inl boundary =>
          cases graph <;>
            simp [
              roundAwareGameTransition,
              stateOf,
              tracking.init_track,
              tracking.update_track,
              tracking.close_track,
              dominantGraph
            ]
      | inr side =>
          cases side with
          | inl withinOne =>
              cases graph <;>
                simp [
                  roundAwareGameTransition,
                  stateOf,
                  tracking.update_track,
                  tracking.close_track,
                  dominantGraph
                ]
          | inr withinTwo =>
              cases graph <;>
                simp [
                  roundAwareGameTransition,
                  stateOf,
                  tracking.update_track,
                  tracking.close_track,
                  dominantGraph
                ]

/--
Along every round-aware finite-game play, the tracked automaton state is
the automaton's run on the emitted word, started at the tracked initial
boundary state.
-/
theorem stateOf_stateStream_runFrom
    (initialBoundary : T.boundary)
    (controller : RoundAwareControllerCode T)
    (environment : EnvironmentCode T)
    (n : Nat) :
    tracking.stateOf
        (roundAwareGameStateStream T initialBoundary controller
          environment n) =
      A.runFrom (tracking.boundaryState initialBoundary)
        (roundAwareGameExecution T initialBoundary controller environment)
        n := by
  induction n with
  | zero =>
      simp [roundAwareGameStateStream, DetParityAutomaton.runFrom, stateOf]
  | succ n ih =>
      rw [
        roundAwareGameStateStream,
        DetParityAutomaton.runFrom,
        tracking.stateOf_roundAwareGameTransition,
        ih
      ]
      rfl

/--
The certificate soundness field reduces, for a tracked transformer, to
the word-match invariant.

If the decoded strategy's real execution against every environment
sequence is exactly the word emitted along the sequence-driven
finite-game play, then winning against every finite environment code
implies acceptance of every real execution: a rejected real execution
would trace a rejected DPA-progress stream through the finite arena,
and the checked loop-erasure machinery would produce a rejecting finite
environment code.  The word-match invariant is the local
implementability content of the paper; everything else is discharged.
-/
theorem strategySound_of_executionWordEq
    [Fintype (GameState T)]
    (initialBoundary : T.boundary)
    (hinitial : tracking.boundaryState initialBoundary = A.initial)
    (hautomaton :
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        T.automaton.Accepts word ↔ A.Accepts word)
    (controller : RoundAwareControllerCode T)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hmatch :
      ∀ env : EnvironmentSequence In₁ In₂,
        execution σ env =
          roundAwareWordOfStateStream T controller
            (sequenceStateStream T initialBoundary controller env) env)
    (hwins :
      ∀ environment : EnvironmentCode T,
        roundAwareGameWins T initialBoundary controller environment) :
    ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env) := by
  intro env
  by_contra hreject
  rw [hmatch env] at hreject
  rcases
      exists_environmentCode_rejected_roundAwareGameExecution_of_rejected_dpaProgress_stateStream
        T initialBoundary controller A
        (sequenceStateStream T initialBoundary controller env) env
        tracking.stateOf rfl (fun n => rfl)
        (by simpa [stateOf] using hinitial)
        (fun n => by
          simpa [
            sequenceStateStream,
            roundAwareWordOfStateStream
          ] using
            tracking.stateOf_roundAwareGameTransition controller
              (sequenceStateStream T initialBoundary controller env n)
              (env n))
        hreject with
    ⟨environment, henv⟩
  exact
    henv
      ((hautomaton _).mp
        ((roundAwareGameWins_iff_accepts
            T initialBoundary controller environment).mp
          (hwins environment)))

end DPATracking

end FiniteEpochTransformer

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v w a, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/--
The DPA-tracking epoch transformer: boundary and within-epoch states are
the automaton states, epochs are opened by the identity, and every
absorbed round applies the automaton step to the record it emits.  This
is the one-directional special case `M_A = S` of `def:epochtransformer`,
identified in the paper with the construction of Berard et al.
-/
def epochTransformer :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂ where
  automaton := A
  boundary := A.State
  boundaryFinite := A.stateFinite
  within _ := ULift.{max u v w a} A.State
  withinFinite _ := ULift.fintype A.State
  init _ state := ULift.up state
  update d state inputOne inputTwo outputOne outputTwo :=
    ULift.up
      (A.step state.down
        {
          inputOne := inputOne
          inputTwo := inputTwo
          graph := dominantGraph d
          outputOne := outputOne
          outputTwo := outputTwo
        })
  close _ state graph letter :=
    A.step state.down
      {
        inputOne := letter.inputOne
        inputTwo := letter.inputTwo
        graph := graph
        outputOne := letter.outputOne
        outputTwo := letter.outputTwo
      }
  continuationInvariant := True

/-- The tracking witness of the DPA-tracking transformer is definitional. -/
def epochTransformerTracking :
    FiniteEpochTransformer.DPATracking A.epochTransformer A where
  boundaryState := id
  withinState _ state := state.down
  init_track _ _ := rfl
  update_track _ _ _ _ _ _ := rfl
  close_track _ _ _ _ := rfl

instance :
    Fintype (FiniteEpochTransformer.GameState A.epochTransformer) := by
  unfold DetParityAutomaton.epochTransformer
  exact inferInstanceAs (Fintype (Sum A.State (Sum _ _)))

/--
Started at the automaton's initial state, the DPA-tracking epoch-game
state stream carries exactly the acceptance run of the objective
automaton on the emitted word.
-/
theorem epochTransformerTracking_stateStream_run
    (controller :
      FiniteEpochTransformer.RoundAwareControllerCode A.epochTransformer)
    (environment :
      FiniteEpochTransformer.EnvironmentCode A.epochTransformer)
    (n : Nat) :
    A.epochTransformerTracking.stateOf
        (FiniteEpochTransformer.roundAwareGameStateStream
          A.epochTransformer A.initial controller environment n) =
      A.run
        (FiniteEpochTransformer.roundAwareGameExecution
          A.epochTransformer A.initial controller environment)
        n :=
  A.epochTransformerTracking.stateOf_stateStream_runFrom
    A.initial controller environment n

end DetParityAutomaton

namespace FiniteEpochTransformer

/--
The componentwise product of two epoch transformers.  The objective
automaton and the winning condition come from the first factor; the
second factor rides along as additional finite controller memory, e.g.
the regular-test, receipt, and fringe data of the journal construction.
-/
def prod
    (T₁ :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (T₂ :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂) :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂ where
  automaton := T₁.automaton
  boundary := T₁.boundary × T₂.boundary
  boundaryFinite :=
    letI := T₁.boundaryFinite
    letI := T₂.boundaryFinite
    inferInstance
  within d := T₁.within d × T₂.within d
  withinFinite d :=
    letI := T₁.withinFinite d
    letI := T₂.withinFinite d
    inferInstance
  init d boundary := (T₁.init d boundary.1, T₂.init d boundary.2)
  update d state inputOne inputTwo outputOne outputTwo :=
    (T₁.update d state.1 inputOne inputTwo outputOne outputTwo,
      T₂.update d state.2 inputOne inputTwo outputOne outputTwo)
  close d state graph letter :=
    (T₁.close d state.1 graph letter, T₂.close d state.2 graph letter)
  continuationInvariant :=
    T₁.continuationInvariant ∧ T₂.continuationInvariant

/-- A tracking witness transports through the first product factor. -/
def DPATracking.prodFst
    {T₁ :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂}
    {A :
      DetParityAutomaton.{max u v w a, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (tracking : DPATracking T₁ A)
    (T₂ :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂) :
    DPATracking (T₁.prod T₂) A where
  boundaryState boundary := tracking.boundaryState boundary.1
  withinState d state := tracking.withinState d state.1
  init_track d boundary := tracking.init_track d boundary.1
  update_track d state inputOne inputTwo outputOne outputTwo :=
    tracking.update_track d state.1 inputOne inputTwo outputOne outputTwo
  close_track d state graph letter :=
    tracking.close_track d state.1 graph letter

end FiniteEpochTransformer

end DistributedSynthesis
