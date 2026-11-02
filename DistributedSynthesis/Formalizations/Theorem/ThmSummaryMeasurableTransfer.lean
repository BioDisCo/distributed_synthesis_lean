/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# Transfer of summary-measurable winning strategies to the finite game

This file proves the transfer half of the epoch-game certificate
completeness field for `def:epochtransformer` from `paper.tex`.

A distributed strategy is summary measurable when it is the readback of
output tables over a `LocalSummaryAutomaton`.  For such a strategy the
summary-factored finite controller plays, against every finite
environment code, exactly the rounds the strategy plays against the
induced real environment sequence: the game states along the play are
the sequence-driven states of the induced sequence, and the emitted
word is the strategy's real execution
(`SummaryTracking.roundAwareGameExecution_readback`, from the adequacy
law of `ThmLocalSummaryAutomaton.lean`).  Consequently, if every real
execution of the strategy is accepted, the factored controller wins the
finite game against every environment code
(`SummaryTracking.exists_lambdaController_wins_of_readback_accepts`),
and the controller is locally observable by finite lambda decoders
because it factors through the summary observations.

What remains for the certificate `complete` field is the measurability
upgrade of `prop:journalgivesuniform`: every winning distributed
strategy is dominated by a winning summary-measurable one.  The
per-round matching interface (`matchingControllers` of
`ofTransformerWithSoundAndFiniteViewStateDecoders`) is not used here.
-/

namespace DistributedSynthesis

universe u v w a s z o b x

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace FiniteEpochTransformer

/--
Along a finite-game play, the sequence-driven state stream of the
induced real environment sequence is the game state stream.
-/
theorem sequenceStateStream_environmentSequenceOfGamePlay
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (controller : RoundAwareControllerCode T)
    (environment : EnvironmentCode T)
    (n : Nat) :
    sequenceStateStream T initialBoundary controller
        (roundAwareEnvironmentSequenceOfGamePlay
          T initialBoundary controller environment) n =
      roundAwareGameStateStream T initialBoundary controller
        environment n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [
        sequenceStateStream_succ,
        roundAwareGameStateStream_succ,
        ih
      ]
      rfl

/--
Along a finite-game play, the word emitted over the sequence-driven
states of the induced real environment sequence is the finite-game
execution.
-/
theorem roundAwareWordOfStateStream_environmentSequenceOfGamePlay
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (initialBoundary : T.boundary)
    (controller : RoundAwareControllerCode T)
    (environment : EnvironmentCode T) :
    roundAwareWordOfStateStream T controller
        (sequenceStateStream T initialBoundary controller
          (roundAwareEnvironmentSequenceOfGamePlay
            T initialBoundary controller environment))
        (roundAwareEnvironmentSequenceOfGamePlay
          T initialBoundary controller environment) =
      roundAwareGameExecution T initialBoundary controller environment := by
  funext n
  simp only [
    roundAwareWordOfStateStream,
    sequenceStateStream_environmentSequenceOfGamePlay
  ]
  rfl

namespace SummaryTracking

variable
  {T :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂}
  {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂}
  (tracking : SummaryTracking T M)

/--
The finite lambda fringe decoder of side `d`: the current summary of
`d`, read from the game state advanced by the current environment move.
This is the game-side observation of the adequate local observation.
-/
def fringeDecoder (d : Proc) :
    GameState T -> EnvironmentRound In₁ In₂ -> M.Summary d :=
  fun state envRound =>
    M.component d
      (M.advance (tracking.summaryOf state) envRound.graph
        envRound.inputOne envRound.inputTwo)

/-- The finite controller reading its outputs off the current summaries. -/
def summaryController
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂) :
    RoundAwareControllerCode T :=
  fun state envRound =>
    (outputOne (tracking.fringeDecoder Proc.one state envRound),
      outputTwo (tracking.fringeDecoder Proc.two state envRound))

/--
The summary controller is locally observable by finite lambda decoders
for every choice of history decoders: its outputs factor through the
fringe decoders alone.
-/
theorem summaryController_locallyObservable
    {H₁ : Type b} {H₂ : Type x}
    (historyOne :
      GameState T -> EnvironmentRound In₁ In₂ -> List H₁)
    (historyTwo :
      GameState T -> EnvironmentRound In₁ In₂ -> List H₂)
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂) :
    RoundAwareControllerLocallyObservableByFiniteLambda
      T historyOne historyTwo
      (tracking.fringeDecoder Proc.one) (tracking.fringeDecoder Proc.two)
      (tracking.summaryController outputOne outputTwo) := by
  constructor
  · intro stateA envA stateB envB _hhistory hfringe
    simp [summaryController, hfringe]
  · intro stateA envA stateB envB _hhistory hfringe
    simp [summaryController, hfringe]

/--
Along every finite-game play of the summary controller, the emitted
word is the real execution of the summary readback strategy against the
induced environment sequence.
-/
theorem roundAwareGameExecution_readback
    (initialBoundary : T.boundary)
    (hinitial :
      tracking.boundarySummary initialBoundary =
        (M.initial Proc.one, M.initial Proc.two))
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂)
    (environment : EnvironmentCode T) :
    roundAwareGameExecution T initialBoundary
        (tracking.summaryController outputOne outputTwo) environment =
      execution (M.readbackStrategy outputOne outputTwo)
        (roundAwareEnvironmentSequenceOfGamePlay T initialBoundary
          (tracking.summaryController outputOne outputTwo) environment) := by
  have hexec :=
    (tracking.localObservation initialBoundary hinitial).execution_readbackStrategy
      outputOne outputTwo
      (tracking.summaryController outputOne outputTwo)
      (fun state envRound => rfl)
      (roundAwareEnvironmentSequenceOfGamePlay T initialBoundary
        (tracking.summaryController outputOne outputTwo) environment)
  rw [roundAwareWordOfStateStream_environmentSequenceOfGamePlay] at hexec
  exact hexec.symm

/--
Transfer of summary-measurable winning strategies: if every real
execution of the summary readback strategy is accepted by the objective
automaton, the summary controller wins the finite game against every
finite environment code.
-/
theorem roundAwareGameWins_summaryController_of_readback_accepts
    {A :
      DetParityAutomaton.{max u v w a, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (initialBoundary : T.boundary)
    (hinitial :
      tracking.boundarySummary initialBoundary =
        (M.initial Proc.one, M.initial Proc.two))
    (hautomaton :
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        T.automaton.Accepts word ↔ A.Accepts word)
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂)
    (haccepts :
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts
          (execution (M.readbackStrategy outputOne outputTwo) env)) :
    ∀ environment : EnvironmentCode T,
      roundAwareGameWins T initialBoundary
        (tracking.summaryController outputOne outputTwo) environment := by
  intro environment
  rw [
    roundAwareGameWins_iff_accepts_of_automaton_equiv T initialBoundary
      (tracking.summaryController outputOne outputTwo) environment
      A hautomaton,
    tracking.roundAwareGameExecution_readback initialBoundary hinitial
      outputOne outputTwo environment
  ]
  exact haccepts _

/--
The certificate completeness field for summary-measurable strategies:
a winning summary readback strategy is matched by a winning finite
lambda controller, for every choice of history decoders.  The remaining
obligation of `complete` is the measurability upgrade: every winning
distributed strategy is dominated by a winning summary readback.
-/
theorem exists_lambdaController_wins_of_readback_accepts
    {A :
      DetParityAutomaton.{max u v w a, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (initialBoundary : T.boundary)
    (hinitial :
      tracking.boundarySummary initialBoundary =
        (M.initial Proc.one, M.initial Proc.two))
    (hautomaton :
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        T.automaton.Accepts word ↔ A.Accepts word)
    {H₁ : Type b} {H₂ : Type x}
    (historyOne :
      GameState T -> EnvironmentRound In₁ In₂ -> List H₁)
    (historyTwo :
      GameState T -> EnvironmentRound In₁ In₂ -> List H₂)
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂)
    (haccepts :
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts
          (execution (M.readbackStrategy outputOne outputTwo) env)) :
    ∃ controller :
        T.RoundAwareLambdaControllerCode historyOne historyTwo
          (tracking.fringeDecoder Proc.one)
          (tracking.fringeDecoder Proc.two),
      ∀ environment : EnvironmentCode T,
        roundAwareGameWins T initialBoundary controller.1 environment :=
  ⟨⟨tracking.summaryController outputOne outputTwo,
      tracking.summaryController_locallyObservable historyOne historyTwo
        outputOne outputTwo⟩,
    tracking.roundAwareGameWins_summaryController_of_readback_accepts
      initialBoundary hinitial hautomaton outputOne outputTwo haccepts⟩

end SummaryTracking

end FiniteEpochTransformer

end DistributedSynthesis
