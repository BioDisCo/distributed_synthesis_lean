/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBlindKnowledgeGame
import DistributedSynthesis.Formalizations.Lemma.LemReadbackUpgradeReduction
import DistributedSynthesis.Formalizations.Theorem.ThmSummaryMeasurableTransfer

/-!
# Sound readback from the blind knowledge game

This file proves the sound-readback endpoint of the knowledge-arena step of
the summary-fold construction: a positional
Even winner of the blind knowledge game `G†` of
`ThmBlindKnowledgeGame.lean`, whose committed informed tables are position
uniform, reads back to output tables over the knowledge summary automaton
`M*` whose summary controller wins the real round-aware epoch game from the
initial boundary against **every** finite environment code -- the conclusion
shape of `SummaryObservableWinnerCertificate`
(`LemReadbackUpgradeReduction.lean`) at `M*`.

The proof is a play correspondence between real rounds and knowledge-game
rounds, in the `journal_step`/`journal_tracks` induction shape of
`ThmJournalPlayCorrespondence.lean` and the `contingentPlayPath` toolkit of
`ThmEpochArenaAnchor.lean`.  The invariant: along the real play of the
summary controller, the process-one summary carries the tracked knowledge
position at the winner's selector, the process-two summary carries the
informed annotation, the pair of the objective run and the annotation is a
live thread of the tracked belief, and the tracked bundle state is the
bundle automaton's fold of the emitted knowledge letters.  The winner's
parity then transfers through the bundle acceptance characterization
(`blindBundleDPA_accepts_iff`) to acceptance of the real emitted word.

**Flagged hypothesis** (`PositionUniformInformedTables`): the winner's
committed contingent informed tables must agree across staging nodes with a
single table `F`.  This is forced by the model, not by the proof technique:
on rounds on which the designated informed side sends (graph `left`), its
output table can read only its own summary, while the tracked knowledge
position is private to the blind side; a position-varying committed table is
then not reproducible by any fixed readback table. The theorem assumes
this uniformity property together with the winning strategy.
-/

namespace DistributedSynthesis

universe u v w a

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace DetParityAutomaton

open FiniteEpochTransformer

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂]
  (A :
    DetParityAutomaton.{max u v w a, max u v w a}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (N : InformedAnnotationAutomaton.{u, v, w, a} In₁ In₂)

/-- The move selector of an Even positional strategy of the knowledge game:
its committed move at every staging node. -/
noncomputable def knowledgeSelectorOf
    (τ : (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even) :
    KnowledgeSelector A N :=
  fun staging => evenKnowledgeMove A N τ staging

/-- A positional successor strategy realizes a first-class move selector when
its successor at every staging node is exactly the commitment selected by that
selector.  Keeping this witness explicit avoids recovering actions through the
generally non-injective `knowledgeCommitStep`. -/
def SelectorRealizedBy
    (strategy :
      (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (selector : KnowledgeSelector A N) : Prop :=
  ∀ staging : KnowledgeCommitNode A N,
    strategy.move (Sum.inr (Sum.inl staging)) =
      Sum.inl (knowledgeCommitStep A N staging (selector staging))

omit [Fintype Out₁] [Fintype Out₂] in
/-- The selector extracted from an ordinary positional strategy is realized
by that strategy. -/
theorem selectorRealizedBy_knowledgeSelectorOf
    (strategy :
      (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even) :
    SelectorRealizedBy A N strategy (knowledgeSelectorOf A N strategy) :=
  fun staging => evenKnowledgeMove_spec A N strategy staging

/-- The informed component of a selector factors through the fixed finite
annotation table `F`.  This is the selector-first form of the distributed
uniformity condition used by the generalized readback below. -/
def SelectorUniformInformedTables
    (selector : KnowledgeSelector A N) (F : N.Ann -> Out₂) : Prop :=
  ∀ staging : KnowledgeCommitNode A N, (selector staging).2 = F

/-- The process-one readback table: the blind output of the last move
committed on the tracked knowledge position at the supplied selector. -/
noncomputable def readbackOutputOne
    (selector : KnowledgeSelector A N) :
    (knowledgeSummaryAutomaton A N).Summary Proc.one -> Out₁ :=
  fun s => (s selector).2.1

/-- The process-two readback table: the position-uniform informed table
applied to the tracked informed annotation. -/
noncomputable def readbackOutputTwo (F : N.Ann -> Out₂) :
    (knowledgeSummaryAutomaton A N).Summary Proc.two -> Out₂ :=
  fun s => F s.2

/--
**The flagged uniformity hypothesis**: the committed informed tables of the
Even winner agree across staging nodes with the single table `F`.  See the
module docstring for the local-observation condition it expresses.
-/
def PositionUniformInformedTables
    (τ : (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (F : N.Ann -> Out₂) : Prop :=
  ∀ staging : KnowledgeCommitNode A N,
    (evenKnowledgeMove A N τ staging).2 = F

omit [Fintype Out₁] [Fintype Out₂] in
/-- The legacy positional-strategy uniformity condition is exactly selector
uniformity for its chosen selector. -/
theorem positionUniformInformedTables_iff_selectorUniform
    (τ : (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (F : N.Ann -> Out₂) :
    PositionUniformInformedTables A N τ F ↔
      SelectorUniformInformedTables A N (knowledgeSelectorOf A N τ) F :=
  Iff.rfl

omit [Fintype Out₁] [Fintype Out₂] [Inhabited Out₂] in
/-- Legality in the fixed-table subgame exposes a blind output at every Even
staging node; the informed component is definitionally `F`. -/
theorem exists_fixedTableBlindOutput (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even)
    (staging : KnowledgeCommitNode A N) :
    ∃ outputOne : Out₁,
      strategy.move (Sum.inr (Sum.inl staging)) =
        Sum.inl (knowledgeCommitStep A N staging (outputOne, F)) := by
  have hlegal := strategy.legal (Sum.inr (Sum.inl staging)) rfl
  cases hmove : strategy.move (Sum.inr (Sum.inl staging)) with
  | inl node' =>
      rw [hmove] at hlegal
      obtain ⟨outputOne, houtput⟩ :
          ∃ outputOne : Out₁,
            node' = knowledgeCommitStep A N staging (outputOne, F) := by
        simpa [fixedTableKnowledgeGame] using hlegal
      exact ⟨outputOne, congrArg Sum.inl houtput⟩
  | inr q =>
      rw [hmove] at hlegal
      rcases q with staging' | u <;>
        exact absurd hlegal (by simp [fixedTableKnowledgeGame])

/-- The first-class selector carried by a fixed-table positional strategy. -/
noncomputable def fixedTableSelector (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even) :
    KnowledgeSelector A N :=
  fun staging => ((exists_fixedTableBlindOutput A N F strategy staging).choose, F)

omit [Fintype Out₁] [Fintype Out₂] [Inhabited Out₂] in
theorem fixedTableSelector_spec (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even)
    (staging : KnowledgeCommitNode A N) :
    strategy.move (Sum.inr (Sum.inl staging)) =
      Sum.inl
        (knowledgeCommitStep A N staging
          (fixedTableSelector A N F strategy staging)) :=
  (exists_fixedTableBlindOutput A N F strategy staging).choose_spec

/-- Regard a fixed-table strategy as a strategy of the unrestricted knowledge
game.  Odd moves are unchanged and every fixed-table Even move is admitted by
the unrestricted arena. -/
noncomputable def fixedTableStrategyToBlind (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even) :
    (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even where
  move := strategy.move
  legal p hp := by
    apply fixedTableKnowledgeGame_step_mono A N F
    exact strategy.legal p (by simpa using hp)

omit [Fintype Out₁] [Fintype Out₂] in
theorem fixedTableStrategy_realizes_selector (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even) :
    SelectorRealizedBy A N (fixedTableStrategyToBlind A N F strategy)
      (fixedTableSelector A N F strategy) :=
  fixedTableSelector_spec A N F strategy

omit [Fintype Out₁] [Fintype Out₂] [Inhabited Out₂] in
theorem fixedTableSelector_uniform (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even) :
    SelectorUniformInformedTables A N
      (fixedTableSelector A N F strategy) F :=
  fun _ => rfl

omit [Fintype Out₁] [Fintype Out₂] in
/-- Winning transfers from the fixed-table subgame to the unrestricted game.
The arenas differ only at Even moves; consistency forces those moves to be the
fixed-table strategy's legal successors, while Odd moves and priorities are
identical. -/
theorem fixedTableStrategy_winningToBlind (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even)
    (hwinning :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := fixedTableKnowledgeGame A N F) strategy
        (blindKnowledgeGameInitial A N)) :
    CountableParityGame.PositionalStrategy.WinningFrom
      (G := blindKnowledgeGame A N)
      (fixedTableStrategyToBlind A N F strategy)
      (blindKnowledgeGameInitial A N) := by
  intro path hplay hconsistent
  have hfixedPlay :
      (fixedTableKnowledgeGame A N F).PlayFrom
        (blindKnowledgeGameInitial A N) path := by
    refine ⟨hplay.1, fun n => ?_⟩
    cases howner : (blindKnowledgeGame A N).owner (path n) with
    | even =>
        rw [hconsistent n howner]
        exact strategy.legal (path n) (by simpa using howner)
    | odd =>
        exact fixedTableKnowledgeGame_step_of_odd A N F howner (hplay.2 n)
  have hfixedConsistent :
      CountableParityGame.PositionalStrategy.Consistent
        (G := fixedTableKnowledgeGame A N F) strategy path := by
    intro n howner
    exact hconsistent n (by simpa using howner)
  have hwin := hwinning path hfixedPlay hfixedConsistent
  simpa [CountableParityGame.PlayerWinsPath,
    CountableParityGame.MinPriorityEven,
    CountableParityGame.PrioritySeenInfinitelyOften] using hwin

/-- A single dependent finite family containing one Odd positional strategy
for every informed table.  All index and strategy spaces are finite in the
present section; the dependent-function packaging is the spoiler object used
by the Brick-4 contradiction argument. -/
def FixedTableSpoilerFamily : Prop :=
  ∃ spoilers : ∀ F : N.Ann -> Out₂,
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.odd,
    ∀ F : N.Ann -> Out₂,
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := fixedTableKnowledgeGame A N F) (spoilers F)
        (blindKnowledgeGameInitial A N)

omit [Fintype Out₁] [Fintype Out₂] in
/-- If no fixed informed table has an Even positional winner, positional
determinacy supplies the finite family of Odd spoilers.  This closes the pure
game-theory half of D4-B; the remaining completeness work must compile these
spoilers against the alleged realizing distributed strategy. -/
theorem exists_fixedTableSpoilerFamily_of_no_even_winner
    (hno : ∀ (F : N.Ann -> Out₂)
      (strategy :
        (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even),
      ¬ CountableParityGame.PositionalStrategy.WinningFrom
        (G := fixedTableKnowledgeGame A N F) strategy
        (blindKnowledgeGameInitial A N)) :
    FixedTableSpoilerFamily A N := by
  classical
  have hodd : ∀ F : N.Ann -> Out₂,
      ∃ strategy :
          (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.odd,
        CountableParityGame.PositionalStrategy.WinningFrom
          (G := fixedTableKnowledgeGame A N F) strategy
          (blindKnowledgeGameInitial A N) := by
    intro F
    rcases
        (fixedTableKnowledgeGame A N F).positionalGameDetermined
          (blindKnowledgeGameInitial A N) with heven | hodd
    · obtain ⟨strategy, hstrategy⟩ := heven
      exact absurd hstrategy (hno F strategy)
    · exact hodd
  choose spoilers hspoilers using hodd
  exact ⟨spoilers, hspoilers⟩

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited In₁]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- One thread step on the observation and resolution of a real round is the
objective step on the reconstructed real round record. -/
theorem knowledgeThreadStep_round (thread : KnowledgeThread A N)
    (move : KnowledgeMove Out₁ Out₂ N)
    (envRound : EnvironmentRound In₁ In₂) :
    knowledgeThreadStep A N thread
        (roundObservation envRound, move) (roundResolution envRound) =
      (A.step thread.1
          { inputOne := envRound.inputOne
            inputTwo := envRound.inputTwo
            graph := envRound.graph
            outputOne := move.1
            outputTwo := move.2 (N.advanceRound thread.2 envRound) },
        N.advanceRound thread.2 envRound) := by
  cases envRound with
  | mk inputOne inputTwo graph =>
      cases graph <;> rfl

section Correspondence

variable
  (τ : KnowledgeSelector A N)
  (F : N.Ann -> Out₂)
  (environment :
    EnvironmentCode
      (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂)
        (knowledgeSummaryAutomaton A N)))

/-- The summary controller induced by the readback tables. -/
noncomputable def readbackController :
    RoundAwareControllerCode
      (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂)
        (knowledgeSummaryAutomaton A N)) :=
  (A.summaryEpochTransformerTracking
    (knowledgeSummaryAutomaton A N)).summaryController
    (readbackOutputOne A N τ) (readbackOutputTwo A N F)

/-- The real game states along the play of the readback controller. -/
noncomputable def readbackState (n : Nat) :
    GameState
      (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂)
        (knowledgeSummaryAutomaton A N)) :=
  roundAwareGameStateStream (A.summaryEpochTransformer
      (knowledgeSummaryAutomaton A N))
    (A.summaryInitialBoundary (knowledgeSummaryAutomaton A N))
    (readbackController A N τ F) environment n

/-- The real environment rounds along the play. -/
noncomputable def readbackEnv (n : Nat) : EnvironmentRound In₁ In₂ :=
  environment (readbackState A N τ F environment n)

/-- The blind observations along the play. -/
noncomputable def readbackObs (n : Nat) : BlindObservation In₁ In₂ :=
  roundObservation (readbackEnv A N τ F environment n)

/-- The tracked knowledge position and last committed move along the play. -/
noncomputable def readbackTrack : Nat -> KnowledgeTrack A N
  | 0 => initialKnowledgeTrack A N
  | n + 1 =>
      knowledgeTrackStep A N τ
        (readbackTrack n) (readbackObs A N τ F environment n)

/-- The informed annotations along the play. -/
noncomputable def readbackAnn : Nat -> N.Ann
  | 0 => N.init
  | n + 1 =>
      N.advanceRound (readbackAnn n) (readbackEnv A N τ F environment n)

/-- The emitted knowledge letters along the play. -/
noncomputable def readbackLetter (n : Nat) :
    KnowledgeLetter Out₁ Out₂ N :=
  (readbackObs A N τ F environment n,
    τ
      ((readbackTrack A N τ F environment n).1,
        readbackObs A N τ F environment n))

omit [Inhabited In₁] in
/-- The committed move of round `n` is the move component of the next
track. -/
theorem readbackTrack_succ_snd (n : Nat) :
    (readbackTrack A N τ F environment (n + 1)).2 =
      (readbackLetter A N τ F environment n).2 :=
  rfl

omit [Inhabited In₁] in
/-- The next tracked position is the Even commitment at the emitted
letter. -/
theorem readbackTrack_succ_fst (n : Nat) :
    (readbackTrack A N τ F environment (n + 1)).1 =
      knowledgeCommitStep A N
        ((readbackTrack A N τ F environment n).1,
          readbackObs A N τ F environment n)
        (readbackLetter A N τ F environment n).2 :=
  rfl

/-- The summary pair carried by the real game state. -/
noncomputable def readbackSummaryPair (n : Nat) :
    (knowledgeSummaryAutomaton A N).Pair :=
  ((A.summaryEpochTransformerTracking
      (knowledgeSummaryAutomaton A N)).summaryOf
    (readbackState A N τ F environment n))

section
omit [Inhabited In₁]

@[simp]
theorem readbackSummaryPair_zero :
    readbackSummaryPair A N τ F environment 0 =
      ((knowledgeSummaryAutomaton A N).initial Proc.one,
        (knowledgeSummaryAutomaton A N).initial Proc.two) :=
  rfl

/-- One real round advances the carried summary pair by the joint summary
update on the current environment round. -/
theorem readbackSummaryPair_succ (n : Nat) :
    readbackSummaryPair A N τ F environment (n + 1) =
      (knowledgeSummaryAutomaton A N).advance
        (readbackSummaryPair A N τ F environment n)
        (readbackEnv A N τ F environment n).graph
        (readbackEnv A N τ F environment n).inputOne
        (readbackEnv A N τ F environment n).inputTwo := by
  show
    (A.summaryEpochTransformerTracking
        (knowledgeSummaryAutomaton A N)).summaryOf
      (roundAwareGameTransition
        (A.summaryEpochTransformer (knowledgeSummaryAutomaton A N))
        (readbackController A N τ F)
        (readbackState A N τ F environment n)
        (readbackEnv A N τ F environment n)) = _
  rw [←
    recordTransition_emitted
      (A.summaryEpochTransformer (knowledgeSummaryAutomaton A N))
      (readbackController A N τ F)
      (readbackState A N τ F environment n)
      (readbackEnv A N τ F environment n),
    SummaryTracking.summaryOf_recordTransition]
  rfl

/-- **The summary invariant**: along the real play, the process-one summary
at the winner's selector is the tracked knowledge position, and the
process-two summary carries the informed annotation. -/
theorem readbackSummaryPair_track (n : Nat) :
    (readbackSummaryPair A N τ F environment n).1
        τ =
        readbackTrack A N τ F environment n ∧
      (readbackSummaryPair A N τ F environment n).2.2 =
        readbackAnn A N τ F environment n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      rw [readbackSummaryPair_succ,
        knowledgeSummaryAutomaton_advance A N
          (readbackSummaryPair A N τ F environment n)
          (readbackEnv A N τ F environment n)]
      constructor
      · show
          knowledgeTrackStep A N τ
              ((readbackSummaryPair A N τ F environment n).1
                τ)
              (readbackObs A N τ F environment n) =
            readbackTrack A N τ F environment (n + 1)
        rw [ih.1]
        rfl
      · show
          N.advanceRound
              (readbackSummaryPair A N τ F environment n).2.2
              (readbackEnv A N τ F environment n) =
            readbackAnn A N τ F environment (n + 1)
        rw [ih.2]
        rfl

/-- The readback controller plays the committed blind output and the
uniform informed table at the advanced annotation. -/
theorem readbackController_apply (n : Nat) :
    readbackController A N τ F
        (readbackState A N τ F environment n)
        (readbackEnv A N τ F environment n) =
      ((readbackTrack A N τ F environment (n + 1)).2.1,
        F (readbackAnn A N τ F environment (n + 1))) := by
  show
    (readbackOutputOne A N τ
        ((knowledgeSummaryAutomaton A N).component Proc.one
          ((knowledgeSummaryAutomaton A N).advance
            (readbackSummaryPair A N τ F environment n)
            (readbackEnv A N τ F environment n).graph
            (readbackEnv A N τ F environment n).inputOne
            (readbackEnv A N τ F environment n).inputTwo)),
      readbackOutputTwo A N F
        ((knowledgeSummaryAutomaton A N).component Proc.two
          ((knowledgeSummaryAutomaton A N).advance
            (readbackSummaryPair A N τ F environment n)
            (readbackEnv A N τ F environment n).graph
            (readbackEnv A N τ F environment n).inputOne
            (readbackEnv A N τ F environment n).inputTwo))) = _
  rw [← readbackSummaryPair_succ]
  have h := readbackSummaryPair_track A N τ F environment (n + 1)
  show
    (((readbackSummaryPair A N τ F environment (n + 1)).1
        τ).2.1,
      F (readbackSummaryPair A N τ F environment (n + 1)).2.2) = _
  rw [h.1, h.2]

end

/-- The real emitted word of the readback play. -/
noncomputable def readbackExecution :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  roundAwareGameExecution
    (A.summaryEpochTransformer (knowledgeSummaryAutomaton A N))
    (A.summaryInitialBoundary (knowledgeSummaryAutomaton A N))
    (readbackController A N τ F) environment

omit [Inhabited In₁] in
/-- The emitted real round records, componentwise. -/
theorem readbackExecution_apply (n : Nat) :
    readbackExecution A N τ F environment n =
      { inputOne := (readbackEnv A N τ F environment n).inputOne
        inputTwo := (readbackEnv A N τ F environment n).inputTwo
        graph := (readbackEnv A N τ F environment n).graph
        outputOne := (readbackTrack A N τ F environment (n + 1)).2.1
        outputTwo := F (readbackAnn A N τ F environment (n + 1)) } := by
  show
    ({ inputOne := (readbackEnv A N τ F environment n).inputOne
       inputTwo := (readbackEnv A N τ F environment n).inputTwo
       graph := (readbackEnv A N τ F environment n).graph
       outputOne :=
         (readbackController A N τ F
           (readbackState A N τ F environment n)
           (readbackEnv A N τ F environment n)).1
       outputTwo :=
         (readbackController A N τ F
           (readbackState A N τ F environment n)
           (readbackEnv A N τ F environment n)).2 } :
      RoundRecord In₁ In₂ Graph Out₁ Out₂) = _
  rw [readbackController_apply]

/-- The live thread of the real play: the objective run of the emitted word
paired with the informed annotation. -/
noncomputable def readbackThread (n : Nat) : KnowledgeThread A N :=
  (A.run (readbackExecution A N τ F environment) n,
    readbackAnn A N τ F environment n)

section
omit [Inhabited In₁]

/-- **The live thread is a hidden resolution of the emitted letter stream.**
This is where the position-uniformity of the informed tables enters: the
real informed output is the fixed table at the advanced annotation, and the
committed table of the letter agrees with it. -/
theorem readbackThread_isRun
    (hF : SelectorUniformInformedTables A N τ F) :
    (blindThreadSystem A N).IsRun (readbackLetter A N τ F environment)
      (readbackThread A N τ F environment) := by
  refine
    ⟨rfl, fun n =>
      ⟨roundResolution (readbackEnv A N τ F environment n), ?_⟩⟩
  show
    readbackThread A N τ F environment (n + 1) =
      knowledgeThreadStep A N (readbackThread A N τ F environment n)
        (roundObservation (readbackEnv A N τ F environment n),
          (readbackLetter A N τ F environment n).2)
        (roundResolution (readbackEnv A N τ F environment n))
  rw [knowledgeThreadStep_round]
  have hout :
      (readbackLetter A N τ F environment n).2.2 = F :=
    hF
      ((readbackTrack A N τ F environment n).1,
        readbackObs A N τ F environment n)
  show
    (A.step (A.run (readbackExecution A N τ F environment) n)
        (readbackExecution A N τ F environment n),
      readbackAnn A N τ F environment (n + 1)) = _
  rw [readbackExecution_apply, hout]
  rfl

/-- **The live-thread invariant**: the real thread lies in the tracked
belief at every round. -/
theorem readbackThread_mem_belief
    (hF : SelectorUniformInformedTables A N τ F) (n : Nat) :
    readbackThread A N τ F environment n ∈
      (readbackTrack A N τ F environment n).1.1 := by
  induction n with
  | zero => exact Finset.mem_singleton_self _
  | succ n ih =>
      obtain ⟨r, hr⟩ := (readbackThread_isRun A N τ F environment hF).2 n
      rw [readbackTrack_succ_fst]
      exact
        (mem_beliefStep A N).mpr
          ⟨readbackThread A N τ F environment n, ih, r, hr⟩

/-- The tracked bundle state is the bundle automaton's run on the emitted
letter stream. -/
theorem readbackTrack_bundle_run (n : Nat) :
    (readbackTrack A N τ F environment n).1.2 =
      (blindBundleDPA A N).run (readbackLetter A N τ F environment) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [(blindBundleDPA A N).run_succ, ← ih]
      rfl

end

/-- The interleaved knowledge-game play of the real rounds: resolve nodes at
even times, staging nodes at odd times. -/
noncomputable def readbackPlay (k : Nat) :
    (blindKnowledgeGame A N).Position :=
  if k % 2 = 0 then
    Sum.inl (readbackTrack A N τ F environment (k / 2)).1
  else
    Sum.inr
      (Sum.inl
        ((readbackTrack A N τ F environment (k / 2)).1,
          readbackObs A N τ F environment (k / 2)))

theorem readbackPlay_two_mul (n : Nat) :
    readbackPlay A N τ F environment (2 * n) =
      Sum.inl (readbackTrack A N τ F environment n).1 := by
  simp only [readbackPlay]
  rw [if_pos (by omega : 2 * n % 2 = 0), show 2 * n / 2 = n from by omega]

theorem readbackPlay_two_mul_add_one (n : Nat) :
    readbackPlay A N τ F environment (2 * n + 1) =
      Sum.inr
        (Sum.inl
          ((readbackTrack A N τ F environment n).1,
            readbackObs A N τ F environment n)) := by
  simp only [readbackPlay]
  rw [if_neg (by omega : ¬ (2 * n + 1) % 2 = 0),
    show (2 * n + 1) / 2 = n from by omega]

/-- The interleaved play is a play of the knowledge game from the initial
position. -/
theorem readbackPlay_playFrom
    (hF : SelectorUniformInformedTables A N τ F) :
    (blindKnowledgeGame A N).PlayFrom (blindKnowledgeGameInitial A N)
      (readbackPlay A N τ F environment) := by
  constructor
  · rw [show (0 : Nat) = 2 * 0 from rfl, readbackPlay_two_mul]
    rfl
  · intro k
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
    · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
      rw [readbackPlay_two_mul, readbackPlay_two_mul_add_one]
      exact
        ⟨rfl,
          ⟨readbackThread A N τ F environment n,
            readbackThread_mem_belief A N τ F environment hF n⟩⟩
    · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
      rw [readbackPlay_two_mul_add_one,
        show 2 * n + 1 + 1 = 2 * (n + 1) from by omega,
        readbackPlay_two_mul]
      exact
        ⟨(readbackLetter A N τ F environment n).2,
          readbackTrack_succ_fst A N τ F environment n⟩

/-- The interleaved play is consistent with the Even winner. -/
theorem readbackPlay_consistent :
    ∀ (strategy :
        (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even),
      SelectorRealizedBy A N strategy τ ->
    CountableParityGame.PositionalStrategy.Consistent
      (G := blindKnowledgeGame A N) strategy
      (readbackPlay A N τ F environment) := by
  intro strategy hstrategy k howner
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [readbackPlay_two_mul] at howner
    exact absurd howner (by simp [blindKnowledgeGame])
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [readbackPlay_two_mul_add_one,
      show 2 * n + 1 + 1 = 2 * (n + 1) from by omega,
      readbackPlay_two_mul, hstrategy]
    rfl

/-- Priority along the interleaved play reads the tracked bundle state. -/
theorem priority_readbackPlay (k : Nat) :
    (blindKnowledgeGame A N).priority
        (readbackPlay A N τ F environment k) =
      (blindBundleDPA A N).priority
        (readbackTrack A N τ F environment (k / 2)).1.2 := by
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [readbackPlay_two_mul, show 2 * n / 2 = n from by omega]
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [readbackPlay_two_mul_add_one,
      show (2 * n + 1) / 2 = n from by omega]
    rfl

/-- Priority recurrence transfers between the interleaved play and the
bundle run on the emitted letter stream. -/
theorem prioritySeen_readbackPlay_iff (q : Nat) :
    (blindKnowledgeGame A N).PrioritySeenInfinitelyOften
        (readbackPlay A N τ F environment) q ↔
      (blindBundleDPA A N).PrioritySeenInfinitelyOften
        (readbackLetter A N τ F environment) q := by
  constructor
  · intro hseen n
    obtain ⟨k, hk, hkq⟩ := hseen (2 * n)
    refine ⟨k / 2, by omega, ?_⟩
    rw [priority_readbackPlay, readbackTrack_bundle_run] at hkq
    exact hkq
  · intro hseen n
    obtain ⟨m, hm, hmq⟩ := hseen n
    refine ⟨2 * m, by omega, ?_⟩
    rw [priority_readbackPlay, show 2 * m / 2 = m from by omega,
      readbackTrack_bundle_run]
    exact hmq

/-- The interleaved play satisfies the min-even objective iff the bundle
automaton accepts the emitted letter stream. -/
theorem minPriorityEven_readbackPlay_iff_accepts :
    (blindKnowledgeGame A N).MinPriorityEven
        (readbackPlay A N τ F environment) ↔
      (blindBundleDPA A N).Accepts
        (readbackLetter A N τ F environment) := by
  have h := fun q => prioritySeen_readbackPlay_iff A N τ F environment q
  constructor
  · rintro ⟨p, hpe, hps, hpm⟩
    exact ⟨p, hpe, (h p).mp hps, fun q hq => hpm q ((h q).mpr hq)⟩
  · rintro ⟨p, hpe, hps, hpm⟩
    exact ⟨p, hpe, (h p).mpr hps, fun q hq => hpm q ((h q).mp hq)⟩

end Correspondence

/--
**Sound readback from the blind knowledge game** (the endpoint for
paper `prop:starcomplete`): a positional Even winner of the knowledge game
from the initial position, with position-uniform informed tables, yields
output tables over the knowledge summary automaton whose summary controller
wins the real round-aware epoch game from the initial boundary against
every finite environment code -- the `SummaryObservableWinnerCertificate`
conclusion shape at `M*`.
-/
theorem exists_summaryObservableWinner_of_selector_winner
    (selector : KnowledgeSelector A N)
    (strategy : (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (F : N.Ann -> Out₂)
    (hrealizes : SelectorRealizedBy A N strategy selector)
    (hstrategy :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := blindKnowledgeGame A N) strategy (blindKnowledgeGameInitial A N))
    (hF : SelectorUniformInformedTables A N selector F) :
    ∃ (outputOne :
        (knowledgeSummaryAutomaton A N).Summary Proc.one -> Out₁)
      (outputTwo :
        (knowledgeSummaryAutomaton A N).Summary Proc.two -> Out₂),
      ∀ environment :
          EnvironmentCode
            (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂)
              (knowledgeSummaryAutomaton A N)),
        roundAwareGameWins
          (A.summaryEpochTransformer (knowledgeSummaryAutomaton A N))
          (A.summaryInitialBoundary (knowledgeSummaryAutomaton A N))
          ((A.summaryEpochTransformerTracking
              (knowledgeSummaryAutomaton A N)).summaryController
            outputOne outputTwo)
  environment := by
  refine
    ⟨readbackOutputOne A N selector, readbackOutputTwo A N F, fun environment => ?_⟩
  rw [
    roundAwareGameWins_iff_accepts_of_automaton_equiv
      (A.summaryEpochTransformer (knowledgeSummaryAutomaton A N))
      (A.summaryInitialBoundary (knowledgeSummaryAutomaton A N))
      ((A.summaryEpochTransformerTracking
          (knowledgeSummaryAutomaton A N)).summaryController
        (readbackOutputOne A N selector) (readbackOutputTwo A N F))
      environment A (fun _ => Iff.rfl)]
  have haccepts :
      (blindBundleDPA A N).Accepts
        (readbackLetter A N selector F environment) := by
    rw [← minPriorityEven_readbackPlay_iff_accepts]
    have hwin :=
      hstrategy (readbackPlay A N selector F environment)
        (readbackPlay_playFrom A N selector F environment hF)
        (readbackPlay_consistent A N selector F environment strategy hrealizes)
    simpa [CountableParityGame.PlayerWinsPath] using hwin
  have hthreads :=
    (blindBundleDPA_accepts_iff A N
        (readbackLetter A N selector F environment)).mp haccepts
      (readbackThread A N selector F environment)
      (readbackThread_isRun A N selector F environment hF)
  exact hthreads

/-- A winner of the fixed-table subgame reads back immediately: its extracted
selector is uniform by construction and its winning property transfers to the
unrestricted knowledge game. -/
theorem exists_summaryObservableWinner_of_fixedTable_winner
    (F : N.Ann -> Out₂)
    (strategy :
      (fixedTableKnowledgeGame A N F).PositionalStrategy ParityPlayer.even)
    (hstrategy :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := fixedTableKnowledgeGame A N F) strategy
        (blindKnowledgeGameInitial A N)) :
    ∃ (outputOne :
        (knowledgeSummaryAutomaton A N).Summary Proc.one -> Out₁)
      (outputTwo :
        (knowledgeSummaryAutomaton A N).Summary Proc.two -> Out₂),
      ∀ environment :
          EnvironmentCode
            (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂)
              (knowledgeSummaryAutomaton A N)),
        roundAwareGameWins
          (A.summaryEpochTransformer (knowledgeSummaryAutomaton A N))
          (A.summaryInitialBoundary (knowledgeSummaryAutomaton A N))
          ((A.summaryEpochTransformerTracking
              (knowledgeSummaryAutomaton A N)).summaryController
            outputOne outputTwo)
          environment :=
  exists_summaryObservableWinner_of_selector_winner A N
    (fixedTableSelector A N F strategy)
    (fixedTableStrategyToBlind A N F strategy) F
    (fixedTableStrategy_realizes_selector A N F strategy)
    (fixedTableStrategy_winningToBlind A N F strategy hstrategy)
    (fixedTableSelector_uniform A N F strategy)

/-- Compatibility endpoint for an ordinary positional winner.  Its chosen
move selector supplies the first-class selector required above. -/
theorem exists_summaryObservableWinner_of_knowledgeGame_winner
    (τ : (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
    (F : N.Ann -> Out₂)
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := blindKnowledgeGame A N) τ (blindKnowledgeGameInitial A N))
    (hF : PositionUniformInformedTables A N τ F) :
    ∃ (outputOne :
        (knowledgeSummaryAutomaton A N).Summary Proc.one -> Out₁)
      (outputTwo :
        (knowledgeSummaryAutomaton A N).Summary Proc.two -> Out₂),
      ∀ environment :
          EnvironmentCode
            (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂)
              (knowledgeSummaryAutomaton A N)),
        roundAwareGameWins
          (A.summaryEpochTransformer (knowledgeSummaryAutomaton A N))
          (A.summaryInitialBoundary (knowledgeSummaryAutomaton A N))
          ((A.summaryEpochTransformerTracking
              (knowledgeSummaryAutomaton A N)).summaryController
            outputOne outputTwo)
          environment :=
  exists_summaryObservableWinner_of_selector_winner A N
    (knowledgeSelectorOf A N τ) τ F
    (selectorRealizedBy_knowledgeSelectorOf A N τ) hτ
    ((positionUniformInformedTables_iff_selectorUniform A N τ F).mp hF)

/--
**The exact Brick-4 completeness statement.**  For the fixed finite informed
annotation automaton `N`, every realizing distributed strategy can be replaced
by a winning strategy of the blind knowledge game whose informed table factors
through `N.Ann` alone.

This definition deliberately packages the winner and its uniform table
together.  Plain positional determinacy of `blindKnowledgeGame` only produces
an unrestricted positional winner and does not imply
`PositionUniformInformedTables`; the latter is the distributed-observation
content of the hierarchical finite-memory theorem.
-/
def BlindKnowledgeCompleteness : Prop :=
  ∀ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution σ env)) ->
      ∃ (τ : (blindKnowledgeGame A N).PositionalStrategy ParityPlayer.even)
        (F : N.Ann -> Out₂),
        CountableParityGame.PositionalStrategy.WinningFrom
            (G := blindKnowledgeGame A N) τ (blindKnowledgeGameInitial A N) ∧
          PositionUniformInformedTables A N τ F

/--
A strong, mechanically clean **sufficient** Brick-4 target: for one fixed
finite annotation automaton `N`, every realizing distributed strategy yields
some fixed informed table `F` for which Even wins the fixed-table knowledge
subgame.  Unlike `BlindKnowledgeCompleteness`, this statement contains no
post-hoc uniformity condition and no action-recovery ambiguity.

It is not claimed for the full model with the present
`InformedAnnotationAutomaton` interface: `N.stepRecv` sees only the current
inputs, whereas a real receive reveals the partner's previous recursive view.
Consequently a legal informed output can depend on received partner history
that `N.Ann` cannot reconstruct.  The fixed-table theorem remains useful for
the restricted flat-observation case and as sound infrastructure for a future
full-local-summary table domain.
-/
def FixedTableKnowledgeCompleteness : Prop :=
  ∀ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution σ env)) ->
      ∃ (F : N.Ann -> Out₂)
        (strategy :
          (fixedTableKnowledgeGame A N F).PositionalStrategy
            ParityPlayer.even),
        CountableParityGame.PositionalStrategy.WinningFrom
          (G := fixedTableKnowledgeGame A N F) strategy
          (blindKnowledgeGameInitial A N)

/--
**Brick 4 closes the principled finite-game certificate.**  Once
`BlindKnowledgeCompleteness A N` is proved, the sound readback theorem above
supplies `SummaryObservableWinnerCertificate` for the concrete, finite
`knowledgeSummaryAutomaton A N`.  All later adapters to `ReadbackUpgrade` and
the full-LTL synthesis endpoint are therefore already available.
-/
theorem summaryObservableWinnerCertificate_of_blindKnowledgeCompleteness
    (hcomplete : BlindKnowledgeCompleteness A N) :
    SummaryObservableWinnerCertificate A (knowledgeSummaryAutomaton A N) := by
  intro σ hσ
  obtain ⟨τ, F, hτ, hF⟩ := hcomplete σ hσ
  exact exists_summaryObservableWinner_of_knowledgeGame_winner A N τ F hτ hF

/-- The strong fixed-table completeness target, when available, closes the
same certificate without passing through `Classical.choose` action recovery. -/
theorem summaryObservableWinnerCertificate_of_fixedTableKnowledgeCompleteness
    (hcomplete : FixedTableKnowledgeCompleteness A N) :
    SummaryObservableWinnerCertificate A (knowledgeSummaryAutomaton A N) := by
  intro σ hσ
  obtain ⟨F, strategy, hstrategy⟩ := hcomplete σ hσ
  exact
    exists_summaryObservableWinner_of_fixedTable_winner A N F strategy hstrategy

end DetParityAutomaton

end DistributedSynthesis
