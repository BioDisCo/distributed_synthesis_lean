/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmEpochLocalObservation

/-!
# Local summary automata and adequate observations

This file constructs adequate local observations (in the sense of
`ThmEpochLocalObservation.lean`) for epoch transformers of the journal
shape from `paper.tex`, closing the soundness half of the epoch-game
certificate for every finite choice of per-side summaries.

A `LocalSummaryAutomaton` is a pair of finite automata, one per process,
reading exactly the observation increments of Definition `def:views`: a
`noRecv` step consumes the own input of a non-dominant round, and a
`recv` step consumes both inputs together with the sender's summary.
Its fold over a view (`LocalSummaryAutomaton.read`) is therefore
computable by the process from its own view alone.  The joint one-round
update (`LocalSummaryAutomaton.advance`) mirrors `advanceViews`; in
particular the receiver's update on a dominant round coincides with its
update on a `both` round, exactly as its view does (the one-bit fringe
of `thm:onebitfringe`), and no update reads an output.  These two
invariances are what make the adequacy law provable over arbitrary
recorded histories rather than only along plays of a fixed strategy.

A `FiniteEpochTransformer.SummaryTracking` witness projects transformer
states to the joint summary pair so that every absorbed round applies
`advance`.  The projection then agrees with the view folds along every
recorded history (`SummaryTracking.summaryOf_recordFold`), which is the
adequacy field of the induced observation
(`SummaryTracking.localObservation`).  Combining with a `DPATracking`
witness yields the certificate soundness statement: a finite-game
controller whose outputs factor through the current summaries decodes
to the distributed readback strategy, and winning against every finite
environment code implies acceptance of every real execution
(`SummaryTracking.strategySound`).

The journal transformer of the paper is assembled as the product of the
DPA tracker with the summary carrier
(`DetParityAutomaton.summaryEpochTransformer`); its tracking witnesses
transport through the product factors, giving the endpoint
`DetParityAutomaton.summaryEpochTransformer_strategySound`, the sound
half of the epoch-game certificate parametric in the summary automaton.
-/

namespace DistributedSynthesis

universe u v w a s z o

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

/--
One finite summary automaton per process, reading the observation
increments of Definition `def:views`.  On a received round the other
process's view enters only through its summary, never verbatim, so the
summary state spaces stay finite while views grow.
-/
structure LocalSummaryAutomaton (In₁ : Type u) (In₂ : Type v) where
  Summary : Proc -> Type o
  finite : (d : Proc) -> Fintype (Summary d)
  initial : (d : Proc) -> Summary d
  stepNoRecv : (d : Proc) -> Summary d -> PSum In₁ In₂ -> Summary d
  stepRecv :
    (d : Proc) -> Summary d -> PSum In₁ In₂ ->
      Summary d.other -> PSum In₁ In₂ -> Summary d

attribute [instance] LocalSummaryAutomaton.finite

namespace LocalSummaryAutomaton

variable (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)

/-- The joint summary pair of the two processes. -/
abbrev Pair : Type o := M.Summary Proc.one × M.Summary Proc.two

/-- The summary of one side of the joint pair. -/
def component : (d : Proc) -> M.Pair -> M.Summary d
  | .one, pair => pair.1
  | .two, pair => pair.2

/-- The summary a process computes from its own view. -/
def read : {d : Proc} -> View In₁ In₂ d -> M.Summary d
  | _, .empty p => M.initial p
  | _, .noRecv prevSelf inputSelf =>
      M.stepNoRecv _ (read prevSelf) inputSelf
  | _, .recv prevSelf inputSelf prevOther inputOther =>
      M.stepRecv _ (read prevSelf) inputSelf (read prevOther) inputOther

@[simp]
theorem read_empty (p : Proc) :
    M.read (View.empty p : View In₁ In₂ p) = M.initial p :=
  rfl

@[simp]
theorem read_noRecv {p : Proc}
    (prevSelf : View In₁ In₂ p) (inputSelf : PSum In₁ In₂) :
    M.read (View.noRecv prevSelf inputSelf) =
      M.stepNoRecv p (M.read prevSelf) inputSelf :=
  rfl

@[simp]
theorem read_recv {p : Proc}
    (prevSelf : View In₁ In₂ p) (inputSelf : PSum In₁ In₂)
    (prevOther : View In₁ In₂ p.other) (inputOther : PSum In₁ In₂) :
    M.read (View.recv prevSelf inputSelf prevOther inputOther) =
      M.stepRecv p (M.read prevSelf) inputSelf
        (M.read prevOther) inputOther :=
  rfl

/--
The joint one-round update of the two summaries.  It mirrors
`advanceViews`: the receiver of the round steps by `stepRecv` on both
inputs and the sender's previous summary, the sender by `stepNoRecv` on
its own input, and a `both` round steps both sides by `stepRecv`.  No
case reads an output, and the updates on a dominant round and on a
`both` round agree for the receiving side, exactly as the views do.
-/
def advance (pair : M.Pair) (graph : Graph)
    (inputOne : In₁) (inputTwo : In₂) : M.Pair :=
  match graph with
  | .left =>
      (M.stepRecv Proc.one pair.1 (.inl inputOne) pair.2 (.inr inputTwo),
        M.stepNoRecv Proc.two pair.2 (.inr inputTwo))
  | .right =>
      (M.stepNoRecv Proc.one pair.1 (.inl inputOne),
        M.stepRecv Proc.two pair.2 (.inr inputTwo) pair.1 (.inl inputOne))
  | .both =>
      (M.stepRecv Proc.one pair.1 (.inl inputOne) pair.2 (.inr inputTwo),
        M.stepRecv Proc.two pair.2 (.inr inputTwo) pair.1 (.inl inputOne))

/-- The joint summary pair computed from the two views. -/
def readPair
    (views : View In₁ In₂ Proc.one × View In₁ In₂ Proc.two) : M.Pair :=
  (M.read views.1, M.read views.2)

/-- One recorded round advances the view summaries by the joint update. -/
theorem readPair_advanceViews
    (views : View In₁ In₂ Proc.one × View In₁ In₂ Proc.two)
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    M.readPair (advanceViews views round) =
      M.advance (M.readPair views) round.graph
        round.inputOne round.inputTwo := by
  cases hGraph : round.graph <;>
    simp [readPair, advanceViews, advance, hGraph] <;>
      first
        | rfl
        | exact ⟨rfl, rfl⟩

/-- One environment move advances the view summaries by the joint update. -/
theorem readPair_advanceViewsWithEnvironment
    (views : View In₁ In₂ Proc.one × View In₁ In₂ Proc.two)
    (envRound : EnvironmentRound In₁ In₂) :
    M.readPair (advanceViewsWithEnvironment views envRound) =
      M.advance (M.readPair views) envRound.graph
        envRound.inputOne envRound.inputTwo := by
  cases hGraph : envRound.graph <;>
    simp [readPair, advanceViewsWithEnvironment, advance, hGraph] <;>
      first
        | rfl
        | exact ⟨rfl, rfl⟩

/--
The distributed strategy induced by output tables over the summaries:
each process folds its view through its summary automaton and applies
its table.
-/
def readbackStrategy
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂) :
    StrategyPair In₁ In₂ Out₁ Out₂ where
  one := fun view => outputOne (M.read view)
  two := fun view => outputTwo (M.read view)

end LocalSummaryAutomaton

namespace FiniteEpochTransformer

/--
A projection of transformer states to the joint summary pair under which
every absorbed round applies the joint summary update.
-/
structure SummaryTracking
    (T :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) where
  boundarySummary : T.boundary -> M.Pair
  withinSummary : (d : Proc) -> T.within d -> M.Pair
  init_summary :
    ∀ (d : Proc) (boundary : T.boundary),
      withinSummary d (T.init d boundary) = boundarySummary boundary
  update_summary :
    ∀ (d : Proc) (state : T.within d)
      (inputOne : In₁) (inputTwo : In₂)
      (outputOne : Out₁) (outputTwo : Out₂),
      withinSummary d (T.update d state inputOne inputTwo outputOne outputTwo) =
        M.advance (withinSummary d state) (dominantGraph d) inputOne inputTwo
  close_summary :
    ∀ (d : Proc) (state : T.within d) (graph : Graph)
      (letter : ClosingLetter In₁ In₂ Out₁ Out₂),
      boundarySummary (T.close d state graph letter) =
        M.advance (withinSummary d state) graph
          letter.inputOne letter.inputTwo

namespace SummaryTracking

variable
  {T :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂}
  {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂}
  (tracking : SummaryTracking T M)

/-- The joint summary pair carried by an epoch-game state. -/
def summaryOf : GameState T -> M.Pair
  | Sum.inl boundary => tracking.boundarySummary boundary
  | Sum.inr (Sum.inl withinOne) => tracking.withinSummary Proc.one withinOne
  | Sum.inr (Sum.inr withinTwo) => tracking.withinSummary Proc.two withinTwo

/-- One controller-free epoch fold step applies the joint summary update. -/
theorem summaryOf_recordTransition
    (state : GameState T)
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    tracking.summaryOf (recordTransition T state round) =
      M.advance (tracking.summaryOf state) round.graph
        round.inputOne round.inputTwo := by
  cases state with
  | inl boundary =>
      cases hGraph : round.graph <;>
        simp [
          recordTransition,
          summaryOf,
          hGraph,
          tracking.init_summary,
          tracking.update_summary,
          tracking.close_summary,
          dominantGraph,
          roundRecordClosingLetter
        ]
  | inr side =>
      cases side with
      | inl withinOne =>
          cases hGraph : round.graph <;>
            simp [
              recordTransition,
              summaryOf,
              hGraph,
              tracking.update_summary,
              tracking.close_summary,
              dominantGraph,
              roundRecordClosingLetter
            ]
      | inr withinTwo =>
          cases hGraph : round.graph <;>
            simp [
              recordTransition,
              summaryOf,
              hGraph,
              tracking.update_summary,
              tracking.close_summary,
              dominantGraph,
              roundRecordClosingLetter
            ]

/--
Along every recorded history, the tracked summary pair is the pair of
view folds.  Outputs never enter: both sides of the equation are
functions of the inputs and graphs alone.
-/
theorem summaryOf_recordFold
    (initialBoundary : T.boundary)
    (hinitial :
      tracking.boundarySummary initialBoundary =
        (M.initial Proc.one, M.initial Proc.two))
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    tracking.summaryOf (recordFold T initialBoundary history) =
      M.readPair (viewPair history) := by
  induction history using List.reverseRecOn with
  | nil =>
      simpa [
        summaryOf,
        LocalSummaryAutomaton.readPair
      ] using hinitial
  | append_singleton history round ih =>
      show
        tracking.summaryOf
            (recordFold T initialBoundary (History.append history round)) =
          M.readPair (viewPair (History.append history round))
      rw [
        recordFold_append,
        tracking.summaryOf_recordTransition,
        ih,
        viewPair_append,
        M.readPair_advanceViews
      ]

/--
The adequate local observation induced by a summary tracking: the
game-side observation advances the tracked pair by the current
environment move, and the view-side observation folds the view through
the summary automaton.
-/
def localObservation
    (initialBoundary : T.boundary)
    (hinitial :
      tracking.boundarySummary initialBoundary =
        (M.initial Proc.one, M.initial Proc.two)) :
    LocalObservation T initialBoundary where
  Ω := M.Summary
  obs d state envRound :=
    M.component d
      (M.advance (tracking.summaryOf state) envRound.graph
        envRound.inputOne envRound.inputTwo)
  read d view := M.read view
  adequate := by
    intro d history envRound
    cases d with
    | one =>
        show
          (M.readPair
              (advanceViewsWithEnvironment (viewPair history) envRound)).1 =
            M.component Proc.one
              (M.advance
                (tracking.summaryOf (recordFold T initialBoundary history))
                envRound.graph envRound.inputOne envRound.inputTwo)
        rw [
          M.readPair_advanceViewsWithEnvironment,
          tracking.summaryOf_recordFold initialBoundary hinitial history
        ]
        rfl
    | two =>
        show
          (M.readPair
              (advanceViewsWithEnvironment (viewPair history) envRound)).2 =
            M.component Proc.two
              (M.advance
                (tracking.summaryOf (recordFold T initialBoundary history))
                envRound.graph envRound.inputOne envRound.inputTwo)
        rw [
          M.readPair_advanceViewsWithEnvironment,
          tracking.summaryOf_recordFold initialBoundary hinitial history
        ]
        rfl

/--
Soundness of the summary readback for tracked transformers: a
finite-game controller whose outputs factor through the current
summaries and which wins against every finite environment code decodes
to a distributed strategy all of whose real executions are accepted.
-/
theorem strategySound
    {A :
      DetParityAutomaton.{max u v w a, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (dpaTracking : DPATracking T A)
    [Fintype (GameState T)]
    (initialBoundary : T.boundary)
    (hboundary :
      tracking.boundarySummary initialBoundary =
        (M.initial Proc.one, M.initial Proc.two))
    (hinitial : dpaTracking.boundaryState initialBoundary = A.initial)
    (hautomaton :
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        T.automaton.Accepts word ↔ A.Accepts word)
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂)
    (controller : RoundAwareControllerCode T)
    (hfactor :
      ∀ (state : GameState T) (envRound : EnvironmentRound In₁ In₂),
        controller state envRound =
          (outputOne
              (M.component Proc.one
                (M.advance (tracking.summaryOf state) envRound.graph
                  envRound.inputOne envRound.inputTwo)),
            outputTwo
              (M.component Proc.two
                (M.advance (tracking.summaryOf state) envRound.graph
                  envRound.inputOne envRound.inputTwo))))
    (hwins :
      ∀ environment : EnvironmentCode T,
        roundAwareGameWins T initialBoundary controller environment) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (execution (M.readbackStrategy outputOne outputTwo) env) :=
  (tracking.localObservation initialBoundary hboundary).strategySound_of_localObservation
    dpaTracking hinitial hautomaton outputOne outputTwo controller
    hfactor hwins

end SummaryTracking

/-- The finite rotating game state space of an epoch transformer. -/
@[reducible]
def gameStateFintype
    (T :
      FiniteEpochTransformer
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂) :
    Fintype (GameState T) :=
  letI := T.boundaryFinite
  letI := T.withinFinite Proc.one
  letI := T.withinFinite Proc.two
  inferInstanceAs
    (Fintype (Sum T.boundary (Sum (T.within Proc.one) (T.within Proc.two))))

/-- A summary tracking witness transports through the second product factor. -/
def SummaryTracking.prodSnd
    {T₂ :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂}
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂}
    (tracking : SummaryTracking T₂ M)
    (T₁ :
      FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂) :
    SummaryTracking (T₁.prod T₂) M where
  boundarySummary boundary := tracking.boundarySummary boundary.2
  withinSummary d state := tracking.withinSummary d state.2
  init_summary d boundary := tracking.init_summary d boundary.2
  update_summary d state inputOne inputTwo outputOne outputTwo :=
    tracking.update_summary d state.2 inputOne inputTwo outputOne outputTwo
  close_summary d state graph letter :=
    tracking.close_summary d state.2 graph letter

end FiniteEpochTransformer

namespace LocalSummaryAutomaton

/--
The summary carrier transformer: boundary and within-epoch states are
the joint summary pair, epochs are opened by the identity, and every
absorbed round applies the joint summary update.  It rides along as the
second factor of the journal product, supplying the per-side finite
observations that decide local implementability.
-/
def carrier
    (M : LocalSummaryAutomaton.{u, v, z} In₁ In₂)
    (automaton :
      DetParityAutomaton.{max u v w a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂ where
  automaton := automaton
  boundary := M.Pair
  boundaryFinite := inferInstance
  within _ := ULift.{max u v w a} M.Pair
  withinFinite _ := ULift.fintype M.Pair
  init _ pair := ULift.up pair
  update d state inputOne inputTwo _outputOne _outputTwo :=
    ULift.up (M.advance state.down (dominantGraph d) inputOne inputTwo)
  close _ state graph letter :=
    M.advance state.down graph letter.inputOne letter.inputTwo
  continuationInvariant := True

/-- The summary tracking witness of the carrier is definitional. -/
def carrierTracking
    (M : LocalSummaryAutomaton.{u, v, z} In₁ In₂)
    (automaton :
      DetParityAutomaton.{max u v w a, z}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    FiniteEpochTransformer.SummaryTracking
      (M.carrier (Out₁ := Out₁) (Out₂ := Out₂) automaton) M where
  boundarySummary := id
  withinSummary _ state := state.down
  init_summary _ _ := rfl
  update_summary _ _ _ _ _ _ := rfl
  close_summary _ _ _ _ := rfl

end LocalSummaryAutomaton

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v w a, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, v, s} In₁ In₂)

/--
The journal-shape epoch transformer: the DPA tracker enriched with the
per-side summary carrier.  The objective automaton and the winning
condition come from the tracker; the summaries decide local
implementability.
-/
def summaryEpochTransformer :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂ :=
  (A.epochTransformer (Out₁ := Out₁) (Out₂ := Out₂)).prod (M.carrier A)

/-- The initial boundary of the journal-shape transformer. -/
def summaryInitialBoundary :
    (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M).boundary :=
  (A.initial, (M.initial Proc.one, M.initial Proc.two))

/-- The summary tracking of the journal-shape transformer. -/
def summaryEpochTransformerTracking :
    FiniteEpochTransformer.SummaryTracking
      (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M) M :=
  (M.carrierTracking A).prodSnd (A.epochTransformer)

instance :
    Fintype
      (FiniteEpochTransformer.GameState
        (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M)) :=
  FiniteEpochTransformer.gameStateFintype _

/--
The sound half of the epoch-game certificate for the journal-shape
transformer, parametric in the summary automaton: a finite-game
controller whose outputs factor through the current summaries and which
wins against every finite environment code decodes to the summary
readback strategy, all of whose real executions are accepted by the
objective automaton.
-/
theorem summaryEpochTransformer_strategySound
    (outputOne : M.Summary Proc.one -> Out₁)
    (outputTwo : M.Summary Proc.two -> Out₂)
    (controller :
      FiniteEpochTransformer.RoundAwareControllerCode
        (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M))
    (hfactor :
      ∀ (state :
          FiniteEpochTransformer.GameState
            (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M))
        (envRound : EnvironmentRound In₁ In₂),
        controller state envRound =
          (outputOne
              (M.component Proc.one
                (M.advance
                  ((A.summaryEpochTransformerTracking
                      (Out₁ := Out₁) (Out₂ := Out₂) M).summaryOf state)
                  envRound.graph envRound.inputOne envRound.inputTwo)),
            outputTwo
              (M.component Proc.two
                (M.advance
                  ((A.summaryEpochTransformerTracking
                      (Out₁ := Out₁) (Out₂ := Out₂) M).summaryOf state)
                  envRound.graph envRound.inputOne envRound.inputTwo))))
    (hwins :
      ∀ environment :
          FiniteEpochTransformer.EnvironmentCode
            (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M),
        FiniteEpochTransformer.roundAwareGameWins
          (A.summaryEpochTransformer M)
          (A.summaryInitialBoundary M) controller environment) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (execution (M.readbackStrategy outputOne outputTwo) env) :=
  (A.summaryEpochTransformerTracking M).strategySound
    (A.epochTransformerTracking.prodFst (M.carrier A))
    (A.summaryInitialBoundary M) rfl rfl (fun _ => Iff.rfl)
    outputOne outputTwo controller hfactor hwins

end DetParityAutomaton

end DistributedSynthesis
