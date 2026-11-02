/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropJournalgivesuniform
import DistributedSynthesis.Formalizations.Proposition.PropEpochhierarchical
import DistributedSynthesis.Formalizations.Proposition.PropRegulartestbasistorepair
import DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem
import DistributedSynthesis.Formalizations.Lemma.LemEpochtorotating
import DistributedSynthesis.Formalizations.Theorem.ThmConditionaldec
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteAindex

/-!
# No-direct-reversal fragment certificate

This file packages the no-direct-reversal certificate used by
`prop:nodirectfromjournal`.  The paper's semantic preservation obligations
are represented explicitly as certificate fields.
-/

namespace DistributedSynthesis

universe u v w x y z

/-- A pair of adjacent graph letters is a direct one-way reversal. -/
def IsDirectReversalPair (first second : Graph) : Prop :=
  (first = .left ∧ second = .right) ∨ (first = .right ∧ second = .left)

/-- A graph word has no adjacent direct reversal factors. -/
def NoDirectReversalWord (word : List Graph) : Prop :=
  ∀ leftCtx first second rightCtx,
    word = leftCtx ++ first :: second :: rightCtx ->
      ¬ IsDirectReversalPair first second

/-- In a no-direct-reversal word, adjacent one-way opposite letters cannot occur. -/
theorem noDirectReversalWord_no_left_right_factor
    (word : List Graph)
    (hword : NoDirectReversalWord word)
    (leftCtx rightCtx : List Graph)
    (hfactor : word = leftCtx ++ .left :: .right :: rightCtx) :
    False := by
  exact hword leftCtx .left .right rightCtx hfactor (Or.inl ⟨rfl, rfl⟩)

/-- Symmetric adjacent one-way reversal exclusion. -/
theorem noDirectReversalWord_no_right_left_factor
    (word : List Graph)
    (hword : NoDirectReversalWord word)
    (leftCtx rightCtx : List Graph)
    (hfactor : word = leftCtx ++ .right :: .left :: rightCtx) :
    False := by
  exact hword leftCtx .right .left rightCtx hfactor (Or.inr ⟨rfl, rfl⟩)

/--
The finite epoch transformer induced by a uniform one-directional construction
on the no-direct-reversal fragment.

In this fragment, side changes pass through a `both` boundary.  The close map
therefore uses the side-local one-directional close operation; opposite
one-way closes are harmlessly mapped by the same finite function because they
are unreachable under `NoDirectReversalWord`.
-/
def UniformOneDirectionalFiniteIndexLemma.noDirectEpochTransformer
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂) :
    FiniteEpochTransformer.{u, v, w, x, y, z}
      Alphabet In₁ In₂ Out₁ Out₂ where
  automaton := uniform.automaton
  boundary := uniform.boundary
  boundaryFinite := uniform.boundaryFinite
  within := uniform.summary
  withinFinite := uniform.summaryFinite
  init := fun d boundary => (uniform.sideData d).init boundary
  update := fun d state inputOne inputTwo outputOne outputTwo =>
    (uniform.sideData d).update state inputOne inputTwo outputOne outputTwo
  close := fun d state _graph letter =>
    (uniform.sideData d).close state letter
  continuationInvariant := uniform.continuationInvariant

/-- The no-direct epoch transformer has the expected finite rotating state space. -/
theorem noDirectEpochTransformer_rotating_state_finite
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂) :
    Nonempty
      (Fintype
        (EpochRotatingAccessState
          uniform.boundary
          (uniform.summary Proc.one)
          (uniform.summary Proc.two))) :=
  epoch_transformer_rotating_state_finite
    (uniform.noDirectEpochTransformer)

/-- The boundary letter carried by a recorded round. -/
def roundRecordClosingLetter
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    ClosingLetter In₁ In₂ Out₁ Out₂ where
  inputOne := round.inputOne
  inputTwo := round.inputTwo
  outputOne := round.outputOne
  outputTwo := round.outputTwo

/--
One concrete no-direct epoch-state transition induced by a recorded round.

The outputs are read from the concrete round.  A closing non-dominant graph
applies `close` to the old within-epoch summary, matching the epoch transition
convention used by the finite-game backend.
-/
def UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateTransition
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (state :
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two))
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    EpochRotatingAccessState
      uniform.boundary
      (uniform.summary Proc.one)
      (uniform.summary Proc.two) :=
  match state with
  | Sum.inl boundary =>
      match round.graph with
      | .left =>
          Sum.inr (Sum.inl
            ((uniform.sideData Proc.one).update
              ((uniform.sideData Proc.one).init boundary)
              round.inputOne round.inputTwo round.outputOne round.outputTwo))
      | .right =>
          Sum.inr (Sum.inr
            ((uniform.sideData Proc.two).update
              ((uniform.sideData Proc.two).init boundary)
              round.inputOne round.inputTwo round.outputOne round.outputTwo))
      | .both =>
          Sum.inl ((uniform.sideData Proc.one).close
            ((uniform.sideData Proc.one).init boundary)
            (roundRecordClosingLetter round))
  | Sum.inr (Sum.inl summaryOne) =>
      let summaryOne' :=
        (uniform.sideData Proc.one).update summaryOne
          round.inputOne round.inputTwo round.outputOne round.outputTwo
      match round.graph with
      | .left => Sum.inr (Sum.inl summaryOne')
      | _ => Sum.inl ((uniform.sideData Proc.one).close summaryOne
          (roundRecordClosingLetter round))
  | Sum.inr (Sum.inr summaryTwo) =>
      let summaryTwo' :=
        (uniform.sideData Proc.two).update summaryTwo
          round.inputOne round.inputTwo round.outputOne round.outputTwo
      match round.graph with
      | .right => Sum.inr (Sum.inr summaryTwo')
      | _ => Sum.inl ((uniform.sideData Proc.two).close summaryTwo
          (roundRecordClosingLetter round))

/--
Two round records are equivalent for the raw no-direct epoch transition when
they agree on exactly the fields used by that transition.
-/
def NoDirectEpochRelevantRoundEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (round round' : RoundRecord In₁ In₂ Graph Out₁ Out₂) : Prop :=
  round.graph = round'.graph ∧
    round.inputOne = round'.inputOne ∧
    round.inputTwo = round'.inputTwo ∧
    round.outputOne = round'.outputOne ∧
    round.outputTwo = round'.outputTwo

/--
Two histories have the same no-direct transition-relevant trace when their
graph, input, and output sequences agree componentwise.
-/
def NoDirectEpochRelevantHistoryTracesEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (history history' : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  history.map RoundRecord.graph = history'.map RoundRecord.graph ∧
    history.map RoundRecord.inputOne = history'.map RoundRecord.inputOne ∧
    history.map RoundRecord.inputTwo = history'.map RoundRecord.inputTwo ∧
    history.map RoundRecord.outputOne = history'.map RoundRecord.outputOne ∧
    history.map RoundRecord.outputTwo = history'.map RoundRecord.outputTwo

/--
The same five trace equalities, phrased through the named history sequence API.
-/
def NoDirectEpochRelevantHistoryNamedTracesEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (history history' : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  History.graphSequence history = History.graphSequence history' ∧
    History.inputSequence Proc.one history = History.inputSequence Proc.one history' ∧
    History.inputSequence Proc.two history = History.inputSequence Proc.two history' ∧
    History.outputSequence Proc.one history = History.outputSequence Proc.one history' ∧
    History.outputSequence Proc.two history = History.outputSequence Proc.two history'

/-- Transition-relevant round equality is reflexive. -/
theorem NoDirectEpochRelevantRoundEq.refl
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    NoDirectEpochRelevantRoundEq round round := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Transition-relevant round equality is symmetric. -/
theorem NoDirectEpochRelevantRoundEq.symm
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {round round' : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (hround : NoDirectEpochRelevantRoundEq round round') :
    NoDirectEpochRelevantRoundEq round' round := by
  rcases hround with ⟨hgraph, hinputOne, hinputTwo, houtputOne, houtputTwo⟩
  exact
    ⟨hgraph.symm, hinputOne.symm, hinputTwo.symm, houtputOne.symm,
      houtputTwo.symm⟩

/-- Transition-relevant round equality is transitive. -/
theorem NoDirectEpochRelevantRoundEq.trans
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {round₁ round₂ round₃ : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (hleft : NoDirectEpochRelevantRoundEq round₁ round₂)
    (hright : NoDirectEpochRelevantRoundEq round₂ round₃) :
    NoDirectEpochRelevantRoundEq round₁ round₃ := by
  rcases hleft with ⟨hgraphLeft, hinputOneLeft, hinputTwoLeft,
    houtputOneLeft, houtputTwoLeft⟩
  rcases hright with ⟨hgraphRight, hinputOneRight, hinputTwoRight,
    houtputOneRight, houtputTwoRight⟩
  exact
    ⟨hgraphLeft.trans hgraphRight,
      hinputOneLeft.trans hinputOneRight,
      hinputTwoLeft.trans hinputTwoRight,
      houtputOneLeft.trans houtputOneRight,
      houtputTwoLeft.trans houtputTwoRight⟩

/-- Equality of rounds gives transition-relevant round equality. -/
theorem NoDirectEpochRelevantRoundEq.of_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {round round' : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (hround : round = round') :
    NoDirectEpochRelevantRoundEq round round' := by
  subst round'
  exact NoDirectEpochRelevantRoundEq.refl round

/--
For a fixed strategy, equal next local views force equality of the whole
generated round and hence of all no-direct transition-relevant fields.
-/
theorem NoDirectEpochRelevantRoundEq.nextRound_of_nextView_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    {env env' : EnvironmentRound In₁ In₂}
    (hone :
      nextView Proc.one h env =
        nextView Proc.one h' env')
    (htwo :
      nextView Proc.two h env =
        nextView Proc.two h' env') :
    NoDirectEpochRelevantRoundEq
      (nextRound σ h env) (nextRound σ h' env') :=
  NoDirectEpochRelevantRoundEq.of_eq
    (nextRound_eq_of_nextView_eq σ hone htwo)

/--
Appending strategy-generated rounds preserves transition-relevant history
equality when the prefixes are already equivalent and the next local views
match.
-/
theorem noDirectEpochRelevantHistoryEq_append_nextRound_of_relevantHistoryEq_nextView_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    {env env' : EnvironmentRound In₁ In₂}
    (hhistory : List.Forall₂ NoDirectEpochRelevantRoundEq h h')
    (hone :
      nextView Proc.one h env =
        nextView Proc.one h' env')
    (htwo :
      nextView Proc.two h env =
        nextView Proc.two h' env') :
    List.Forall₂ NoDirectEpochRelevantRoundEq
      (History.append h (nextRound σ h env))
      (History.append h' (nextRound σ h' env')) := by
  unfold History.append
  exact List.rel_append hhistory
    (List.Forall₂.cons
      (NoDirectEpochRelevantRoundEq.nextRound_of_nextView_eq σ hone htwo)
      List.Forall₂.nil)

/--
Current-view form of
`noDirectEpochRelevantHistoryEq_append_nextRound_of_relevantHistoryEq_nextView_eq`.
This is the shape that matches joint-view equality of the one-step-extended
histories.
-/
theorem noDirectEpochRelevantHistoryEq_append_nextRound_of_relevantHistoryEq_currentView_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    {env env' : EnvironmentRound In₁ In₂}
    (hhistory : List.Forall₂ NoDirectEpochRelevantRoundEq h h')
    (hone :
      currentView Proc.one (History.append h (nextRound σ h env)) =
        currentView Proc.one (History.append h' (nextRound σ h' env')))
    (htwo :
      currentView Proc.two (History.append h (nextRound σ h env)) =
        currentView Proc.two (History.append h' (nextRound σ h' env'))) :
    List.Forall₂ NoDirectEpochRelevantRoundEq
      (History.append h (nextRound σ h env))
      (History.append h' (nextRound σ h' env')) := by
  apply noDirectEpochRelevantHistoryEq_append_nextRound_of_relevantHistoryEq_nextView_eq
    σ hhistory
  · simpa [currentView_append_nextRound] using hone
  · simpa [currentView_append_nextRound] using htwo

/--
Generated-prefix induction principle for the no-direct relevant-history
relation.  For a fixed strategy, if the two generated executions have matching
current views at every positive prefix length below `n`, then their length-`n`
prefixes agree on all no-direct transition-relevant fields.
-/
theorem noDirectEpochRelevantHistoryEq_executionPrefix_of_currentView_succ_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env env' : EnvironmentSequence In₁ In₂)
    (n : Nat)
    (hviews :
      ∀ k : Nat, k < n ->
        currentView Proc.one (executionPrefix σ env (k + 1)) =
          currentView Proc.one (executionPrefix σ env' (k + 1)) ∧
        currentView Proc.two (executionPrefix σ env (k + 1)) =
          currentView Proc.two (executionPrefix σ env' (k + 1))) :
    List.Forall₂ NoDirectEpochRelevantRoundEq
      (executionPrefix σ env n) (executionPrefix σ env' n) := by
  induction n with
  | zero =>
      exact List.Forall₂.nil
  | succ n ih =>
      have hprefix :
          List.Forall₂ NoDirectEpochRelevantRoundEq
            (executionPrefix σ env n) (executionPrefix σ env' n) := by
        apply ih
        intro k hk
        exact hviews k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hstep := hviews n (Nat.lt_succ_self n)
      apply
        noDirectEpochRelevantHistoryEq_append_nextRound_of_relevantHistoryEq_currentView_eq
          σ hprefix
      · simpa [executionPrefix_succ] using hstep.1
      · simpa [executionPrefix_succ] using hstep.2

/--
Finite-list generated-prefix induction principle for the no-direct
relevant-history relation.
-/
theorem noDirectEpochRelevantHistoryEq_executionPrefixFromList_of_currentView_snoc_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs envs' : List (EnvironmentRound In₁ In₂))
    (hlength : envs.length = envs'.length)
    (hviews :
      ∀ pref pref' : List (EnvironmentRound In₁ In₂),
        pref.length = pref'.length ->
        pref.length ≤ envs.length ->
        (∃ suff, envs = pref ++ suff) ->
        (∃ suff', envs' = pref' ++ suff') ->
        currentView Proc.one (executionPrefixFromList σ pref) =
          currentView Proc.one (executionPrefixFromList σ pref') ∧
        currentView Proc.two (executionPrefixFromList σ pref) =
          currentView Proc.two (executionPrefixFromList σ pref')) :
    List.Forall₂ NoDirectEpochRelevantRoundEq
      (executionPrefixFromList σ envs)
      (executionPrefixFromList σ envs') := by
  induction envs using List.reverseRecOn generalizing envs' with
  | nil =>
      have hnil : envs' = [] := by
        exact List.eq_nil_of_length_eq_zero hlength.symm
      subst envs'
      exact List.Forall₂.nil
  | append_singleton envs env ih =>
      cases envs' using List.reverseRecOn with
      | nil =>
          have : (envs ++ [env]).length ≠ ([] : List (EnvironmentRound In₁ In₂)).length := by
            simp
          exact False.elim (this hlength)
      | append_singleton envs' env' =>
          have hprefixLength : envs.length = envs'.length := by
            simpa [List.length_append] using hlength
          have hprefix :
              List.Forall₂ NoDirectEpochRelevantRoundEq
                (executionPrefixFromList σ envs)
                (executionPrefixFromList σ envs') := by
            apply ih envs' hprefixLength
            intro pref pref' hprefLength hprefLe hprefSub hprefSub'
            apply hviews pref pref' hprefLength
            · simpa [List.length_append] using Nat.le_succ_of_le hprefLe
            · rcases hprefSub with ⟨suff, hsuff⟩
              exact ⟨suff ++ [env], by rw [hsuff, List.append_assoc]⟩
            · rcases hprefSub' with ⟨suff', hsuff'⟩
              exact ⟨suff' ++ [env'], by rw [hsuff', List.append_assoc]⟩
          have hstepViews :
              currentView Proc.one
                  (History.append (executionPrefixFromList σ envs)
                    (nextRound σ (executionPrefixFromList σ envs) env)) =
                currentView Proc.one
                  (History.append (executionPrefixFromList σ envs')
                    (nextRound σ (executionPrefixFromList σ envs') env')) ∧
              currentView Proc.two
                  (History.append (executionPrefixFromList σ envs)
                    (nextRound σ (executionPrefixFromList σ envs) env)) =
                currentView Proc.two
                  (History.append (executionPrefixFromList σ envs')
                    (nextRound σ (executionPrefixFromList σ envs') env')) := by
            simpa using
              hviews (envs ++ [env]) (envs' ++ [env'])
                (by simpa [List.length_append] using hlength)
                (by simp)
                ⟨[], by simp⟩
                ⟨[], by simp⟩
          simpa using
            noDirectEpochRelevantHistoryEq_append_nextRound_of_relevantHistoryEq_currentView_eq
              σ hprefix hstepViews.1 hstepViews.2

/--
Roundwise transition-relevant history equality determines equality of all
transition-relevant traces.
-/
theorem noDirectEpochRelevantHistoryTracesEq_of_relevantHistoryEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (hhistory : List.Forall₂ NoDirectEpochRelevantRoundEq history history') :
    NoDirectEpochRelevantHistoryTracesEq history history' := by
  induction hhistory with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons hround _ ih =>
      rcases hround with ⟨hgraph, hinputOne, hinputTwo, houtputOne, houtputTwo⟩
      rcases ih with ⟨hgraphs, hinputsOne, hinputsTwo, houtputsOne, houtputsTwo⟩
      exact
        ⟨by simp [hgraph, hgraphs],
          by simp [hinputOne, hinputsOne],
          by simp [hinputTwo, hinputsTwo],
          by simp [houtputOne, houtputsOne],
          by simp [houtputTwo, houtputsTwo]⟩

/--
The generated-prefix induction principle in trace form.
-/
theorem noDirectEpochRelevantHistoryTracesEq_executionPrefix_of_currentView_succ_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env env' : EnvironmentSequence In₁ In₂)
    (n : Nat)
    (hviews :
      ∀ k : Nat, k < n ->
        currentView Proc.one (executionPrefix σ env (k + 1)) =
          currentView Proc.one (executionPrefix σ env' (k + 1)) ∧
        currentView Proc.two (executionPrefix σ env (k + 1)) =
          currentView Proc.two (executionPrefix σ env' (k + 1))) :
    NoDirectEpochRelevantHistoryTracesEq
      (executionPrefix σ env n) (executionPrefix σ env' n) :=
  noDirectEpochRelevantHistoryTracesEq_of_relevantHistoryEq
    (noDirectEpochRelevantHistoryEq_executionPrefix_of_currentView_succ_eq
      σ env env' n hviews)

/--
The finite-list generated-prefix induction principle in trace form.
-/
theorem noDirectEpochRelevantHistoryTracesEq_executionPrefixFromList_of_currentView_snoc_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs envs' : List (EnvironmentRound In₁ In₂))
    (hlength : envs.length = envs'.length)
    (hviews :
      ∀ pref pref' : List (EnvironmentRound In₁ In₂),
        pref.length = pref'.length ->
        pref.length ≤ envs.length ->
        (∃ suff, envs = pref ++ suff) ->
        (∃ suff', envs' = pref' ++ suff') ->
        currentView Proc.one (executionPrefixFromList σ pref) =
          currentView Proc.one (executionPrefixFromList σ pref') ∧
        currentView Proc.two (executionPrefixFromList σ pref) =
          currentView Proc.two (executionPrefixFromList σ pref')) :
    NoDirectEpochRelevantHistoryTracesEq
      (executionPrefixFromList σ envs) (executionPrefixFromList σ envs') :=
  noDirectEpochRelevantHistoryTracesEq_of_relevantHistoryEq
    (noDirectEpochRelevantHistoryEq_executionPrefixFromList_of_currentView_snoc_eq
      σ envs envs' hlength hviews)

/--
Equality of the five transition-relevant traces reconstructs roundwise
transition-relevant history equality.
-/
theorem noDirectEpochRelevantHistoryEq_of_tracesEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (htraces : NoDirectEpochRelevantHistoryTracesEq history history') :
    List.Forall₂ NoDirectEpochRelevantRoundEq history history' := by
  rcases htraces with ⟨hgraphs, hinputsOne, hinputsTwo, houtputsOne, houtputsTwo⟩
  induction history generalizing history' with
  | nil =>
      cases history' with
      | nil => exact List.Forall₂.nil
      | cons round' history' => simp at hgraphs
  | cons round history ih =>
      cases history' with
      | nil => simp at hgraphs
      | cons round' history' =>
          simp at hgraphs hinputsOne hinputsTwo houtputsOne houtputsTwo
          exact
            List.Forall₂.cons
              ⟨hgraphs.1, hinputsOne.1, hinputsTwo.1, houtputsOne.1,
                houtputsTwo.1⟩
              (ih hgraphs.2 hinputsOne.2 hinputsTwo.2 houtputsOne.2
                houtputsTwo.2)

/--
The transition-relevant trace predicate is exactly roundwise
`NoDirectEpochRelevantRoundEq`.
-/
theorem noDirectEpochRelevantHistoryTracesEq_iff_relevantHistoryEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂} :
    NoDirectEpochRelevantHistoryTracesEq history history' ↔
      List.Forall₂ NoDirectEpochRelevantRoundEq history history' := by
  constructor
  · exact noDirectEpochRelevantHistoryEq_of_tracesEq
  · exact noDirectEpochRelevantHistoryTracesEq_of_relevantHistoryEq

/--
Named history trace equality is the same as the raw five-map trace equality.
-/
theorem noDirectEpochRelevantHistoryNamedTracesEq_iff_tracesEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂} :
    NoDirectEpochRelevantHistoryNamedTracesEq history history' ↔
      NoDirectEpochRelevantHistoryTracesEq history history' := by
  simp [NoDirectEpochRelevantHistoryNamedTracesEq,
    NoDirectEpochRelevantHistoryTracesEq, History.graphSequence,
    History.inputSequence, History.outputSequence]

/--
The named history trace predicate is exactly roundwise
`NoDirectEpochRelevantRoundEq`.
-/
theorem noDirectEpochRelevantHistoryNamedTracesEq_iff_relevantHistoryEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂} :
    NoDirectEpochRelevantHistoryNamedTracesEq history history' ↔
      List.Forall₂ NoDirectEpochRelevantRoundEq history history' := by
  rw [noDirectEpochRelevantHistoryNamedTracesEq_iff_tracesEq,
    noDirectEpochRelevantHistoryTracesEq_iff_relevantHistoryEq]

/--
Named history trace equality gives the raw five-map trace equality.
-/
theorem noDirectEpochRelevantHistoryTracesEq_of_namedTracesEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (htraces : NoDirectEpochRelevantHistoryNamedTracesEq history history') :
    NoDirectEpochRelevantHistoryTracesEq history history' :=
  (noDirectEpochRelevantHistoryNamedTracesEq_iff_tracesEq.mp htraces)

/--
Raw five-map trace equality gives named history trace equality.
-/
theorem noDirectEpochRelevantHistoryNamedTracesEq_of_tracesEq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (htraces : NoDirectEpochRelevantHistoryTracesEq history history') :
    NoDirectEpochRelevantHistoryNamedTracesEq history history' :=
  (noDirectEpochRelevantHistoryNamedTracesEq_iff_tracesEq.mpr htraces)

/--
The generated-prefix induction principle in named-trace form.
-/
theorem noDirectEpochRelevantHistoryNamedTracesEq_executionPrefix_of_currentView_succ_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env env' : EnvironmentSequence In₁ In₂)
    (n : Nat)
    (hviews :
      ∀ k : Nat, k < n ->
        currentView Proc.one (executionPrefix σ env (k + 1)) =
          currentView Proc.one (executionPrefix σ env' (k + 1)) ∧
        currentView Proc.two (executionPrefix σ env (k + 1)) =
          currentView Proc.two (executionPrefix σ env' (k + 1))) :
    NoDirectEpochRelevantHistoryNamedTracesEq
      (executionPrefix σ env n) (executionPrefix σ env' n) :=
  noDirectEpochRelevantHistoryNamedTracesEq_of_tracesEq
    (noDirectEpochRelevantHistoryTracesEq_executionPrefix_of_currentView_succ_eq
      σ env env' n hviews)

/--
The finite-list generated-prefix induction principle in named-trace form.
-/
theorem noDirectEpochRelevantHistoryNamedTracesEq_executionPrefixFromList_of_currentView_snoc_eq
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (envs envs' : List (EnvironmentRound In₁ In₂))
    (hlength : envs.length = envs'.length)
    (hviews :
      ∀ pref pref' : List (EnvironmentRound In₁ In₂),
        pref.length = pref'.length ->
        pref.length ≤ envs.length ->
        (∃ suff, envs = pref ++ suff) ->
        (∃ suff', envs' = pref' ++ suff') ->
        currentView Proc.one (executionPrefixFromList σ pref) =
          currentView Proc.one (executionPrefixFromList σ pref') ∧
        currentView Proc.two (executionPrefixFromList σ pref) =
          currentView Proc.two (executionPrefixFromList σ pref')) :
    NoDirectEpochRelevantHistoryNamedTracesEq
      (executionPrefixFromList σ envs) (executionPrefixFromList σ envs') :=
  noDirectEpochRelevantHistoryNamedTracesEq_of_tracesEq
    (noDirectEpochRelevantHistoryTracesEq_executionPrefixFromList_of_currentView_snoc_eq
      σ envs envs' hlength hviews)

/--
The raw no-direct epoch transition depends only on the graph/input/output
fields named by `NoDirectEpochRelevantRoundEq`.
-/
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateTransition_eq_of_relevantRoundEq
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (state :
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two))
    {round round' : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (hround : NoDirectEpochRelevantRoundEq round round') :
    uniform.noDirectEpochStateTransition state round =
      uniform.noDirectEpochStateTransition state round' := by
  rcases hround with ⟨hgraph, hinputOne, hinputTwo, houtputOne, houtputTwo⟩
  cases state with
  | inl boundary =>
      cases round
      cases round'
      simp [NoDirectEpochRelevantRoundEq] at hgraph hinputOne hinputTwo houtputOne houtputTwo
      subst hgraph
      subst hinputOne
      subst hinputTwo
      subst houtputOne
      subst houtputTwo
      simp [UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateTransition,
        roundRecordClosingLetter]
  | inr side =>
      cases side with
      | inl summaryOne =>
          cases round
          cases round'
          simp [NoDirectEpochRelevantRoundEq] at hgraph hinputOne hinputTwo houtputOne houtputTwo
          subst hgraph
          subst hinputOne
          subst hinputTwo
          subst houtputOne
          subst houtputTwo
          simp [UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateTransition,
            roundRecordClosingLetter]
      | inr summaryTwo =>
          cases round
          cases round'
          simp [NoDirectEpochRelevantRoundEq] at hgraph hinputOne hinputTwo houtputOne houtputTwo
          subst hgraph
          subst hinputOne
          subst hinputTwo
          subst houtputOne
          subst houtputTwo
          simp [UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateTransition,
            roundRecordClosingLetter]

/-- Run the no-direct epoch-state transition from an arbitrary state. -/
def UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂) :
    EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two) ->
      History In₁ In₂ Graph Out₁ Out₂ ->
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two)
  | state, [] => state
  | state, round :: history =>
      uniform.noDirectEpochStateAfterHistoryFrom
        (uniform.noDirectEpochStateTransition state round)
        history

/-- The no-direct rotating access state reached after a concrete history. -/
def UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    EpochRotatingAccessState
      uniform.boundary
      (uniform.summary Proc.one)
      (uniform.summary Proc.two) :=
  uniform.noDirectEpochStateAfterHistoryFrom (Sum.inl initialBoundary) history

@[simp]
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom_nil
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (state :
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two)) :
    uniform.noDirectEpochStateAfterHistoryFrom state
        ([] : History In₁ In₂ Graph Out₁ Out₂) =
      state := rfl

@[simp]
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom_cons
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (state :
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two))
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    uniform.noDirectEpochStateAfterHistoryFrom state (round :: history) =
    uniform.noDirectEpochStateAfterHistoryFrom
        (uniform.noDirectEpochStateTransition state round)
        history := rfl

/--
The raw no-direct epoch state after a history depends only on the
transition-relevant fields of each round.
-/
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom_eq_of_relevantHistoryEq
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (state :
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two))
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (hhistory : List.Forall₂ NoDirectEpochRelevantRoundEq history history') :
    uniform.noDirectEpochStateAfterHistoryFrom state history =
      uniform.noDirectEpochStateAfterHistoryFrom state history' := by
  induction hhistory generalizing state with
  | nil => rfl
  | cons hround htail ih =>
      simp [UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom_cons,
        uniform.noDirectEpochStateTransition_eq_of_relevantRoundEq state hround,
        ih]

/--
Initial-boundary form of
`noDirectEpochStateAfterHistoryFrom_eq_of_relevantHistoryEq`.
-/
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory_eq_of_relevantHistoryEq
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (hhistory : List.Forall₂ NoDirectEpochRelevantRoundEq history history') :
    uniform.noDirectEpochStateAfterHistory initialBoundary history =
      uniform.noDirectEpochStateAfterHistory initialBoundary history' :=
  uniform.noDirectEpochStateAfterHistoryFrom_eq_of_relevantHistoryEq
    (Sum.inl initialBoundary) hhistory

/-- Transition-relevant history equality is reflexive. -/
theorem noDirectEpochRelevantHistoryEq_refl
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    List.Forall₂ NoDirectEpochRelevantRoundEq history history := by
  induction history with
  | nil => exact List.Forall₂.nil
  | cons round history ih =>
      exact List.Forall₂.cons (NoDirectEpochRelevantRoundEq.refl round) ih

/-- Transition-relevant history equality is symmetric. -/
theorem noDirectEpochRelevantHistoryEq_symm
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (hhistory : List.Forall₂ NoDirectEpochRelevantRoundEq history history') :
    List.Forall₂ NoDirectEpochRelevantRoundEq history' history := by
  induction hhistory with
  | nil => exact List.Forall₂.nil
  | cons hround _ ih =>
      exact List.Forall₂.cons (NoDirectEpochRelevantRoundEq.symm hround) ih

/-- Transition-relevant history equality is transitive. -/
theorem noDirectEpochRelevantHistoryEq_trans
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {history₁ history₂ history₃ : History In₁ In₂ Graph Out₁ Out₂}
    (hleft : List.Forall₂ NoDirectEpochRelevantRoundEq history₁ history₂)
    (hright : List.Forall₂ NoDirectEpochRelevantRoundEq history₂ history₃) :
    List.Forall₂ NoDirectEpochRelevantRoundEq history₁ history₃ := by
  induction hleft generalizing history₃ with
  | nil =>
      cases hright
      exact List.Forall₂.nil
  | cons hroundLeft htailLeft ih =>
      cases hright with
      | cons hroundRight htailRight =>
          exact
            List.Forall₂.cons
              (NoDirectEpochRelevantRoundEq.trans hroundLeft hroundRight)
              (ih htailRight)

@[simp]
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory_nil
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary) :
    uniform.noDirectEpochStateAfterHistory initialBoundary
        ([] : History In₁ In₂ Graph Out₁ Out₂) =
      Sum.inl initialBoundary := rfl

/-- Running a concatenated concrete history is prefix-then-suffix execution. -/
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom_append
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (state :
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two))
    (pref suff : History In₁ In₂ Graph Out₁ Out₂) :
    uniform.noDirectEpochStateAfterHistoryFrom state (pref ++ suff) =
      uniform.noDirectEpochStateAfterHistoryFrom
        (uniform.noDirectEpochStateAfterHistoryFrom state pref)
        suff := by
  induction pref generalizing state with
  | nil => rfl
  | cons round pref ih =>
      simp [noDirectEpochStateAfterHistoryFrom_cons, ih]

/-- Initial-boundary form of the no-direct history append lemma. -/
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory_append
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (pref suff : History In₁ In₂ Graph Out₁ Out₂) :
    uniform.noDirectEpochStateAfterHistory initialBoundary (pref ++ suff) =
      uniform.noDirectEpochStateAfterHistoryFrom
        (uniform.noDirectEpochStateAfterHistory initialBoundary pref)
        suff := by
  exact
    uniform.noDirectEpochStateAfterHistoryFrom_append
      (Sum.inl initialBoundary) pref suff

@[simp]
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom_singleton
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (state :
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two))
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    uniform.noDirectEpochStateAfterHistoryFrom state [round] =
      uniform.noDirectEpochStateTransition state round := rfl

/-- Appending one concrete round applies exactly one no-direct epoch transition. -/
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory_append_round
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (history : History In₁ In₂ Graph Out₁ Out₂)
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    uniform.noDirectEpochStateAfterHistory initialBoundary (History.append history round) =
      uniform.noDirectEpochStateTransition
        (uniform.noDirectEpochStateAfterHistory initialBoundary history)
        round := by
  rw [History.append]
  rw [uniform.noDirectEpochStateAfterHistory_append]
  simp

/--
The concrete no-direct epoch state stream along the execution generated by a
strategy/environment pair.
-/
def UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateStream
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    Nat ->
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two) :=
  fun n => uniform.noDirectEpochStateAfterHistory initialBoundary (executionPrefix σ env n)

@[simp]
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateStream_zero
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    uniform.noDirectEpochStateStream initialBoundary σ env 0 =
      Sum.inl initialBoundary := by
  simp [UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateStream]

/--
Successor recurrence for the concrete no-direct epoch state stream.  This is
the induction equation used by the later `\lambda`/hidden-bit replay argument.
-/
theorem UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateStream_succ
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (n : Nat) :
    uniform.noDirectEpochStateStream initialBoundary σ env (n + 1) =
      uniform.noDirectEpochStateTransition
        (uniform.noDirectEpochStateStream initialBoundary σ env n)
        (nextRound σ (executionPrefix σ env n) (env n)) := by
  simp [
    noDirectEpochStateStream,
    executionPrefix_succ,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory_append_round
  ]

/--
The smallest right-only environment used below to sanity-check full-view
decoder targets.
-/
def unitRightEnvironment : EnvironmentSequence Unit Unit :=
  fun _ => { inputOne := (), inputTwo := (), graph := .right }

/-- The unique unit-output strategy. -/
def unitStrategy : StrategyPair Unit Unit Unit Unit where
  one := fun _ => ()
  two := fun _ => ()

/-- The degenerate unit one-directional summary package. -/
def unitUniformOneDirectional :
    UniformOneDirectionalFiniteIndexLemma
      (RoundRecord Unit Unit Graph Unit Unit) Unit Unit Unit Unit where
  automaton := {
    State := Unit
    stateFinite := inferInstance
    initial := ()
    step := fun _ _ => ()
    priority := fun _ => 0
  }
  boundary := Unit
  boundaryFinite := inferInstance
  summary := fun _ => Unit
  summaryFinite := fun _ => inferInstance
  sideData := fun _ => {
    init := fun _ => ()
    update := fun _ _ _ _ _ => ()
    close := fun _ _ => ()
  }
  continuationInvariant := True
  regularRepresentation := True

theorem unitRight_nextView_one_deepens :
    nextView Proc.one
        (executionPrefix unitStrategy unitRightEnvironment 1)
        (unitRightEnvironment 1) ≠
      nextView Proc.one
        (executionPrefix unitStrategy unitRightEnvironment 2)
        (unitRightEnvironment 2) := by
  intro h
  simp [unitStrategy, unitRightEnvironment, nextView, advanceViewsWithEnvironment,
    executionPrefix_succ, nextRound, History.append, viewPair,
    advanceViews] at h

theorem unitUniform_noDirect_stateStream_right_one_eq_two :
    unitUniformOneDirectional.noDirectEpochStateStream
        () unitStrategy unitRightEnvironment 1 =
      unitUniformOneDirectional.noDirectEpochStateStream
        () unitStrategy unitRightEnvironment 2 := by
  simp [unitUniformOneDirectional, unitRightEnvironment, unitStrategy,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateStream,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateTransition,
    executionPrefix_succ, nextRound, History.append]

/-- The one-round bidirectional unit history used to test receipt preservation. -/
def unitBothRound : RoundRecord Unit Unit Graph Unit Unit where
  inputOne := ()
  inputTwo := ()
  graph := .both
  outputOne := ()
  outputTwo := ()

/--
The raw no-direct access state does not record a bidirectional boundary receipt:
in the degenerate uniform construction, the empty history and the one-`both`
history have the same no-direct state.
-/
theorem unitUniform_noDirect_state_empty_eq_both :
    unitUniformOneDirectional.noDirectEpochStateAfterHistory
        () ([] : History Unit Unit Graph Unit Unit) =
      unitUniformOneDirectional.noDirectEpochStateAfterHistory
        () [unitBothRound] := by
  simp [unitUniformOneDirectional, unitBothRound,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistory,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateAfterHistoryFrom,
    UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateTransition]

/--
But the current process-1 receipt tag differs between those two histories.  Thus
even coherent receipt tags are not determined by the raw no-direct state alone.
-/
theorem unit_currentReceipt_one_empty_ne_both :
    (currentView Proc.one ([] : History Unit Unit Graph Unit Unit)).receiptTag ≠
      (currentView Proc.one [unitBothRound]).receiptTag := by
  simp [unitBothRound, currentView, viewPair, advanceViews, View.receiptTag]

/--
Sanity check for the current full-view decoder target.

Even in the degenerate finite no-direct transformer, the right-only stream has
the same finite no-direct state before rounds `1` and `2`, and the same current
environment round, but process `1`'s full local view is strictly deeper.  Thus
full-view decoding from only `(finite state, current environment round)` is not
a consequence of the no-direct state map itself; the final proof must use a
finite `\lambda`/local-observation interface rather than trying to recover full
recursive views from the finite state alone.
-/
theorem not_unitUniform_noDirect_fullViewDecoder :
    ¬ ∃ viewOne :
          EpochRotatingAccessState
              unitUniformOneDirectional.boundary
              (unitUniformOneDirectional.summary Proc.one)
              (unitUniformOneDirectional.summary Proc.two) ->
            EnvironmentRound Unit Unit -> View Unit Unit Proc.one,
        ∀ n : Nat,
          viewOne
              (unitUniformOneDirectional.noDirectEpochStateStream
                () unitStrategy unitRightEnvironment n)
              (unitRightEnvironment n) =
            nextView Proc.one
              (executionPrefix unitStrategy unitRightEnvironment n)
              (unitRightEnvironment n) := by
  rintro ⟨viewOne, hview⟩
  have hstate := unitUniform_noDirect_stateStream_right_one_eq_two
  have henv : unitRightEnvironment 1 = unitRightEnvironment 2 := rfl
  have hsame :
      nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 1)
          (unitRightEnvironment 1) =
        nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 2)
          (unitRightEnvironment 2) := by
    rw [← hview 1, ← hview 2, hstate, henv]
  exact unitRight_nextView_one_deepens hsame

/--
The same obstruction already applies to the exact current
non-fringe/receipt-tag split.

Thus the final lambda-local proof cannot ask the no-direct state, together
with the current environment round, to decode the actual current non-fringe
view and receipt tag.  The lambda carrier has to be a genuine finite local
summary interface, not the raw recursive view split into two fields.
-/
theorem not_unitUniform_noDirect_currentNonFringeReceiptDecoder :
    ¬ ∃ historyOne :
          EpochRotatingAccessState
              unitUniformOneDirectional.boundary
              (unitUniformOneDirectional.summary Proc.one)
              (unitUniformOneDirectional.summary Proc.two) ->
            EnvironmentRound Unit Unit -> List (NonFringeView Unit Unit Proc.one),
        ∃ fringeOne :
          EpochRotatingAccessState
              unitUniformOneDirectional.boundary
              (unitUniformOneDirectional.summary Proc.one)
              (unitUniformOneDirectional.summary Proc.two) ->
            EnvironmentRound Unit Unit -> ReceiptTag,
          ∀ n : Nat,
            historyOne
                (unitUniformOneDirectional.noDirectEpochStateStream
                  () unitStrategy unitRightEnvironment n)
                (unitRightEnvironment n) =
              [(nextView Proc.one
                (executionPrefix unitStrategy unitRightEnvironment n)
                (unitRightEnvironment n)).nonFringe] ∧
            fringeOne
                (unitUniformOneDirectional.noDirectEpochStateStream
                  () unitStrategy unitRightEnvironment n)
                (unitRightEnvironment n) =
              (nextView Proc.one
                (executionPrefix unitStrategy unitRightEnvironment n)
                (unitRightEnvironment n)).receiptTag := by
  rintro ⟨historyOne, fringeOne, htrack⟩
  have hstate := unitUniform_noDirect_stateStream_right_one_eq_two
  have henv : unitRightEnvironment 1 = unitRightEnvironment 2 := rfl
  rcases htrack 1 with ⟨hhistoryOne, hfringeOne⟩
  rcases htrack 2 with ⟨hhistoryTwo, hfringeTwo⟩
  have hnonFringe :
      (nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 1)
          (unitRightEnvironment 1)).nonFringe =
        (nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 2)
          (unitRightEnvironment 2)).nonFringe := by
    have hlist :
        [(nextView Proc.one
            (executionPrefix unitStrategy unitRightEnvironment 1)
            (unitRightEnvironment 1)).nonFringe] =
          [(nextView Proc.one
            (executionPrefix unitStrategy unitRightEnvironment 2)
            (unitRightEnvironment 2)).nonFringe] := by
      calc
        [(nextView Proc.one
            (executionPrefix unitStrategy unitRightEnvironment 1)
            (unitRightEnvironment 1)).nonFringe]
            = historyOne
                (unitUniformOneDirectional.noDirectEpochStateStream
                  () unitStrategy unitRightEnvironment 1)
                (unitRightEnvironment 1) := hhistoryOne.symm
        _ = historyOne
                (unitUniformOneDirectional.noDirectEpochStateStream
                  () unitStrategy unitRightEnvironment 2)
                (unitRightEnvironment 2) := by rw [hstate, henv]
        _ = [(nextView Proc.one
            (executionPrefix unitStrategy unitRightEnvironment 2)
            (unitRightEnvironment 2)).nonFringe] := hhistoryTwo
    simpa using hlist
  have hreceipt :
      (nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 1)
          (unitRightEnvironment 1)).receiptTag =
        (nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 2)
          (unitRightEnvironment 2)).receiptTag := by
    calc
      (nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 1)
          (unitRightEnvironment 1)).receiptTag
          = fringeOne
              (unitUniformOneDirectional.noDirectEpochStateStream
                () unitStrategy unitRightEnvironment 1)
              (unitRightEnvironment 1) := hfringeOne.symm
      _ = fringeOne
              (unitUniformOneDirectional.noDirectEpochStateStream
                () unitStrategy unitRightEnvironment 2)
              (unitRightEnvironment 2) := by rw [hstate, henv]
      _ = (nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 2)
          (unitRightEnvironment 2)).receiptTag := hfringeTwo
  have hsame :
      nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 1)
          (unitRightEnvironment 1) =
        nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 2)
          (unitRightEnvironment 2) := by
    calc
      nextView Proc.one
          (executionPrefix unitStrategy unitRightEnvironment 1)
          (unitRightEnvironment 1) =
          ((nextView Proc.one
            (executionPrefix unitStrategy unitRightEnvironment 1)
            (unitRightEnvironment 1)).nonFringe.withReceiptTag
              (nextView Proc.one
                (executionPrefix unitStrategy unitRightEnvironment 1)
                (unitRightEnvironment 1)).receiptTag) := by
            exact (View.withReceiptTag_nonFringe_receiptTag
              (nextView Proc.one
                (executionPrefix unitStrategy unitRightEnvironment 1)
                (unitRightEnvironment 1))).symm
      _ =
          ((nextView Proc.one
            (executionPrefix unitStrategy unitRightEnvironment 2)
            (unitRightEnvironment 2)).nonFringe.withReceiptTag
              (nextView Proc.one
                (executionPrefix unitStrategy unitRightEnvironment 2)
                (unitRightEnvironment 2)).receiptTag) := by
            rw [hnonFringe, hreceipt]
      _ =
          nextView Proc.one
            (executionPrefix unitStrategy unitRightEnvironment 2)
            (unitRightEnvironment 2) := by
            exact View.withReceiptTag_nonFringe_receiptTag
              (nextView Proc.one
                (executionPrefix unitStrategy unitRightEnvironment 2)
                (unitRightEnvironment 2))
  exact unitRight_nextView_one_deepens hsame

/--
Disjoint-union case split for the no-direct rotating access state.

This is the finite part of the paper proof of Lemma `lem:epochtorotating`:
after the concrete history map has landed in `M_A ⊎ P₁ ⊎ P₂`, equality of
access states can be discharged by the boundary congruence, the process-1
within-epoch congruence, or the process-2 within-epoch congruence.
-/
theorem noDirectHistoryAccessState_refines_AContinuation_of_components
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    ∀ c c',
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c c' := by
  intro c c' hsame
  cases hstate :
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history with
  | inl boundary =>
      have hstate' :
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
            Sum.inl boundary := by
        rw [← hsame, hstate]
      exact boundaryRefines c c' boundary hstate hstate'
  | inr side =>
      cases side with
      | inl summary =>
          have hstate' :
              uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
                Sum.inr (Sum.inl summary) := by
            rw [← hsame, hstate]
          exact sideOneRefines c c' summary hstate hstate'
        | inr summary =>
            have hstate' :
                uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
                  Sum.inr (Sum.inr summary) := by
              rw [← hsame, hstate]
            exact sideTwoRefines c c' summary hstate hstate'

/--
The semantic component-congruence package for the concrete no-direct
history-access-state map.

This is the finite-retraction hinge left by the paper argument: each component of
`M_A ⊎ P₁ ⊎ P₂` must refine `A`-continuation equivalence.  Once these three
component facts are supplied, the generic case split above turns equality of the
no-direct rotating access state into the full continuation equivalence needed by
the finite-index route.
-/
structure NoDirectHistoryAccessStateComponentRefinement
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder) where
  boundaryRefines :
    ∀ c c' boundary,
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
        Sum.inl boundary ->
      uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
        Sum.inl boundary ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c c'
  sideOneRefines :
    ∀ c c' summary,
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
        Sum.inr (Sum.inl summary) ->
      uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
        Sum.inr (Sum.inl summary) ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c c'
  sideTwoRefines :
    ∀ c c' summary,
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
        Sum.inr (Sum.inr summary) ->
      uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
        Sum.inr (Sum.inr summary) ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c c'

/--
The component-refinement package implies full refinement of equal no-direct
history-access states.
-/
theorem NoDirectHistoryAccessStateComponentRefinement.refinesAContinuation
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂}
    {initialBoundary : uniform.boundary}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    (refinement :
      NoDirectHistoryAccessStateComponentRefinement
        uniform initialBoundary sameParityOutcomes containmentOrder) :
    ∀ c c',
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c c' :=
  noDirectHistoryAccessState_refines_AContinuation_of_components
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    refinement.boundaryRefines
    refinement.sideOneRefines
    refinement.sideTwoRefines

/--
Build the component-refinement package from the single semantic theorem that
equality of the concrete no-direct access state refines `A`-continuation
equivalence.

This is the preferred statement shape for the remaining finite-retraction proof:
prove one equality-of-`μ` theorem, then package it for the component-based
finite-index route.
-/
def NoDirectHistoryAccessStateComponentRefinement.ofRefinesAContinuation
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂}
    {initialBoundary : uniform.boundary}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    (refinesAContinuation :
      ∀ c c',
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    NoDirectHistoryAccessStateComponentRefinement
      uniform initialBoundary sameParityOutcomes containmentOrder where
  boundaryRefines := by
    intro c c' boundary hstate hstate'
    exact refinesAContinuation c c' (by rw [hstate, hstate'])
  sideOneRefines := by
    intro c c' summary hstate hstate'
    exact refinesAContinuation c c' (by rw [hstate, hstate'])
  sideTwoRefines := by
    intro c c' summary hstate hstate'
    exact refinesAContinuation c c' (by rw [hstate, hstate'])

/--
Sanity check: the unrestricted no-direct equality-refinement theorem cannot hold
for arbitrary `ContinuationConfiguration`s.

The current `ContinuationConfiguration` record stores `receiptOne` and
`receiptTwo` as free fields, not as values computed from `history`.  Hence two
configurations with the same history have the same no-direct access state but
may carry different receipt tags.  Any theorem intended to close the concrete
finite retraction must therefore either restrict to coherent configurations or
make the quotient/refinement relation include the receipt fields.
-/
theorem not_noDirectAccessState_refines_AContinuation_unrestricted
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    [Inhabited AState]
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder) :
    ¬ (∀ c c',
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') := by
  intro hrefines
  let c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState := {
    history := []
    automatonState := default
    receiptOne := .recv
    receiptTwo := .noRecv
  }
  let c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState := {
    history := []
    automatonState := default
    receiptOne := .noRecv
    receiptTwo := .noRecv
  }
  have hsame :
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history := rfl
  rcases hrefines c c' hsame with
    ⟨_hautomaton, hreceiptOne, _hreceiptTwo, _horder, _hparity⟩
  cases hreceiptOne

/--
Consequently, the currently packaged component-refinement certificate is also
not constructible for arbitrary, incoherent configurations.
-/
theorem not_noDirectHistoryAccessStateComponentRefinement_unrestricted
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    [Inhabited AState]
    {uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂}
    {initialBoundary : uniform.boundary}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder} :
    ¬ NoDirectHistoryAccessStateComponentRefinement
        uniform initialBoundary sameParityOutcomes containmentOrder := by
  intro refinement
  exact
    not_noDirectAccessState_refines_AContinuation_unrestricted
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      refinement.refinesAContinuation

/--
The no-direct access state enriched with the current receipt/order payload.

The counterexamples above show that the raw `M_A ⊎ P₁ ⊎ P₂` state cannot be
the final quotient by itself: even coherent current receipt tags are not
determined by it.  This enriched state is the corrected finite-retraction
component for the receipt/order part of `A`-continuation equivalence.
-/
def UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateWithReceiptOrder
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two) ×
      ReceiptOrderData :=
  (uniform.noDirectEpochStateAfterHistory initialBoundary history,
    currentReceiptOrderData history (orderOfHistory history))

/--
Equality of the enriched no-direct state determines the concrete current
receipt tags and containment order of the two histories.
-/
theorem noDirectEpochStateWithReceiptOrder_determines_historyReceiptOrder
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (hsame :
      uniform.noDirectEpochStateWithReceiptOrder initialBoundary orderOfHistory history =
        uniform.noDirectEpochStateWithReceiptOrder initialBoundary orderOfHistory history') :
    (currentView Proc.one history).receiptTag =
        (currentView Proc.one history').receiptTag ∧
      (currentView Proc.two history).receiptTag =
        (currentView Proc.two history').receiptTag ∧
      orderOfHistory history = orderOfHistory history' := by
  have hdata :
      currentReceiptOrderData history (orderOfHistory history) =
        currentReceiptOrderData history' (orderOfHistory history') := by
    exact congrArg Prod.snd hsame
  have hone := congrArg ReceiptOrderData.receiptOne hdata
  have htwo := congrArg ReceiptOrderData.receiptTwo hdata
  have horder := congrArg ReceiptOrderData.containmentOrder hdata
  exact
    ⟨by simpa [currentReceiptOrderData] using hone,
      by simpa [currentReceiptOrderData] using htwo,
      by simpa [currentReceiptOrderData] using horder⟩

/--
Coherence of a continuation configuration with the concrete history-derived
receipt tags and a chosen history-derived containment order.
-/
def ContinuationConfigurationReceiptOrderCoherent
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState) : Prop :=
  c.receiptOne = (currentView Proc.one c.history).receiptTag ∧
    c.receiptTwo = (currentView Proc.two c.history).receiptTag ∧
    containmentOrder c = orderOfHistory c.history

/--
For coherent configurations, equality of the enriched no-direct state determines
the receipt/order fields required by `AContinuationEquivalent`.
-/
theorem noDirectEpochStateWithReceiptOrder_determines_configReceiptOrder_of_coherent
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    (hcoh :
      ContinuationConfigurationReceiptOrderCoherent
        containmentOrder orderOfHistory c)
    (hcoh' :
      ContinuationConfigurationReceiptOrderCoherent
        containmentOrder orderOfHistory c')
    (hsame :
      uniform.noDirectEpochStateWithReceiptOrder
          initialBoundary orderOfHistory c.history =
        uniform.noDirectEpochStateWithReceiptOrder
          initialBoundary orderOfHistory c'.history) :
    c.receiptOne = c'.receiptOne ∧
      c.receiptTwo = c'.receiptTwo ∧
      containmentOrder c = containmentOrder c' := by
  rcases hcoh with ⟨hone, htwo, horder⟩
  rcases hcoh' with ⟨hone', htwo', horder'⟩
  rcases
    noDirectEpochStateWithReceiptOrder_determines_historyReceiptOrder
      uniform initialBoundary orderOfHistory hsame with
    ⟨hhistOne, hhistTwo, hhistOrder⟩
  exact
    ⟨by rw [hone, hone', hhistOne],
      by rw [htwo, htwo', hhistTwo],
      by rw [horder, horder', hhistOrder]⟩

/--
Concrete-summary version of the enriched no-direct receipt/order recovery.

If the concrete finite summary decoder agrees with the canonical current
receipt/order component on every nonempty prefix, equality of the concrete
summary states determines the same current receipt tags and final-graph
containment order as equality of
`noDirectEpochStateWithReceiptOrder`.  This is the bridge from the abstract
summary plan in `PropEpochhierarchical` to the no-direct enriched state.
-/
theorem noDirectSummaryState_determines_historyReceiptOrder_of_decodesCurrent
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOrder : Summary₁ × Summary₂ -> ReceiptOrderData)
    (decodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          decodeReceiptOrder (summaryOfHistory (History.append pref r)) =
            currentReceiptOrderDataForAppend pref r)
    {pref pref' : History In₁ In₂ Graph Out₁ Out₂}
    {r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (hsame :
      summaryOfHistory (History.append pref r) =
        summaryOfHistory (History.append pref' r')) :
    (currentView Proc.one (History.append pref r)).receiptTag =
        (currentView Proc.one (History.append pref' r')).receiptTag ∧
      (currentView Proc.two (History.append pref r)).receiptTag =
        (currentView Proc.two (History.append pref' r')).receiptTag ∧
      graphContainmentOrder r.graph = graphContainmentOrder r'.graph := by
  have hdata :
      currentReceiptOrderDataForAppend pref r =
        currentReceiptOrderDataForAppend pref' r' := by
    calc
      currentReceiptOrderDataForAppend pref r =
          decodeReceiptOrder (summaryOfHistory (History.append pref r)) := by
            exact (decodesCurrent pref r).symm
      _ = decodeReceiptOrder (summaryOfHistory (History.append pref' r')) := by
            rw [hsame]
      _ = currentReceiptOrderDataForAppend pref' r' := by
            exact decodesCurrent pref' r'
  have hone := congrArg ReceiptOrderData.receiptOne hdata
  have htwo := congrArg ReceiptOrderData.receiptTwo hdata
  have horder := congrArg ReceiptOrderData.containmentOrder hdata
  exact
    ⟨by simpa [currentReceiptOrderDataForAppend, currentReceiptOrderData] using hone,
      by simpa [currentReceiptOrderDataForAppend, currentReceiptOrderData] using htwo,
      by simpa [currentReceiptOrderDataForAppend, currentReceiptOrderData] using horder⟩

/--
Coherent-configuration form of
`noDirectSummaryState_determines_historyReceiptOrder_of_decodesCurrent`.
Use this when the concrete summary state is attached to continuation
configurations whose receipt/order fields are known to be history-derived.
-/
theorem noDirectSummaryState_determines_configReceiptOrder_of_decodesCurrent_coherent
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type c}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOrder : Summary₁ × Summary₂ -> ReceiptOrderData)
    (decodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          decodeReceiptOrder (summaryOfHistory (History.append pref r)) =
            currentReceiptOrderDataForAppend pref r)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (orderOfAppend :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          orderOfHistory (History.append pref r) = graphContainmentOrder r.graph)
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    {pref pref' : History In₁ In₂ Graph Out₁ Out₂}
    {r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (hc : c.history = History.append pref r)
    (hc' : c'.history = History.append pref' r')
    (hcoh :
      ContinuationConfigurationReceiptOrderCoherent
        containmentOrder orderOfHistory c)
    (hcoh' :
      ContinuationConfigurationReceiptOrderCoherent
        containmentOrder orderOfHistory c')
    (hsame :
      summaryOfHistory c.history = summaryOfHistory c'.history) :
    c.receiptOne = c'.receiptOne ∧
      c.receiptTwo = c'.receiptTwo ∧
      containmentOrder c = containmentOrder c' := by
  rcases hcoh with ⟨hone, htwo, horder⟩
  rcases hcoh' with ⟨hone', htwo', horder'⟩
  have hsameAppend :
      summaryOfHistory (History.append pref r) =
        summaryOfHistory (History.append pref' r') := by
    simpa [hc, hc'] using hsame
  rcases
    noDirectSummaryState_determines_historyReceiptOrder_of_decodesCurrent
      summaryOfHistory decodeReceiptOrder decodesCurrent hsameAppend with
    ⟨hhistOne, hhistTwo, hhistOrder⟩
  exact
    ⟨by rw [hone, hone', hc, hc', hhistOne],
      by rw [htwo, htwo', hc, hc', hhistTwo],
      by
        rw [horder, horder', hc, hc', orderOfAppend pref r,
          orderOfAppend pref' r', hhistOrder]⟩

/--
The no-direct access state enriched with every non-parity field of
`A`-continuation equivalence, plus a finite parity-progress payload.

This is the corrected finite-retraction shape after the raw-state
counterexamples: the raw `M_A ⊎ P₁ ⊎ P₂` state is kept, but current
receipt/order data and the current automaton profile are explicit state
components.  The remaining semantic input is that equality of the chosen
`ParityProgress` payload implies `sameParityOutcomes`.
-/
def UniformOneDirectionalFiniteIndexLemma.noDirectEpochStateWithAContinuationData
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (history : History In₁ In₂ Graph Out₁ Out₂) :
    ((EpochRotatingAccessState
          uniform.boundary
          (uniform.summary Proc.one)
          (uniform.summary Proc.two) ×
        ReceiptOrderData) ×
      AState) ×
      ParityProgress :=
  ((uniform.noDirectEpochStateWithReceiptOrder initialBoundary orderOfHistory history,
      automatonOfHistory history),
    parityOfHistory history)

/--
Equality of enriched no-direct `A`-continuation states determines the
history-derived automaton profile component.
-/
theorem noDirectEpochStateWithAContinuationData_determines_historyAutomatonState
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (hsame :
      uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          history =
        uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          history') :
    automatonOfHistory history = automatonOfHistory history' := by
  exact congrArg (fun data => (data.1).2) hsame

/--
Coherence of a continuation configuration with the history-derived current
receipt/order data and automaton profile.
-/
def ContinuationConfigurationAContinuationDataCoherent
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState) : Prop :=
    ContinuationConfigurationReceiptOrderCoherent
        containmentOrder orderOfHistory c ∧
      c.automatonState = automatonOfHistory c.history

/--
The corrected configuration carrier for the enriched no-direct finite
retraction: continuation configurations whose free fields agree with the
history-derived receipt/order and automaton-profile data.
-/
abbrev CoherentContinuationConfiguration
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState) :=
  { c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState //
      ContinuationConfigurationAContinuationDataCoherent
        containmentOrder orderOfHistory automatonOfHistory c }

/--
Coherent-configuration version of
`noDirectEpochStateWithAContinuationData_determines_historyAutomatonState`.
-/
theorem noDirectEpochStateWithAContinuationData_determines_configAutomatonState_of_coherent
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    (hcoh :
      ContinuationConfigurationAContinuationDataCoherent
        containmentOrder orderOfHistory automatonOfHistory c)
    (hcoh' :
      ContinuationConfigurationAContinuationDataCoherent
        containmentOrder orderOfHistory automatonOfHistory c')
    (hsame :
      uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c.history =
        uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c'.history) :
    c.automatonState = c'.automatonState := by
  rcases hcoh with ⟨_hreceiptOrder, hautomaton⟩
  rcases hcoh' with ⟨_hreceiptOrder', hautomaton'⟩
  have hhistory :
      automatonOfHistory c.history = automatonOfHistory c'.history :=
    noDirectEpochStateWithAContinuationData_determines_historyAutomatonState
      uniform initialBoundary orderOfHistory automatonOfHistory parityOfHistory
      hsame
  calc
    c.automatonState = automatonOfHistory c.history := hautomaton
    _ = automatonOfHistory c'.history := hhistory
    _ = c'.automatonState := hautomaton'.symm

/--
Equality of enriched no-direct `A`-continuation states determines both the
current receipt/order payload and the history-derived automaton profile.
-/
theorem noDirectEpochStateWithAContinuationData_determines_historyReceiptOrderAutomatonState
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    {history history' : History In₁ In₂ Graph Out₁ Out₂}
    (hsame :
      uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          history =
        uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          history') :
    ((currentView Proc.one history).receiptTag =
        (currentView Proc.one history').receiptTag ∧
      (currentView Proc.two history).receiptTag =
        (currentView Proc.two history').receiptTag ∧
      orderOfHistory history = orderOfHistory history') ∧
      automatonOfHistory history = automatonOfHistory history' := by
  constructor
  · exact
      noDirectEpochStateWithReceiptOrder_determines_historyReceiptOrder
        uniform initialBoundary orderOfHistory
        (congrArg (fun data => (data.1).1) hsame)
  · exact
      noDirectEpochStateWithAContinuationData_determines_historyAutomatonState
        uniform initialBoundary orderOfHistory automatonOfHistory parityOfHistory
        hsame

/--
Coherent-configuration projection from enriched no-direct `A`-continuation
state equality.  This is the preferred handle for feeding the triple-based
`AContinuationEquivalent` assemblers: the first component is the automaton
state equality, and the second component is the receipt/order triple.
-/
theorem noDirectEpochStateWithAContinuationData_determines_configStateReceiptOrder_of_coherent
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    (hcoh :
      ContinuationConfigurationAContinuationDataCoherent
        containmentOrder orderOfHistory automatonOfHistory c)
    (hcoh' :
      ContinuationConfigurationAContinuationDataCoherent
        containmentOrder orderOfHistory automatonOfHistory c')
    (hsame :
      uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c.history =
        uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c'.history) :
    c.automatonState = c'.automatonState ∧
      (c.receiptOne = c'.receiptOne ∧
        c.receiptTwo = c'.receiptTwo ∧
        containmentOrder c = containmentOrder c') := by
  constructor
  · exact
      noDirectEpochStateWithAContinuationData_determines_configAutomatonState_of_coherent
        uniform initialBoundary containmentOrder orderOfHistory automatonOfHistory
        parityOfHistory hcoh hcoh' hsame
  · exact
      noDirectEpochStateWithReceiptOrder_determines_configReceiptOrder_of_coherent
        uniform initialBoundary containmentOrder orderOfHistory hcoh.1 hcoh'.1
        (congrArg (fun data => (data.1).1) hsame)

/--
Finite parity-progress certificate for the coherent enriched retraction.

The finite quotient already stores the raw no-direct state, receipt/order data,
and automaton profile.  This certificate names the last remaining payload:
finite parity progress whose equality implies the `sameParityOutcomes` component
of `A`-continuation equivalence on coherent configurations.
-/
structure NoDirectCoherentParityProgressCertificate
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState) where
  ParityProgress : Type (max u v w x y z)
  parityProgressFinite : Fintype ParityProgress
  parityOfHistory :
    History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress
  sameParityOfProgress :
    ∀ c c' :
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory,
      parityOfHistory c.1.history = parityOfHistory c'.1.history ->
        sameParityOutcomes c.1 c'.1

attribute [instance] NoDirectCoherentParityProgressCertificate.parityProgressFinite

/--
Turn a finite regular-test quotient into the parity-progress component required
by the coherent no-direct retraction.

The remaining hypothesis is exactly the semantic content of the paper's
right-congruence/continuation closure clause: equal finite regular-test atoms
must imply equal parity outcomes for coherent continuation configurations.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestTruthQuotient
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (sameParityOfTruthAtom :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
          sameParityOutcomes c.1 c'.1) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory where
  ParityProgress :=
    ULift.{max u v w x y z, max u z} (RegularTestTruthAtom basis)
  parityProgressFinite := by
    letI := regularTestTruthAtomFintype basis
    infer_instance
  parityOfHistory := fun h =>
    ULift.up (regularTestTruthVector basis (pathOfHistory h))
  sameParityOfProgress := by
    intro c c' h
    exact sameParityOfTruthAtom c c' (congrArg ULift.down h)

/--
Truth-vector regular-test version whose remaining hypothesis is separation of
full `AContinuationEquivalent` by the regular-test outcomes.

This uses `regularTestTruthVector_eq_iff`: equality of finite truth-vector atoms
is exactly equality of membership in every basis language.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestTruthAContinuation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (basisTestsRefineAContinuation :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
          AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestTruthQuotient
    basis
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    (fun c c' htruth =>
      (basisTestsRefineAContinuation c c'
        ((regularTestTruthVector_eq_iff basis
          (pathOfHistory c.1.history)
          (pathOfHistory c'.1.history)).mp htruth)).2.2.2.2)

/--
Typed interpretation of the `continuationClosed` field of a regular-test basis
for the coherent no-direct `A`-continuation target.

This is the semantic right-congruence theorem promised by
`def:regulartestbasis`: if two coherent configurations have the same truth
value for every basis test, then they are fully `A`-continuation equivalent.
-/
def RegularTestBasisCoherentAContinuationSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState) : Prop :=
  ∀ c c' :
    CoherentContinuationConfiguration
      containmentOrder orderOfHistory automatonOfHistory,
    (∀ test,
      (pathOfHistory c.1.history ∈ basis.language test ↔
        pathOfHistory c'.1.history ∈ basis.language test)) ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1

/--
Named same-tests form of the coherent regular-test separation obligation.

This is equivalent to `RegularTestBasisCoherentAContinuationSeparation`, but it
uses `RegularTestBasisPathEquivalent` as the input predicate so proof scripts
can reuse the generic same-tests lemmas from
`prop:regulartestbasistorepair`.
-/
def RegularTestPathEquivalentCoherentAContinuationSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState) : Prop :=
  ∀ c c' :
    CoherentContinuationConfiguration
      containmentOrder orderOfHistory automatonOfHistory,
    RegularTestBasisPathEquivalent basis
      (pathOfHistory c.1.history)
      (pathOfHistory c'.1.history) ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1

/--
Turn the raw pointwise basis-test separation form into the named same-tests
form.
-/
theorem RegularTestPathEquivalentCoherentAContinuationSeparation_of_basisSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestBasisCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestPathEquivalentCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' heq
  exact separation c c' heq

/--
Turn the named same-tests separation form back into the raw pointwise basis-test
form.
-/
theorem RegularTestBasisCoherentAContinuationSeparation_of_pathEquivalentSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestPathEquivalentCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestBasisCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' heq
  exact separation c c' heq

/--
Truth-vector form of the coherent regular-test separation obligation.

Use this when the finite quotient is already stated as equality of
`regularTestTruthVector` atoms, rather than as pointwise equality of all basis
test outcomes.
-/
def RegularTestTruthVectorCoherentAContinuationSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState) : Prop :=
  ∀ c c' :
    CoherentContinuationConfiguration
      containmentOrder orderOfHistory automatonOfHistory,
    regularTestTruthVector basis (pathOfHistory c.1.history) =
      regularTestTruthVector basis (pathOfHistory c'.1.history) ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1

/--
Turn pointwise basis-test separation into truth-vector separation.
-/
theorem RegularTestTruthVectorCoherentAContinuationSeparation_of_basisSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestBasisCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestTruthVectorCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htruth
  exact
    separation c c'
      ((regularTestTruthVector_eq_iff basis
        (pathOfHistory c.1.history)
        (pathOfHistory c'.1.history)).mp htruth)

/--
Turn named same-tests separation into truth-vector separation.
-/
theorem RegularTestTruthVectorCoherentAContinuationSeparation_of_pathEquivalentSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestPathEquivalentCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestTruthVectorCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  exact
    RegularTestTruthVectorCoherentAContinuationSeparation_of_basisSeparation
      (RegularTestBasisCoherentAContinuationSeparation_of_pathEquivalentSeparation
        separation)

/--
Turn truth-vector separation back into the pointwise basis-test form.
-/
theorem RegularTestBasisCoherentAContinuationSeparation_of_truthVectorSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestTruthVectorCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestBasisCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htests
  exact
    separation c c'
      ((regularTestTruthVector_eq_iff basis
        (pathOfHistory c.1.history)
        (pathOfHistory c'.1.history)).mpr htests)

/--
Turn truth-vector separation back into the named same-tests form.
-/
theorem RegularTestPathEquivalentCoherentAContinuationSeparation_of_truthVectorSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestTruthVectorCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestPathEquivalentCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  exact
    RegularTestPathEquivalentCoherentAContinuationSeparation_of_basisSeparation
      (RegularTestBasisCoherentAContinuationSeparation_of_truthVectorSeparation
        separation)

/-- Assemble full `A`-continuation equivalence from its five paper components. -/
theorem AContinuationEquivalent_of_components
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    (hstate : c.automatonState = c'.automatonState)
    (hreceiptOne : c.receiptOne = c'.receiptOne)
    (hreceiptTwo : c.receiptTwo = c'.receiptTwo)
    (horder : containmentOrder c = containmentOrder c')
    (hparity : sameParityOutcomes c c') :
    AContinuationEquivalent sameParityOutcomes containmentOrder c c' :=
  ⟨hstate, hreceiptOne, hreceiptTwo, horder, hparity⟩

/--
Assemble full `A`-continuation equivalence when receipt/order recovery is
already packaged as the triple returned by the no-direct receipt/order bridges.
-/
theorem AContinuationEquivalent_of_state_receiptOrder_parity
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    (hstate : c.automatonState = c'.automatonState)
    (hreceiptOrder :
      c.receiptOne = c'.receiptOne ∧
        c.receiptTwo = c'.receiptTwo ∧
        containmentOrder c = containmentOrder c')
    (hparity : sameParityOutcomes c c') :
    AContinuationEquivalent sameParityOutcomes containmentOrder c c' :=
  AContinuationEquivalent_of_components
    hstate hreceiptOrder.1 hreceiptOrder.2.1 hreceiptOrder.2.2 hparity

/-- Project the parity-outcome component from full `A`-continuation equivalence. -/
theorem sameParityOutcomes_of_AContinuationEquivalent
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    (heq : AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    sameParityOutcomes c c' :=
  heq.2.2.2.2

/--
Project the parity-outcome field from a regular-test coherent
`A`-continuation separation theorem.
-/
theorem sameParityOutcomes_of_regularTestBasisSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestBasisCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory)
    {c c' :
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory}
    (htests : ∀ test,
      (pathOfHistory c.1.history ∈ basis.language test ↔
        pathOfHistory c'.1.history ∈ basis.language test)) :
    sameParityOutcomes c.1 c'.1 :=
  sameParityOutcomes_of_AContinuationEquivalent (separation c c' htests)

/--
Project the parity-outcome field from a truth-vector coherent
`A`-continuation separation theorem.
-/
theorem sameParityOutcomes_of_regularTestTruthVectorSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestTruthVectorCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory)
    {c c' :
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory}
    (htruth :
      regularTestTruthVector basis (pathOfHistory c.1.history) =
        regularTestTruthVector basis (pathOfHistory c'.1.history)) :
    sameParityOutcomes c.1 c'.1 :=
  sameParityOutcomes_of_AContinuationEquivalent (separation c c' htruth)

/--
Project the parity-outcome field from a named same-tests coherent
`A`-continuation separation theorem.
-/
theorem sameParityOutcomes_of_regularTestPathEquivalentSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestPathEquivalentCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory)
    {c c' :
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory}
    (heq : RegularTestBasisPathEquivalent basis
      (pathOfHistory c.1.history)
      (pathOfHistory c'.1.history)) :
    sameParityOutcomes c.1 c'.1 :=
  sameParityOutcomes_of_AContinuationEquivalent (separation c c' heq)

/--
Build a regular-test coherent `A`-continuation separation theorem from the
five component obligations used in the paper proof.
-/
theorem RegularTestBasisCoherentAContinuationSeparation_of_components
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (automatonState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        c.1.automatonState = c'.1.automatonState)
    (receiptOne_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        c.1.receiptOne = c'.1.receiptOne)
    (receiptTwo_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        c.1.receiptTwo = c'.1.receiptTwo)
    (containmentOrder_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        containmentOrder c.1 = containmentOrder c'.1)
    (parity_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        sameParityOutcomes c.1 c'.1) :
    RegularTestBasisCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htests
  exact
    AContinuationEquivalent_of_components
      (automatonState_eq c c' htests)
      (receiptOne_eq c c' htests)
      (receiptTwo_eq c c' htests)
      (containmentOrder_eq c c' htests)
      (parity_eq c c' htests)

/--
Build a regular-test coherent `A`-continuation separation theorem when the
receipt/order component is supplied as the triple returned by the no-direct
receipt/order bridges.
-/
theorem RegularTestBasisCoherentAContinuationSeparation_of_state_receiptOrder_parity
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (automatonState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        c.1.automatonState = c'.1.automatonState)
    (receiptOrder_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        c.1.receiptOne = c'.1.receiptOne ∧
          c.1.receiptTwo = c'.1.receiptTwo ∧
          containmentOrder c.1 = containmentOrder c'.1)
    (parity_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        sameParityOutcomes c.1 c'.1) :
    RegularTestBasisCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htests
  exact
    AContinuationEquivalent_of_state_receiptOrder_parity
      (automatonState_eq c c' htests)
      (receiptOrder_eq c c' htests)
      (parity_eq c c' htests)

/--
Build a truth-vector coherent `A`-continuation separation theorem from the five
component obligations used in the paper proof.
-/
theorem RegularTestTruthVectorCoherentAContinuationSeparation_of_components
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (automatonState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        c.1.automatonState = c'.1.automatonState)
    (receiptOne_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        c.1.receiptOne = c'.1.receiptOne)
    (receiptTwo_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        c.1.receiptTwo = c'.1.receiptTwo)
    (containmentOrder_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        containmentOrder c.1 = containmentOrder c'.1)
    (parity_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        sameParityOutcomes c.1 c'.1) :
    RegularTestTruthVectorCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htruth
  exact
    AContinuationEquivalent_of_components
      (automatonState_eq c c' htruth)
      (receiptOne_eq c c' htruth)
      (receiptTwo_eq c c' htruth)
      (containmentOrder_eq c c' htruth)
      (parity_eq c c' htruth)

/--
Build a truth-vector coherent `A`-continuation separation theorem when the
receipt/order component is supplied as the triple returned by the no-direct
receipt/order bridges.
-/
theorem RegularTestTruthVectorCoherentAContinuationSeparation_of_state_receiptOrder_parity
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (automatonState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        c.1.automatonState = c'.1.automatonState)
    (receiptOrder_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        c.1.receiptOne = c'.1.receiptOne ∧
          c.1.receiptTwo = c'.1.receiptTwo ∧
          containmentOrder c.1 = containmentOrder c'.1)
    (parity_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        sameParityOutcomes c.1 c'.1) :
    RegularTestTruthVectorCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htruth
  exact
    AContinuationEquivalent_of_state_receiptOrder_parity
      (automatonState_eq c c' htruth)
      (receiptOrder_eq c c' htruth)
      (parity_eq c c' htruth)

/--
Named-separation wrapper for the truth-vector regular-test parity certificate.

Use this when the remaining semantic theorem has already been stated as
`RegularTestBasisCoherentAContinuationSeparation`.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (separation :
      RegularTestBasisCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestTruthAContinuation
    basis
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    separation

/--
Named truth-vector separation wrapper for the regular-test parity certificate.

Use this when the remaining semantic theorem is stated directly as equality of
finite truth-vector atoms refining `AContinuationEquivalent`.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestTruthVectorSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (separation :
      RegularTestTruthVectorCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestTruthQuotient
    basis
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    (fun _ _ htruth =>
      sameParityOutcomes_of_regularTestTruthVectorSeparation separation htruth)

/--
Named same-tests separation wrapper for the regular-test parity certificate.

Use this when the remaining semantic theorem is stated with
`RegularTestBasisPathEquivalent`.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestPathEquivalentSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (separation :
      RegularTestPathEquivalentCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestSeparation
    basis
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    (RegularTestBasisCoherentAContinuationSeparation_of_pathEquivalentSeparation
      separation)

/--
Build the parity-progress certificate from the `continuationClosed` field of a
regular-test basis, once that generic field is interpreted as the coherent
`A`-continuation separation theorem above.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestContinuationClosed
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (continuationClosed_sound :
      basis.continuationClosed ->
        RegularTestBasisCoherentAContinuationSeparation
          basis pathOfHistory sameParityOutcomes containmentOrder
          orderOfHistory automatonOfHistory) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestSeparation
    basis
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    (continuationClosed_sound basis.continuationClosed_proof)

/--
Variant using the finite quotient packaged by
`RegularTestBasisRepairClauses`.  This is the bridge from
`prop:regulartestbasistorepair` to the no-direct theorem-facing parity-progress
certificate.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestRepairClauses
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    (clauses : RegularTestBasisRepairClauses basis)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (sameParityOfRepairAtom :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
          sameParityOutcomes c.1 c'.1) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory where
  ParityProgress :=
    ULift.{max u v w x y z, max u z} clauses.quotient.Atom
  parityProgressFinite := by
    infer_instance
  parityOfHistory := fun h =>
    ULift.up (clauses.quotient.encode (pathOfHistory h))
  sameParityOfProgress := by
    intro c c' h
    exact sameParityOfRepairAtom c c' (congrArg ULift.down h)

/--
`A`-continuation version of
`noDirectCoherentParityProgressCertificateOfRegularTestRepairClauses`.

This is the paper-facing form of the regular-test obligation: equality of the
finite repair atom refines full `AContinuationEquivalent`; the parity-progress
certificate only needs the final parity-outcome component of that equivalence.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestRepairAContinuation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    (clauses : RegularTestBasisRepairClauses basis)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (repairAtomRefinesAContinuation :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
          AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestRepairClauses
    clauses
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    (fun c c' h =>
      (repairAtomRefinesAContinuation c c' h).2.2.2.2)

/--
Named repair-atom version of the coherent `A`-continuation separation
obligation.  This is the repair-quotient analogue of
`RegularTestBasisCoherentAContinuationSeparation`.
-/
def RegularTestRepairCoherentAContinuationSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    (clauses : RegularTestBasisRepairClauses basis)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState) : Prop :=
  ∀ c c' :
    CoherentContinuationConfiguration
      containmentOrder orderOfHistory automatonOfHistory,
    clauses.quotient.encode (pathOfHistory c.1.history) =
      clauses.quotient.encode (pathOfHistory c'.1.history) ->
      AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1

/--
Project the parity-outcome field from a repair-atom coherent
`A`-continuation separation theorem.
-/
theorem sameParityOutcomes_of_regularTestRepairSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {clauses : RegularTestBasisRepairClauses basis}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestRepairCoherentAContinuationSeparation
        clauses pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory)
    {c c' :
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory}
    (hatom :
      clauses.quotient.encode (pathOfHistory c.1.history) =
        clauses.quotient.encode (pathOfHistory c'.1.history)) :
    sameParityOutcomes c.1 c'.1 :=
  sameParityOutcomes_of_AContinuationEquivalent (separation c c' hatom)

/--
Build a repair-atom coherent `A`-continuation separation theorem from the five
component obligations used in the paper proof.
-/
theorem RegularTestRepairCoherentAContinuationSeparation_of_components
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {clauses : RegularTestBasisRepairClauses basis}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (automatonState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        c.1.automatonState = c'.1.automatonState)
    (receiptOne_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        c.1.receiptOne = c'.1.receiptOne)
    (receiptTwo_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        c.1.receiptTwo = c'.1.receiptTwo)
    (containmentOrder_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        containmentOrder c.1 = containmentOrder c'.1)
    (parity_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        sameParityOutcomes c.1 c'.1) :
    RegularTestRepairCoherentAContinuationSeparation
      clauses pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' hatom
  exact
    AContinuationEquivalent_of_components
      (automatonState_eq c c' hatom)
      (receiptOne_eq c c' hatom)
      (receiptTwo_eq c c' hatom)
      (containmentOrder_eq c c' hatom)
      (parity_eq c c' hatom)

/--
Build a repair-atom coherent `A`-continuation separation theorem when the
receipt/order component is supplied as the triple returned by the no-direct
receipt/order bridges.
-/
theorem RegularTestRepairCoherentAContinuationSeparation_of_state_receiptOrder_parity
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {clauses : RegularTestBasisRepairClauses basis}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (automatonState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        c.1.automatonState = c'.1.automatonState)
    (receiptOrder_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        c.1.receiptOne = c'.1.receiptOne ∧
          c.1.receiptTwo = c'.1.receiptTwo ∧
          containmentOrder c.1 = containmentOrder c'.1)
    (parity_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        sameParityOutcomes c.1 c'.1) :
    RegularTestRepairCoherentAContinuationSeparation
      clauses pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' hatom
  exact
    AContinuationEquivalent_of_state_receiptOrder_parity
      (automatonState_eq c c' hatom)
      (receiptOrder_eq c c' hatom)
      (parity_eq c c' hatom)

/--
Turn truth-vector coherent separation into repair-atom separation for the
canonical repair clauses whose atom is exactly `regularTestTruthVector`.
-/
theorem RegularTestRepairCoherentAContinuationSeparation_of_canonicalTruthVectorSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestTruthVectorCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestRepairCoherentAContinuationSeparation
      (regularTestBasisRepairClausesOfTruthVector basis)
      pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' hatom
  exact separation c c' (by simpa using hatom)

/--
Turn pointwise basis-test coherent separation into repair-atom separation for
the canonical repair clauses.
-/
theorem RegularTestRepairCoherentAContinuationSeparation_of_canonicalBasisSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (separation :
      RegularTestBasisCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    RegularTestRepairCoherentAContinuationSeparation
      (regularTestBasisRepairClausesOfTruthVector basis)
      pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' hatom
  exact
    separation c c'
      ((regularTestBasisRepairClausesOfTruthVector_encode_eq_iff basis
        (pathOfHistory c.1.history)
        (pathOfHistory c'.1.history)).mp hatom)

/--
Named-separation wrapper for the repair-quotient parity-progress certificate.
Use this when the remaining semantic theorem has been stated as
`RegularTestRepairCoherentAContinuationSeparation`.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestRepairSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    (clauses : RegularTestBasisRepairClauses basis)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (separation :
      RegularTestRepairCoherentAContinuationSeparation
        clauses pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestRepairAContinuation
    clauses
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    separation

/--
Canonical-repair parity-progress certificate from truth-vector coherent
separation.  This keeps the resulting progress quotient aligned with
`regularTestBasisRepairClausesOfTruthVector`.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestCanonicalRepairTruthVectorSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (separation :
      RegularTestTruthVectorCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestRepairSeparation
    (regularTestBasisRepairClausesOfTruthVector basis)
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    (RegularTestRepairCoherentAContinuationSeparation_of_canonicalTruthVectorSeparation
      separation)

/--
Canonical-repair parity-progress certificate from pointwise basis-test coherent
separation.
-/
noncomputable def noDirectCoherentParityProgressCertificateOfRegularTestCanonicalRepairBasisSeparation
    {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType)
    (pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType)
    (sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (separation :
      RegularTestBasisCoherentAContinuationSeparation
        basis pathOfHistory sameParityOutcomes containmentOrder
        orderOfHistory automatonOfHistory) :
    NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
      sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory :=
  noDirectCoherentParityProgressCertificateOfRegularTestRepairSeparation
    (regularTestBasisRepairClausesOfTruthVector basis)
    pathOfHistory
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    (RegularTestRepairCoherentAContinuationSeparation_of_canonicalBasisSeparation
      separation)

/--
Equality of the enriched no-direct finite state proves full
`A`-continuation equivalence for coherent continuation configurations, provided
the explicit parity-progress component is sound for `sameParityOutcomes`.

This isolates the real remaining semantic content: once the paper supplies a
finite parity-progress quotient, the enriched no-direct state determines the
automaton state, both receipt tags, the containment order, and the parity
outcome component required by `def:Acontinuation`.
-/
theorem noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherent
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (sameParityOfProgress :
      ∀ c c',
        parityOfHistory c.history = parityOfHistory c'.history ->
          sameParityOutcomes c c')
    {c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState}
    (hcoh :
      ContinuationConfigurationAContinuationDataCoherent
        containmentOrder orderOfHistory automatonOfHistory c)
    (hcoh' :
      ContinuationConfigurationAContinuationDataCoherent
        containmentOrder orderOfHistory automatonOfHistory c')
    (hsame :
      uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c.history =
        uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c'.history) :
    AContinuationEquivalent sameParityOutcomes containmentOrder c c' := by
  rcases
    noDirectEpochStateWithAContinuationData_determines_configStateReceiptOrder_of_coherent
      uniform initialBoundary containmentOrder orderOfHistory automatonOfHistory
      parityOfHistory hcoh hcoh' hsame with
    ⟨hautomatonState, hreceiptOrder⟩
  have hparityState :
      parityOfHistory c.history = parityOfHistory c'.history := by
    exact congrArg Prod.snd hsame
  exact
    AContinuationEquivalent_of_state_receiptOrder_parity
      hautomatonState hreceiptOrder
      (sameParityOfProgress c c' hparityState)

/--
Subtype version of
`noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherent`.
The parity-progress soundness hypothesis only has to hold on coherent
continuation configurations, which is the correct carrier for the enriched
finite retraction.
-/
theorem noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherentSubtype
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (sameParityOfProgress :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        parityOfHistory c.1.history = parityOfHistory c'.1.history ->
          sameParityOutcomes c.1 c'.1)
    {c c' :
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory}
    (hsame :
      uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c.1.history =
        uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory parityOfHistory
          c'.1.history) :
    AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1 := by
  rcases
    noDirectEpochStateWithAContinuationData_determines_configStateReceiptOrder_of_coherent
      uniform initialBoundary containmentOrder orderOfHistory automatonOfHistory
      parityOfHistory c.2 c'.2 hsame with
    ⟨hautomatonState, hreceiptOrder⟩
  have hparityState :
      parityOfHistory c.1.history = parityOfHistory c'.1.history := by
    exact congrArg Prod.snd hsame
  exact
    AContinuationEquivalent_of_state_receiptOrder_parity
      hautomatonState hreceiptOrder
      (sameParityOfProgress c c' hparityState)

/--
Certificate-packaged form of
`noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherentSubtype`.
Use this when the parity-progress component has already been packaged as
`NoDirectCoherentParityProgressCertificate`: equality of the enriched no-direct
state then directly yields full `A`-continuation equivalence.
-/
theorem AContinuationEquivalent_of_enrichedNoDirectStateParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    {c c' :
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory}
    (hsame :
      uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory
          parityProgress.parityOfHistory c.1.history =
        uniform.noDirectEpochStateWithAContinuationData
          initialBoundary orderOfHistory automatonOfHistory
          parityProgress.parityOfHistory c'.1.history) :
    AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1 :=
  noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherentSubtype
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityProgress.parityOfHistory
    parityProgress.sameParityOfProgress
    hsame

/--
Build the regular-test coherent separation theorem from equality of the
enriched no-direct `A`-continuation state.  This is useful after a concrete
regular-test quotient has been shown to determine the whole enriched state:
the automaton, receipt/order, and parity fields are then projected uniformly by
`AContinuationEquivalent_of_enrichedNoDirectStateParityProgressCertificate`.
-/
theorem RegularTestBasisCoherentAContinuationSeparation_of_enrichedNoDirectState
    {Alphabet : Type u} {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (enrichedState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        (∀ test,
          (pathOfHistory c.1.history ∈ basis.language test ↔
            pathOfHistory c'.1.history ∈ basis.language test)) ->
        uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory
            parityProgress.parityOfHistory c.1.history =
          uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory
            parityProgress.parityOfHistory c'.1.history) :
    RegularTestBasisCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htests
  exact
    AContinuationEquivalent_of_enrichedNoDirectStateParityProgressCertificate
      uniform initialBoundary sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory parityProgress
      (enrichedState_eq c c' htests)

/--
Truth-vector analogue of
`RegularTestBasisCoherentAContinuationSeparation_of_enrichedNoDirectState`.
After a finite truth-vector quotient is proved to determine the enriched
no-direct state, this wrapper supplies the full coherent `A`-continuation
separation theorem.
-/
theorem RegularTestTruthVectorCoherentAContinuationSeparation_of_enrichedNoDirectState
    {Alphabet : Type u} {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (enrichedState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        regularTestTruthVector basis (pathOfHistory c.1.history) =
          regularTestTruthVector basis (pathOfHistory c'.1.history) ->
        uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory
            parityProgress.parityOfHistory c.1.history =
          uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory
            parityProgress.parityOfHistory c'.1.history) :
    RegularTestTruthVectorCoherentAContinuationSeparation
      basis pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' htruth
  exact
    AContinuationEquivalent_of_enrichedNoDirectStateParityProgressCertificate
      uniform initialBoundary sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory parityProgress
      (enrichedState_eq c c' htruth)

/--
Repair-atom analogue of
`RegularTestBasisCoherentAContinuationSeparation_of_enrichedNoDirectState`.
After a repair quotient is proved to determine the enriched no-direct state,
this wrapper supplies the full coherent `A`-continuation separation theorem.
-/
theorem RegularTestRepairCoherentAContinuationSeparation_of_enrichedNoDirectState
    {Alphabet : Type u} {Boundary : Type u} {EdgeType : Type z}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    {basis : FiniteRegularTestBasis.{u, z, max u z} Boundary EdgeType}
    {clauses : RegularTestBasisRepairClauses basis}
    {pathOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> TypedPath EdgeType}
    {sameParityOutcomes :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration.{v, w, x, y, max u v w x y z}
        In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    {orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder}
    {automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState}
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (enrichedState_eq :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        clauses.quotient.encode (pathOfHistory c.1.history) =
          clauses.quotient.encode (pathOfHistory c'.1.history) ->
        uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory
            parityProgress.parityOfHistory c.1.history =
          uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory
            parityProgress.parityOfHistory c'.1.history) :
    RegularTestRepairCoherentAContinuationSeparation
      clauses pathOfHistory sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory := by
  intro c c' hatom
  exact
    AContinuationEquivalent_of_enrichedNoDirectStateParityProgressCertificate
      uniform initialBoundary sameParityOutcomes containmentOrder
      orderOfHistory automatonOfHistory parityProgress
      (enrichedState_eq c c' hatom)

/--
Rotating access-state semantics for the corrected enriched no-direct quotient.

Unlike `noDirectRotatingAccessStateSemanticsOfHistory`, this state map does not
try to recover receipt/order data from the raw no-direct state.  The receipt
tags, containment order, automaton profile, and parity progress are explicit
finite components; equality of the enriched state therefore refines
`A`-continuation equivalence for coherent configurations.
-/
noncomputable def noDirectEnrichedRotatingAccessStateSemanticsOfHistory
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    [Fintype AState]
    [Fintype ParityProgress]
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (configurationCoherent :
      ∀ c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState,
        ContinuationConfigurationAContinuationDataCoherent
          containmentOrder orderOfHistory automatonOfHistory c)
    (sameParityOfProgress :
      ∀ c c',
        parityOfHistory c.history = parityOfHistory c'.history ->
          sameParityOutcomes c c')
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy) :
    RotatingAccessStateSemantics
      (ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
      (AContinuationEquivalent sameParityOutcomes containmentOrder) := by
  classical
  letI : Fintype
      (EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two)) :=
    Classical.choice (noDirectEpochTransformer_rotating_state_finite uniform)
  exact {
    State :=
      ((EpochRotatingAccessState
            uniform.boundary
            (uniform.summary Proc.one)
            (uniform.summary Proc.two) ×
          ReceiptOrderData) ×
        AState) ×
        ParityProgress
    stateFinite := inferInstance
    accessState := fun c =>
      uniform.noDirectEpochStateWithAContinuationData
        initialBoundary orderOfHistory automatonOfHistory parityOfHistory
        c.history
    determinesReceiptAndOrder :=
      ∀ c c',
        uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory parityOfHistory
            c.history =
          uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory parityOfHistory
            c'.history ->
          c.receiptOne = c'.receiptOne ∧
            c.receiptTwo = c'.receiptTwo ∧
            containmentOrder c = containmentOrder c'
    updateClosed := updateClosed
    preservesDynamicHierarchy := preservesDynamicHierarchy
    determinesReceiptAndOrder_proof := by
      intro c c' hsame
      have hcont :
          AContinuationEquivalent sameParityOutcomes containmentOrder c c' :=
        noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherent
          uniform initialBoundary sameParityOutcomes containmentOrder
          orderOfHistory automatonOfHistory parityOfHistory
          sameParityOfProgress
          (configurationCoherent c)
          (configurationCoherent c')
          hsame
      exact ⟨hcont.2.1, hcont.2.2.1, hcont.2.2.2.1⟩
    updateClosed_proof := updateClosed_proof
    preservesDynamicHierarchy_proof := preservesDynamicHierarchy_proof
    refinesAContinuation := by
      intro c c' hsame
      exact
        noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherent
          uniform initialBoundary sameParityOutcomes containmentOrder
          orderOfHistory automatonOfHistory parityOfHistory
          sameParityOfProgress
          (configurationCoherent c)
          (configurationCoherent c')
          hsame
    }

/--
Rotating access-state semantics for the enriched quotient over the coherent
configuration subtype.

This is the mathematically usable version of
`noDirectEnrichedRotatingAccessStateSemanticsOfHistory`: it does not require all
arbitrary continuation configurations to be coherent.  Coherence is part of the
carrier, so the access-state refinement proof is unconditional on that carrier.
-/
noncomputable def noDirectEnrichedRotatingAccessStateSemanticsOfCoherentHistory
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a} {ParityProgress : Type p}
    [Fintype AState]
    [Fintype ParityProgress]
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (sameParityOfProgress :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        parityOfHistory c.1.history = parityOfHistory c'.1.history ->
          sameParityOutcomes c.1 c'.1)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy) :
    RotatingAccessStateSemantics
      (CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory)
      (fun c c' =>
        AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1) := by
  classical
  letI : Fintype
      (EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two)) :=
    Classical.choice (noDirectEpochTransformer_rotating_state_finite uniform)
  exact {
    State :=
      ((EpochRotatingAccessState
            uniform.boundary
            (uniform.summary Proc.one)
            (uniform.summary Proc.two) ×
          ReceiptOrderData) ×
        AState) ×
        ParityProgress
    stateFinite := inferInstance
    accessState := fun c =>
      uniform.noDirectEpochStateWithAContinuationData
        initialBoundary orderOfHistory automatonOfHistory parityOfHistory
        c.1.history
    determinesReceiptAndOrder :=
      (
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory parityOfHistory
            c.1.history =
          uniform.noDirectEpochStateWithAContinuationData
            initialBoundary orderOfHistory automatonOfHistory parityOfHistory
            c'.1.history ->
          c.1.receiptOne = c'.1.receiptOne ∧
            c.1.receiptTwo = c'.1.receiptTwo ∧
            containmentOrder c.1 = containmentOrder c'.1)
    updateClosed := updateClosed
    preservesDynamicHierarchy := preservesDynamicHierarchy
    determinesReceiptAndOrder_proof := by
      intro c c' hsame
      have hcont :
          AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1 :=
        noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherentSubtype
          uniform initialBoundary sameParityOutcomes containmentOrder
          orderOfHistory automatonOfHistory parityOfHistory
          sameParityOfProgress
          hsame
      exact ⟨hcont.2.1, hcont.2.2.1, hcont.2.2.2.1⟩
    updateClosed_proof := updateClosed_proof
    preservesDynamicHierarchy_proof := preservesDynamicHierarchy_proof
    refinesAContinuation := by
      intro c c' hsame
      exact
        noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherentSubtype
          uniform initialBoundary sameParityOutcomes containmentOrder
          orderOfHistory automatonOfHistory parityOfHistory
          sameParityOfProgress
          hsame
    }

/--
Certificate-packaged version of
`noDirectEnrichedRotatingAccessStateSemanticsOfCoherentHistory`.

Once Step 3 has produced a `NoDirectCoherentParityProgressCertificate`, this is
the preferred rotating-access semantics constructor: it keeps the parity carrier,
the finite instance, and the parity-soundness projection bundled together.
-/
noncomputable def noDirectEnrichedRotatingAccessStateSemanticsOfCoherentHistoryOfParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    [Fintype AState]
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy) :
    RotatingAccessStateSemantics
      (CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory)
      (fun c c' =>
        AContinuationEquivalent sameParityOutcomes containmentOrder c.1 c'.1) :=
  noDirectEnrichedRotatingAccessStateSemanticsOfCoherentHistory
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityProgress.parityOfHistory
    parityProgress.sameParityOfProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof

/--
Concrete receipt/order preservation property for the no-direct rotating access
state.  This is a named version of the receipt and containment-order part of
`AContinuationEquivalent`, because the finite-index route records it as a
paper-facing side condition.
-/
def NoDirectAccessStateDeterminesReceiptAndOrder
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder) : Prop :=
  ∀ c c',
    uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
      uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
    c.receiptOne = c'.receiptOne ∧
      c.receiptTwo = c'.receiptTwo ∧
      containmentOrder c = containmentOrder c'

/--
If equality of no-direct access states refines `A`-continuation equivalence,
then receipt tags and the containment-order component are determined
automatically.
-/
theorem noDirectAccessState_determinesReceiptAndOrder_of_refinesAContinuation
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (refinesAContinuation :
      ∀ c c',
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    NoDirectAccessStateDeterminesReceiptAndOrder
      uniform initialBoundary containmentOrder := by
  intro c c' hsame
  rcases refinesAContinuation c c' hsame with
    ⟨_hautomaton, hreceiptOne, hreceiptTwo, horder, _hparity⟩
  exact ⟨hreceiptOne, hreceiptTwo, horder⟩

/--
Component-refinement version of
`noDirectAccessState_determinesReceiptAndOrder_of_refinesAContinuation`.
-/
theorem noDirectAccessState_determinesReceiptAndOrder_of_components
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    NoDirectAccessStateDeterminesReceiptAndOrder
      uniform initialBoundary containmentOrder :=
  noDirectAccessState_determinesReceiptAndOrder_of_refinesAContinuation
    uniform
    initialBoundary
    sameParityOutcomes
      containmentOrder
      (noDirectHistoryAccessState_refines_AContinuation_of_components
        uniform
        initialBoundary
        sameParityOutcomes
        containmentOrder
        boundaryRefines
        sideOneRefines
        sideTwoRefines)

/--
The named component-refinement certificate determines the current receipt tags
and non-fringe containment-order component.
-/
theorem NoDirectHistoryAccessStateComponentRefinement.determinesReceiptAndOrder
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂}
    {initialBoundary : uniform.boundary}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    (refinement :
      NoDirectHistoryAccessStateComponentRefinement
        uniform initialBoundary sameParityOutcomes containmentOrder) :
    NoDirectAccessStateDeterminesReceiptAndOrder
      uniform initialBoundary containmentOrder :=
  noDirectAccessState_determinesReceiptAndOrder_of_refinesAContinuation
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    refinement.refinesAContinuation

/--
Concrete rotating access-state semantics for the no-direct history map, once
the paper's semantic side conditions prove that equality of this state refines
the chosen `A`-continuation relation.
-/
noncomputable def noDirectRotatingAccessStateSemanticsOfHistory
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (determinesReceiptAndOrder : Prop)
    (determinesReceiptAndOrder_proof : determinesReceiptAndOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (refinesAContinuation :
      ∀ c c',
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    RotatingAccessStateSemantics
      (ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
      (AContinuationEquivalent sameParityOutcomes containmentOrder) := by
  classical
  letI : Fintype
      (EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two)) :=
    Classical.choice (noDirectEpochTransformer_rotating_state_finite uniform)
  exact {
    State :=
      EpochRotatingAccessState
        uniform.boundary
        (uniform.summary Proc.one)
        (uniform.summary Proc.two)
    stateFinite := inferInstance
    accessState := fun c =>
      uniform.noDirectEpochStateAfterHistory initialBoundary c.history
    determinesReceiptAndOrder := determinesReceiptAndOrder
    updateClosed := updateClosed
    preservesDynamicHierarchy := preservesDynamicHierarchy
    determinesReceiptAndOrder_proof := determinesReceiptAndOrder_proof
    updateClosed_proof := updateClosed_proof
    preservesDynamicHierarchy_proof := preservesDynamicHierarchy_proof
    refinesAContinuation := refinesAContinuation
  }

/--
No-direct rotating access-state semantics where the receipt/order side
condition is derived from the `A`-continuation refinement instead of supplied
as a separate hypothesis.
-/
noncomputable def noDirectRotatingAccessStateSemanticsOfHistoryFromRefinement
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (refinesAContinuation :
      ∀ c c',
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    RotatingAccessStateSemantics
      (ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
      (AContinuationEquivalent sameParityOutcomes containmentOrder) :=
  noDirectRotatingAccessStateSemanticsOfHistory
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    (NoDirectAccessStateDeterminesReceiptAndOrder
      uniform initialBoundary containmentOrder)
    (noDirectAccessState_determinesReceiptAndOrder_of_refinesAContinuation
      uniform initialBoundary sameParityOutcomes containmentOrder
      refinesAContinuation)
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    refinesAContinuation

/--
Concrete no-direct rotating access-state semantics from the three component
congruence facts cited in the paper proof of Lemma `lem:epochtorotating`.
-/
noncomputable def noDirectRotatingAccessStateSemanticsOfHistoryComponents
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (determinesReceiptAndOrder : Prop)
    (determinesReceiptAndOrder_proof : determinesReceiptAndOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    RotatingAccessStateSemantics
      (ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
      (AContinuationEquivalent sameParityOutcomes containmentOrder) :=
  noDirectRotatingAccessStateSemanticsOfHistory
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    determinesReceiptAndOrder
    determinesReceiptAndOrder_proof
    updateClosed
    updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      (noDirectHistoryAccessState_refines_AContinuation_of_components
        uniform
        initialBoundary
        sameParityOutcomes
        containmentOrder
        boundaryRefines
        sideOneRefines
        sideTwoRefines)

/--
Component-congruence constructor where receipt/order preservation is derived
from the three refinement cases.
-/
noncomputable def noDirectRotatingAccessStateSemanticsOfHistoryComponentsFromRefinement
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c') :
    RotatingAccessStateSemantics
      (ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
      (AContinuationEquivalent sameParityOutcomes containmentOrder) :=
  noDirectRotatingAccessStateSemanticsOfHistoryFromRefinement
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
      (noDirectHistoryAccessState_refines_AContinuation_of_components
        uniform
        initialBoundary
        sameParityOutcomes
        containmentOrder
        boundaryRefines
        sideOneRefines
        sideTwoRefines)

/--
Concrete no-direct rotating access-state semantics from the named component
refinement certificate.
-/
noncomputable def NoDirectHistoryAccessStateComponentRefinement.toRotatingAccessStateSemantics
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂}
    {initialBoundary : uniform.boundary}
    {sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop}
    {containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder}
    (refinement :
      NoDirectHistoryAccessStateComponentRefinement
        uniform initialBoundary sameParityOutcomes containmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy) :
    RotatingAccessStateSemantics
      (ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
      (AContinuationEquivalent sameParityOutcomes containmentOrder) :=
  noDirectRotatingAccessStateSemanticsOfHistoryFromRefinement
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    refinement.refinesAContinuation

/--
Certificate for the finite quotient used in the no-direct-reversal fragment.
The fields mirror the proof obligations cited in `prop:nodirectfromjournal`.
-/
structure NoDirectReversalFragmentCertificate
    (Alphabet : Type u)
    (In₁ : Type v) (In₂ : Type w) (Out₁ : Type x) (Out₂ : Type y) where
  uniform : UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z} Alphabet In₁ In₂ Out₁ Out₂
  State : Type (max u v w x y z)
  stateFinite : Fintype State
  Realizable : Prop
  finiteGame : FiniteDynamicHierarchyParityGame.{max u v w x y z, max u v w x y z}
  finiteGameRealizableIff : finiteGame.realizable ↔ Realizable
  finiteFringeCompilation : Prop
  boundaryAndBlockTransitionsEffective : Prop
  continuationPreservedBlockByBlock : Prop
  dynamicallyHierarchicalAfterFringeElim : Prop
  finiteFringeCompilation_proof : finiteFringeCompilation
  boundaryAndBlockTransitionsEffective_proof : boundaryAndBlockTransitionsEffective
  continuationPreservedBlockByBlock_proof : continuationPreservedBlockByBlock
  dynamicallyHierarchicalAfterFringeElim_proof : dynamicallyHierarchicalAfterFringeElim

attribute [instance] NoDirectReversalFragmentCertificate.stateFinite

/--
Proposition `prop:nodirectfromjournal`: once the uniform one-directional
summaries have been assembled into the no-direct-reversal finite quotient and
the cited fringe/hierarchy obligations hold, the restricted fragment reduces to
a finite dynamic-hierarchy parity game and is decidable.
-/
noncomputable def no_direct_from_journal
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (certificate :
      NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂) :
    Decidable certificate.Realizable := by
  exact
    conditional_decidability_from_finite_fringe
      {
        finiteGame := certificate.finiteGame
        finiteFringeCompilation := certificate.finiteFringeCompilation
        realizabilityEquivalent := certificate.finiteGameRealizableIff
        finiteFringeCompilation_proof := certificate.finiteFringeCompilation_proof
      }

/--
Paper-facing package exposing the no-direct-reversal side conditions that feed
the finite-game decision procedure.
-/
theorem no_direct_from_journal_certificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (certificate :
      NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂) :
    certificate.finiteFringeCompilation ∧
      certificate.boundaryAndBlockTransitionsEffective ∧
      certificate.continuationPreservedBlockByBlock ∧
      certificate.dynamicallyHierarchicalAfterFringeElim ∧
      certificate.finiteGame.dynamicHierarchy ∧
      certificate.finiteGame.parityObjective ∧
      Nonempty (Decidable certificate.Realizable) := by
  exact
    ⟨certificate.finiteFringeCompilation_proof,
      certificate.boundaryAndBlockTransitionsEffective_proof,
      certificate.continuationPreservedBlockByBlock_proof,
      certificate.dynamicallyHierarchicalAfterFringeElim_proof,
      certificate.finiteGame.dynamicHierarchy_proof,
      certificate.finiteGame.parityObjective_proof,
      ⟨no_direct_from_journal certificate⟩⟩

/--
Submission-facing restricted theorem payload.

This is the honest no-direct-reversal result: after the finite
no-direct certificate has been assembled, the remaining data are exactly the
finite-fringe compilation, block-level effectiveness and continuation
preservation, dynamic hierarchy after fringe elimination, and the finite
parity game.  No direct-reversal handoff is used here.
-/
theorem no_direct_reversal_restricted_theorem_payload
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (certificate :
      NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂) :
    certificate.finiteFringeCompilation ∧
      certificate.boundaryAndBlockTransitionsEffective ∧
      certificate.continuationPreservedBlockByBlock ∧
      certificate.dynamicallyHierarchicalAfterFringeElim ∧
      certificate.finiteGame.dynamicHierarchy ∧
      certificate.finiteGame.parityObjective ∧
      Nonempty (Decidable certificate.Realizable) := by
  exact no_direct_from_journal_certificate certificate

/--
Turn a no-direct finite-game certificate whose `Realizable` proposition is
identified with a concrete execution predicate into the compiled parity
specification interface used by `thm:main`.

This is the certificate-level bridge: the no-direct journal construction
already carries the finite game and the finite-game realizability equivalence;
the only extra input is the statement that its abstract `Realizable` proposition
is exactly realizability of the target execution predicate.
-/
noncomputable def NoDirectReversalFragmentCertificate.toEffectiveParitySpecification
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    (certificate :
      NoDirectReversalFragmentCertificate
        (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)
    (predicate : Specification In₁ In₂ Out₁ Out₂)
    (realizableEquivalent :
      certificate.Realizable ↔
        ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
          ∀ env : EnvironmentSequence In₁ In₂,
            predicate (execution σ env)) :
    EffectiveParitySpecification In₁ In₂ Out₁ Out₂ where
  predicate := predicate
  finiteGame := certificate.finiteGame
  realizabilityEquivalent :=
    certificate.finiteGameRealizableIff.trans realizableEquivalent

/--
Build the no-direct-reversal certificate from the repository's generic finite
`A`-index decision certificate.

This is the main Lean handoff for attacking the no-direct fragment: after the
uniform one-directional summaries have been assembled into a finite quotient
and that quotient is packaged as `FiniteAIndexDecisionCertificate`, the
no-direct-specific certificate only needs the finite-fringe compilation and the
block-level effectiveness/preservation side conditions.
-/
noncomputable def noDirectReversalFragmentCertificateOfFiniteAIndex
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {Config : Type q} {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (finiteIndex :
      FiniteAIndexDecisionCertificate.{q, max u v w x y z,
        max u v w x y z, max u v w x y z}
        Config Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ where
  uniform := uniform
  State := finiteIndex.Quotient
  stateFinite := finiteIndex.quotientFinite
  Realizable := Realizable
  finiteGame := finiteIndex.finiteGame
  finiteGameRealizableIff := finiteIndex.finiteGameRealizableIff
  finiteFringeCompilation := finiteFringeCompilation
  boundaryAndBlockTransitionsEffective := boundaryAndBlockTransitionsEffective
  continuationPreservedBlockByBlock := continuationPreservedBlockByBlock
  dynamicallyHierarchicalAfterFringeElim :=
    finiteIndex.finiteNonFringeSummariesHierarchical ∧
      finiteIndex.olderReceiptTagsRecoverable
  finiteFringeCompilation_proof := finiteFringeCompilation_proof
  boundaryAndBlockTransitionsEffective_proof :=
    boundaryAndBlockTransitionsEffective_proof
  continuationPreservedBlockByBlock_proof :=
    continuationPreservedBlockByBlock_proof
  dynamicallyHierarchicalAfterFringeElim_proof :=
    ⟨finiteIndex.finiteNonFringeSummariesHierarchical_proof,
      finiteIndex.olderReceiptTagsRecoverable_proof⟩

/--
No-direct-reversal decidability from a finite hierarchy-preserving `A`-index.
-/
noncomputable def no_direct_from_finite_A_index
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {Config : Type q} {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (finiteIndex :
      FiniteAIndexDecisionCertificate.{q, max u v w x y z,
        max u v w x y z, max u v w x y z}
        Config Realizable) :
    Decidable Realizable :=
  no_direct_from_journal
    (noDirectReversalFragmentCertificateOfFiniteAIndex
      uniform
      finiteFringeCompilation
      finiteFringeCompilation_proof
      boundaryAndBlockTransitionsEffective
      boundaryAndBlockTransitionsEffective_proof
      continuationPreservedBlockByBlock
      continuationPreservedBlockByBlock_proof
      finiteIndex)

/--
No-direct-reversal decidability from a semantic rotating access-state map.

This is the most concrete currently available proof route: the no-direct
construction should define the rotating access state produced by the
one-directional summaries and `both`-boundary resets, then prove that equal
access states refine continuation equivalence.  The generic finite-`A`-index
and finite-game steps are discharged here.
-/
noncomputable def no_direct_from_rotating_access_state
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {Config : Type q}
    {AContinuation : Config -> Config -> Prop}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (sem :
      RotatingAccessStateSemantics.{q, max u v w x y z}
        Config AContinuation)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_finite_A_index
    uniform
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    (finiteAIndexDecisionCertificateOfRotatingAccessState
      sem
      transitionRelationEffective
      transitionRelationEffective_proof
      finiteNonFringeSummariesHierarchical
      finiteNonFringeSummariesHierarchical_proof
      olderReceiptTagsRecoverable
      olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff)

/--
No-direct decidability from the corrected enriched history access-state map.

This is the finite-index route that avoids the refuted raw no-direct quotient:
the access state contains the raw no-direct state, current receipt/order data,
the automaton profile, and parity progress.  The only semantic payload still
required for `A`-continuation equivalence is that equality of parity progress
implies `sameParityOutcomes`, plus coherence of configurations with the
history-derived fields.
-/
noncomputable def no_direct_from_enriched_history_access_state
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (configurationCoherent :
      ∀ c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState,
        ContinuationConfigurationAContinuationDataCoherent
          containmentOrder orderOfHistory automatonOfHistory c)
    (sameParityOfProgress :
      ∀ c c',
        parityOfHistory c.history = parityOfHistory c'.history ->
          sameParityOutcomes c c')
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_rotating_access_state
    uniform
    (noDirectEnrichedRotatingAccessStateSemanticsOfHistory
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      orderOfHistory
      automatonOfHistory
      parityOfHistory
      configurationCoherent
      sameParityOfProgress
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof)
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff

/--
No-direct decidability from the enriched no-direct quotient over coherent
continuation configurations.

This is the corrected finite-index decision route when the semantic carrier is
restricted to configurations whose free fields agree with their histories.  It
therefore avoids the impossible premise that every arbitrary
`ContinuationConfiguration` is coherent.
-/
noncomputable def no_direct_from_enriched_coherent_history_access_state
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (sameParityOfProgress :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        parityOfHistory c.1.history = parityOfHistory c'.1.history ->
          sameParityOutcomes c.1 c'.1)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_rotating_access_state
    uniform
    (noDirectEnrichedRotatingAccessStateSemanticsOfCoherentHistory
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      orderOfHistory
      automatonOfHistory
      parityOfHistory
      sameParityOfProgress
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof)
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
    (finiteGame := finiteGame)
    (finiteGameRealizableIff := finiteGameRealizableIff)

/--
Finite `A`-index certificate for the coherent enriched no-direct quotient from
a named parity-progress certificate.

This is the reusable Step 4 handoff below the no-direct fragment certificate:
the quotient is exactly the enriched no-direct access state over coherent
configurations, while hierarchy/recoverability and finite-game data remain
explicit certificate fields.
-/
noncomputable def finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateOfParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    FiniteAIndexDecisionCertificate.{max u v w x y z,
      max u v w x y z, max u v w x y z, max u v w x y z}
      (CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory)
      Realizable :=
  finiteAIndexDecisionCertificateOfRotatingAccessState
    (noDirectEnrichedRotatingAccessStateSemanticsOfCoherentHistoryOfParityProgressCertificate
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      orderOfHistory
      automatonOfHistory
      parityProgress
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof)
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
Coherent enriched no-direct decidability from a named parity-progress
certificate.
-/
noncomputable def no_direct_from_enriched_coherent_history_access_state_of_parityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_finite_A_index
    uniform
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    (finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateOfParityProgressCertificate
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      orderOfHistory
      automatonOfHistory
      parityProgress
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      transitionRelationEffective
      transitionRelationEffective_proof
      finiteNonFringeSummariesHierarchical
      finiteNonFringeSummariesHierarchical_proof
      olderReceiptTagsRecoverable
      olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff)

/--
Coherent-subtype version of
`no_direct_from_enriched_history_access_state_with_current_receipt_order_hierarchy`.
-/
noncomputable def no_direct_from_enriched_coherent_history_access_state_with_current_receipt_order_hierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (sameParityOfProgress :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        parityOfHistory c.1.history = parityOfHistory c'.1.history ->
          sameParityOutcomes c.1 c'.1)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  let hierarchy :=
    currentReceiptOrderDataHierarchyCertificateOfPastReceipt
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  no_direct_from_enriched_coherent_history_access_state
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityOfHistory
    sameParityOfProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    hierarchy.accumulatedHistoriesHierarchical
    hierarchy.accumulatedHistoriesHierarchical_proof
    hierarchy.olderReceiptTagsRecoverable
    hierarchy.olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
Hierarchy-specialized coherent enriched no-direct decidability from a named
parity-progress certificate.

This is the decision-level landing zone for the coherent lambda route: the
receipt/order hierarchy inputs are discharged by the current proved hierarchy
certificate, while parity progress is supplied as one named certificate.
-/
noncomputable def no_direct_from_enriched_coherent_history_access_state_with_current_receipt_order_hierarchy_of_parityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_enriched_coherent_history_access_state_with_current_receipt_order_hierarchy
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityProgress.parityOfHistory
    parityProgress.sameParityOfProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteGame
    finiteGameRealizableIff

/--
Enriched no-direct decidability using the fully proved current receipt/order
epoch hierarchy.

This is the corrected proposition-facing endpoint for finite-index
side: it avoids the raw-state refinement certificate and discharges the
hierarchy/recoverability inputs with
`currentReceiptOrderDataHierarchyCertificateOfPastReceipt`.
-/
noncomputable def no_direct_from_enriched_history_access_state_with_current_receipt_order_hierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (configurationCoherent :
      ∀ c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState,
        ContinuationConfigurationAContinuationDataCoherent
          containmentOrder orderOfHistory automatonOfHistory c)
    (sameParityOfProgress :
      ∀ c c',
        parityOfHistory c.history = parityOfHistory c'.history ->
          sameParityOutcomes c c')
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  let hierarchy :=
    currentReceiptOrderDataHierarchyCertificateOfPastReceipt
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  no_direct_from_enriched_history_access_state
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityOfHistory
    configurationCoherent
    sameParityOfProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    hierarchy.accumulatedHistoriesHierarchical
    hierarchy.accumulatedHistoriesHierarchical_proof
    hierarchy.olderReceiptTagsRecoverable
    hierarchy.olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
No-direct decidability using the concrete history access-state map.  The only
semantic handoff left to the paper argument is the refinement theorem for this
specific map.
-/
noncomputable def no_direct_from_history_access_state
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (determinesReceiptAndOrder : Prop)
    (determinesReceiptAndOrder_proof : determinesReceiptAndOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (refinesAContinuation :
      ∀ c c',
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_rotating_access_state
    uniform
    (noDirectRotatingAccessStateSemanticsOfHistory
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      determinesReceiptAndOrder
      determinesReceiptAndOrder_proof
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      refinesAContinuation)
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
No-direct decidability from the concrete history access-state map, with the
receipt/order preservation side condition derived from the refinement theorem.
-/
noncomputable def no_direct_from_history_access_state_from_refinement
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (refinesAContinuation :
      ∀ c c',
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          uniform.noDirectEpochStateAfterHistory initialBoundary c'.history ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_rotating_access_state
    uniform
    (noDirectRotatingAccessStateSemanticsOfHistoryFromRefinement
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      refinesAContinuation)
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
No-direct decidability from the concrete history access-state map and the three
component congruence facts of the epoch-to-rotating proof.
-/
noncomputable def no_direct_from_history_access_state_components
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (determinesReceiptAndOrder : Prop)
    (determinesReceiptAndOrder_proof : determinesReceiptAndOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_rotating_access_state
    uniform
    (noDirectRotatingAccessStateSemanticsOfHistoryComponents
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      determinesReceiptAndOrder
      determinesReceiptAndOrder_proof
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      boundaryRefines
      sideOneRefines
      sideTwoRefines)
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
No-direct decidability from the three component congruence facts, deriving the
receipt/order preservation side condition from those same congruence facts.
-/
noncomputable def no_direct_from_history_access_state_components_from_refinement
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_rotating_access_state
    uniform
    (noDirectRotatingAccessStateSemanticsOfHistoryComponentsFromRefinement
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      boundaryRefines
      sideOneRefines
      sideTwoRefines)
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
No-direct decidability from component congruences and a typed epoch-summary
hierarchy certificate.  This is the route that makes the certificate input
explicitly be `prop:epochhierarchical`, instead of two anonymous
hierarchy/recoverability propositions.
-/
noncomputable def no_direct_from_history_access_state_components_with_epoch_hierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Summary₁ : Type p}
    {Summary₂ : Type q}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (hierarchy :
      EpochSummaryHierarchyCertificate.{p, q} Summary₁ Summary₂)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_history_access_state_components_from_refinement
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    boundaryRefines
    sideOneRefines
    sideTwoRefines
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    hierarchy.accumulatedHistoriesHierarchical
    hierarchy.accumulatedHistoriesHierarchical_proof
    hierarchy.olderReceiptTagsRecoverable
    hierarchy.olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
No-direct decidability from component congruences using the fully proved raw
epoch hierarchy certificate.

This specializes `no_direct_from_history_access_state_components_with_epoch_hierarchy`
to the summaries consisting of the current non-fringe view paired with the
current receipt tag.  The dynamic-hierarchy, older-own-receipt, and direct
reversal pending-counterpart readability obligations are discharged by
`currentReceiptOrderDataHierarchyCertificateOfPastReceipt`.
-/
noncomputable def no_direct_from_history_access_state_components_with_current_receipt_order_hierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (boundaryRefines :
      ∀ c c' boundary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inl boundary ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inl boundary ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideOneRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inl summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inl summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (sideTwoRefines :
      ∀ c c' summary,
        uniform.noDirectEpochStateAfterHistory initialBoundary c.history =
          Sum.inr (Sum.inr summary) ->
        uniform.noDirectEpochStateAfterHistory initialBoundary c'.history =
          Sum.inr (Sum.inr summary) ->
        AContinuationEquivalent sameParityOutcomes containmentOrder c c')
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_history_access_state_components_with_epoch_hierarchy
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    boundaryRefines
    sideOneRefines
    sideTwoRefines
    (currentReceiptOrderDataHierarchyCertificateOfPastReceipt
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteGame
    finiteGameRealizableIff

/--
No-direct decidability from a named component-refinement certificate, using the
fully proved current receipt/order epoch hierarchy.

This is the same theorem as
`no_direct_from_history_access_state_components_with_current_receipt_order_hierarchy`,
but with the three component congruences packaged as the single semantic
finite-retraction obligation that the paper has to construct.
-/
noncomputable def no_direct_from_history_access_state_component_refinement_with_current_receipt_order_hierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (refinement :
      NoDirectHistoryAccessStateComponentRefinement
        uniform initialBoundary sameParityOutcomes containmentOrder)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable :=
  no_direct_from_history_access_state_components_with_current_receipt_order_hierarchy
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    refinement.boundaryRefines
    refinement.sideOneRefines
    refinement.sideTwoRefines
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteGame
    finiteGameRealizableIff

/--
Build the no-direct finite-game certificate from the corrected enriched history
access-state map.

This is the certificate-producing version of
`no_direct_from_enriched_history_access_state`: the finite quotient stores the
raw no-direct state together with receipt/order data, automaton profile, and
parity progress.  Equality of the quotient refines `A`-continuation equivalence
via `noDirectEpochStateWithAContinuationData_refines_AContinuation_of_coherent`.
-/
noncomputable def noDirectReversalFragmentCertificateOfEnrichedHistoryAccessState
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (configurationCoherent :
      ∀ c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState,
        ContinuationConfigurationAContinuationDataCoherent
          containmentOrder orderOfHistory automatonOfHistory c)
    (sameParityOfProgress :
      ∀ c c',
        parityOfHistory c.history = parityOfHistory c'.history ->
          sameParityOutcomes c c')
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  noDirectReversalFragmentCertificateOfFiniteAIndex
    (Config :=
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
    (Realizable := Realizable)
    uniform
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    (finiteAIndexDecisionCertificateOfRotatingAccessState
      (Config :=
        ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState)
      (Realizable := Realizable)
      (noDirectEnrichedRotatingAccessStateSemanticsOfHistory
        uniform
        initialBoundary
        sameParityOutcomes
        containmentOrder
        orderOfHistory
        automatonOfHistory
        parityOfHistory
        configurationCoherent
        sameParityOfProgress
        updateClosed
        updateClosed_proof
        preservesDynamicHierarchy
        preservesDynamicHierarchy_proof)
      transitionRelationEffective
      transitionRelationEffective_proof
      finiteNonFringeSummariesHierarchical
      finiteNonFringeSummariesHierarchical_proof
      olderReceiptTagsRecoverable
      olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff)

/--
Certificate-producing no-direct route from the enriched quotient over coherent
continuation configurations.

This is the theorem-facing counterpart of
`no_direct_from_enriched_coherent_history_access_state`: coherence is part of the
configuration carrier, so the remaining parity-progress soundness hypothesis is
only required on coherent configurations.
-/
noncomputable def noDirectReversalFragmentCertificateOfEnrichedCoherentHistoryAccessState
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (sameParityOfProgress :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        parityOfHistory c.1.history = parityOfHistory c'.1.history ->
          sameParityOutcomes c.1 c'.1)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  noDirectReversalFragmentCertificateOfFiniteAIndex
    (Config :=
      CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory)
    (Realizable := Realizable)
    uniform
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    (finiteAIndexDecisionCertificateOfRotatingAccessState
      (Config :=
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory)
      (Realizable := Realizable)
      (noDirectEnrichedRotatingAccessStateSemanticsOfCoherentHistory
        uniform
        initialBoundary
        sameParityOutcomes
        containmentOrder
        orderOfHistory
        automatonOfHistory
        parityOfHistory
        sameParityOfProgress
        updateClosed
        updateClosed_proof
        preservesDynamicHierarchy
        preservesDynamicHierarchy_proof)
      transitionRelationEffective
      transitionRelationEffective_proof
      finiteNonFringeSummariesHierarchical
      finiteNonFringeSummariesHierarchical_proof
      olderReceiptTagsRecoverable
      olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff)

/--
Certificate-producing coherent enriched no-direct route from a named
parity-progress certificate.

This is the certificate-level counterpart of
`no_direct_from_enriched_coherent_history_access_state_of_parityProgressCertificate`.
-/
noncomputable def noDirectReversalFragmentCertificateOfEnrichedCoherentHistoryAccessStateOfParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  noDirectReversalFragmentCertificateOfEnrichedCoherentHistoryAccessState
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityProgress.parityOfHistory
    parityProgress.sameParityOfProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteNonFringeSummariesHierarchical
    finiteNonFringeSummariesHierarchical_proof
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
Certificate-producing enriched no-direct route using the fully proved current
receipt/order epoch hierarchy.

This is the corrected certificate landing zone for the finite-retraction side of
finite-game compilation: the inputs are the concrete enriched-state coherence,
parity-progress soundness, update/effectiveness/fringe clauses, and the finite
game realizability equivalence.
-/
noncomputable def noDirectReversalFragmentCertificateOfEnrichedHistoryAccessStateWithCurrentReceiptOrderHierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (configurationCoherent :
      ∀ c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState,
        ContinuationConfigurationAContinuationDataCoherent
          containmentOrder orderOfHistory automatonOfHistory c)
    (sameParityOfProgress :
      ∀ c c',
        parityOfHistory c.history = parityOfHistory c'.history ->
          sameParityOutcomes c c')
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  let hierarchy :=
    currentReceiptOrderDataHierarchyCertificateOfPastReceipt
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  noDirectReversalFragmentCertificateOfEnrichedHistoryAccessState
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityOfHistory
    configurationCoherent
    sameParityOfProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    hierarchy.accumulatedHistoriesHierarchical
    hierarchy.accumulatedHistoriesHierarchical_proof
    hierarchy.olderReceiptTagsRecoverable
    hierarchy.olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff

/--
Hierarchy-specialized coherent-subtype no-direct certificate constructor.

This is the current cleanest finite-retraction certificate surface: the carrier
is the coherent subtype and the already-proved receipt/order hierarchy
certificate discharges the finite non-fringe hierarchy and older receipt
recovery inputs.
-/
noncomputable def noDirectReversalFragmentCertificateOfEnrichedCoherentHistoryAccessStateWithCurrentReceiptOrderHierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {ParityProgress : Type (max u v w x y z)}
    [Fintype AState]
    [Fintype ParityProgress]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> ParityProgress)
    (sameParityOfProgress :
      ∀ c c' :
        CoherentContinuationConfiguration
          containmentOrder orderOfHistory automatonOfHistory,
        parityOfHistory c.1.history = parityOfHistory c'.1.history ->
          sameParityOutcomes c.1 c'.1)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  let hierarchy :=
    currentReceiptOrderDataHierarchyCertificateOfPastReceipt
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  noDirectReversalFragmentCertificateOfEnrichedCoherentHistoryAccessState
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityOfHistory
    sameParityOfProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    hierarchy.accumulatedHistoriesHierarchical
    hierarchy.accumulatedHistoriesHierarchical_proof
    hierarchy.olderReceiptTagsRecoverable
    hierarchy.olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
Finite `A`-index handoff specialized to an explicit epoch-summary hierarchy
certificate and a named parity-progress certificate.

This is the finite-index layer used by the generic Step 4 no-direct constructor:
the hierarchy certificate supplies the finite non-fringe hierarchy and older
receipt recovery fields, while the parity-progress certificate supplies the
coherent enriched quotient.
-/
noncomputable def finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateWithEpochHierarchyOfParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {Summary₁ : Type p}
    {Summary₂ : Type q}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (hierarchy :
      EpochSummaryHierarchyCertificate.{p, q} Summary₁ Summary₂)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    FiniteAIndexDecisionCertificate.{max u v w x y z,
      max u v w x y z, max u v w x y z, max u v w x y z}
      (CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory)
      Realizable :=
  finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateOfParityProgressCertificate
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityProgress
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    hierarchy.accumulatedHistoriesHierarchical
    hierarchy.accumulatedHistoriesHierarchical_proof
    hierarchy.olderReceiptTagsRecoverable
    hierarchy.olderReceiptTagsRecoverable_proof
    finiteGame
    finiteGameRealizableIff

/--
Hierarchy-certificate-specialized coherent-subtype no-direct constructor from a
named parity-progress certificate.

This is the generic Step 4 bridge: any concrete finite-summary proof packaged
as `EpochSummaryHierarchyCertificate` supplies the finite non-fringe hierarchy
and older-receipt recovery inputs required by the no-direct reversal
certificate.
-/
noncomputable def noDirectReversalFragmentCertificateOfEnrichedCoherentHistoryAccessStateWithEpochHierarchyOfParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    {Summary₁ : Type p}
    {Summary₂ : Type q}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (hierarchy :
      EpochSummaryHierarchyCertificate.{p, q} Summary₁ Summary₂)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  noDirectReversalFragmentCertificateOfFiniteAIndex
    uniform
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    (finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateWithEpochHierarchyOfParityProgressCertificate
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      orderOfHistory
      automatonOfHistory
      parityProgress
      hierarchy
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      transitionRelationEffective
      transitionRelationEffective_proof
      finiteGame
      finiteGameRealizableIff)

/--
Finite `A`-index handoff specialized to the already proved current
receipt/order hierarchy and a named parity-progress certificate.

Use this for the current-receipt/order route when the proof needs the
`FiniteAIndexDecisionCertificate` itself before building the no-direct fragment
certificate.
-/
noncomputable def finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateWithCurrentReceiptOrderHierarchyOfParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    FiniteAIndexDecisionCertificate.{max u v w x y z,
      max u v w x y z, max u v w x y z, max u v w x y z}
      (CoherentContinuationConfiguration
        containmentOrder orderOfHistory automatonOfHistory)
      Realizable :=
  let hierarchy :=
    currentReceiptOrderDataHierarchyCertificateOfPastReceipt
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateWithEpochHierarchyOfParityProgressCertificate
    uniform
    initialBoundary
    sameParityOutcomes
    containmentOrder
    orderOfHistory
    automatonOfHistory
    parityProgress
    hierarchy
    updateClosed
    updateClosed_proof
    preservesDynamicHierarchy
    preservesDynamicHierarchy_proof
    transitionRelationEffective
    transitionRelationEffective_proof
    finiteGame
    finiteGameRealizableIff

/--
Hierarchy-specialized coherent-subtype no-direct certificate constructor from a
named parity-progress certificate.

This is the theorem-facing finite-game compilation surface after the coherent retraction: the
current receipt/order hierarchy is already supplied, and the remaining
paper-facing payload is the finite parity-progress certificate.
-/
noncomputable def noDirectReversalFragmentCertificateOfEnrichedCoherentHistoryAccessStateWithCurrentReceiptOrderHierarchyOfParityProgressCertificate
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type (max u v w x y z)}
    [Fintype AState]
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (orderOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> NonFringeContainmentOrder)
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState)
    (parityProgress :
      NoDirectCoherentParityProgressCertificate.{u, v, w, x, y, z}
        sameParityOutcomes containmentOrder orderOfHistory automatonOfHistory)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  noDirectReversalFragmentCertificateOfFiniteAIndex
    uniform
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    (finiteAIndexDecisionCertificateOfEnrichedCoherentHistoryAccessStateWithCurrentReceiptOrderHierarchyOfParityProgressCertificate
      uniform
      initialBoundary
      sameParityOutcomes
      containmentOrder
      orderOfHistory
      automatonOfHistory
      parityProgress
      updateClosed
      updateClosed_proof
      preservesDynamicHierarchy
      preservesDynamicHierarchy_proof
      transitionRelationEffective
      transitionRelationEffective_proof
      finiteGame
      finiteGameRealizableIff)

/--
Build the no-direct finite-game certificate from the named component-refinement
certificate, using the fully proved current receipt/order epoch hierarchy.

This is the certificate-producing version of
`no_direct_from_history_access_state_component_refinement_with_current_receipt_order_hierarchy`.
It is the artifact needed by theorem-facing compiler routes: the component
refinement supplies the rotating access-state semantics; the current
receipt/order hierarchy supplies the finite non-fringe hierarchy and older
receipt recovery fields; the remaining arguments are the effective finite-game
bridge clauses and the finite-game realizability equivalence.
-/
noncomputable def noDirectReversalFragmentCertificateOfHistoryAccessStateComponentRefinementWithCurrentReceiptOrderHierarchy
    {Alphabet : Type u}
    {In₁ : Type v} {In₂ : Type w} {Out₁ : Type x} {Out₂ : Type y}
    {AState : Type a}
    {Realizable : Prop}
    (uniform :
      UniformOneDirectionalFiniteIndexLemma.{u, v, w, x, y, z}
        Alphabet In₁ In₂ Out₁ Out₂)
    (initialBoundary : uniform.boundary)
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState ->
      NonFringeContainmentOrder)
    (updateClosed : Prop)
    (updateClosed_proof : updateClosed)
    (preservesDynamicHierarchy : Prop)
    (preservesDynamicHierarchy_proof : preservesDynamicHierarchy)
    (refinement :
      NoDirectHistoryAccessStateComponentRefinement
        uniform initialBoundary sameParityOutcomes containmentOrder)
    (finiteFringeCompilation : Prop)
    (finiteFringeCompilation_proof : finiteFringeCompilation)
    (boundaryAndBlockTransitionsEffective : Prop)
    (boundaryAndBlockTransitionsEffective_proof :
      boundaryAndBlockTransitionsEffective)
    (continuationPreservedBlockByBlock : Prop)
    (continuationPreservedBlockByBlock_proof :
      continuationPreservedBlockByBlock)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteGame :
      FiniteDynamicHierarchyParityGame.{max u v w x y z,
        max u v w x y z})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    NoDirectReversalFragmentCertificate Alphabet In₁ In₂ Out₁ Out₂ :=
  let hierarchy :=
    currentReceiptOrderDataHierarchyCertificateOfPastReceipt
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  noDirectReversalFragmentCertificateOfFiniteAIndex
    uniform
    finiteFringeCompilation
    finiteFringeCompilation_proof
    boundaryAndBlockTransitionsEffective
    boundaryAndBlockTransitionsEffective_proof
    continuationPreservedBlockByBlock
    continuationPreservedBlockByBlock_proof
    (finiteAIndexDecisionCertificateOfRotatingAccessState
      (refinement.toRotatingAccessStateSemantics
        updateClosed
        updateClosed_proof
        preservesDynamicHierarchy
        preservesDynamicHierarchy_proof)
      transitionRelationEffective
      transitionRelationEffective_proof
      hierarchy.accumulatedHistoriesHierarchical
      hierarchy.accumulatedHistoriesHierarchical_proof
      hierarchy.olderReceiptTagsRecoverable
      hierarchy.olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff)

end DistributedSynthesis
