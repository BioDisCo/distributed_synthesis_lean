/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedConcreteEpochAdapter

/-!
# The concrete streaming projection of the witnessed physical query

The recut phase retains all lineage choices.  A deterministic global proof
machine may follow the fixed canonical lineage `default`; no local process is
given that lineage.  This file stores the resulting two finite direction
controls in the direction tag already present in the reachable query.

Strict rounds update only the appropriate direction control.  A closing
`both` round installs canonical row-pivots and the actual closing inputs, and
uses the proof-side recut tier only to select the old query's pointed side.
That side is not part of either local controller.

The construction is finite and total.  The final invariant identifies its
closing tag with `profiledOpenPhysicalStrictAccumulatorRun` on the canonical
lineage history, which discharges the former `completedQuery_eq` field.
-/

namespace DistributedSynthesis

universe i u v x y s c₁ c₂

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ treeState : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A treeState).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (semanticState : ProfiledOpenIndexedOptionalControlledSemanticState A
    strategy hwin basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A policy)
variable
  (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
    strategy hwin basis initialCode policy semanticState initialRoot)

private abbrev StreamingQuery :=
  ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
    max i u v x y s, max i u v x y s} A initialCode

private abbrev StreamingBranch :=
  ProfiledOpenWitnessedDistinguishedState A strategy hwin basis initialCode
    policy semanticState initialRoot package

private abbrev StreamingBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev StreamingState
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂) :=
  FiniteEpochPhysicalState
    (StreamingBranch A strategy hwin basis initialCode policy semanticState
      initialRoot package)
    (StreamingBank A initialCode) (StreamingQuery A initialCode)
    (ProfiledOpenPhysicalRecutPhase A) controller

/-! ## Canonical proof-side lineage history -/

/-- Replace only the proof-side lineage coordinate.  The physical round is
unchanged definitionally. -/
def ProfiledOpenPhysicalStrictLetter.canonicalizeLineage
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :
    ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂) :=
  { side := letter.side
    lineage := default
    inputOne := letter.inputOne
    inputTwo := letter.inputTwo }

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem ProfiledOpenPhysicalStrictLetter.canonicalizeLineage_round
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :
    letter.canonicalizeLineage.round = letter.round := by
  cases letter
  rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem ProfiledOpenPhysicalStrictLetter.canonicalizeLineage_idem
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :
    letter.canonicalizeLineage.canonicalizeLineage =
      letter.canonicalizeLineage := by
  cases letter
  rfl

def profiledOpenPhysicalCanonicalLineageHistory
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :=
  history.map ProfiledOpenPhysicalStrictLetter.canonicalizeLineage

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledOpenPhysicalCanonicalLineageHistory_idem
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    profiledOpenPhysicalCanonicalLineageHistory
        (profiledOpenPhysicalCanonicalLineageHistory history) =
      profiledOpenPhysicalCanonicalLineageHistory history := by
  induction history with
  | nil => rfl
  | cons letter history ih =>
      simp only [profiledOpenPhysicalCanonicalLineageHistory, List.map_cons,
        ProfiledOpenPhysicalStrictLetter.canonicalizeLineage_idem]
      exact congrArg (List.cons letter.canonicalizeLineage) ih

/-! ## Streaming the direction tag already carried by the query -/

/-- Forget the boundary fields of a finite direction summary and recover its
two-lane accumulator. -/
noncomputable def profiledOpenWitnessedAccumulatorOfDirectionTag
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedDirectionAccumulator A tag.1 :=
  ⟨tag.2.rightControl, tag.2.leftControl⟩

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
@[simp] theorem profiledOpenWitnessedAccumulatorOfDirectionTag_finish
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (accumulator : ProfiledOpenIndexedDirectionAccumulator A move)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (rightInput : In₂ × In₁) (leftInput : In₁ × In₂) :
    profiledOpenWitnessedAccumulatorOfDirectionTag A
        ⟨move, accumulator.finish A rightPivot rightInput leftPivot
          leftInput⟩ =
      accumulator := by
  cases accumulator
  rfl

/-- Advance a carried query through one strict letter, using the canonical
proof-side lineage.  Its reachable controller-query bank is retained
definitionally. -/
noncomputable def profiledOpenWitnessedStreamingStrictQueryStep
    (query : StreamingQuery A initialCode)
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) : StreamingQuery A initialCode :=
  let tag := query.1.2
  let accumulator := profiledOpenWitnessedAccumulatorOfDirectionTag A tag
  let canonical := letter.canonicalizeLineage
  let next := profiledOpenPhysicalStrictAccumulatorStep A initialCode tag.1
    accumulator canonical
  profiledOpenWitnessedTableQueryWithDirection A initialCode query
    query.1.1.1
    ⟨tag.1, next.finish A tag.2.rightPivot tag.2.rightInput
      tag.2.leftPivot tag.2.leftInput⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Canonicalizing twice has no further effect on the streaming query.  This
is the small extensional bridge between physical strict letters (whose
lineage is irrelevant to the physical round) and the canonical proof-side
lineage consumed by the query accumulator. -/
@[simp] theorem profiledOpenWitnessedStreamingStrictQueryStep_canonicalize
    (query : StreamingQuery A initialCode)
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂)) :
    profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
        letter.canonicalizeLineage =
      profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
        letter := by
  cases letter
  rfl

/-- Pure query scan through a strict physical history. -/
noncomputable def profiledOpenWitnessedStreamingStrictQueryRunFrom :
    StreamingQuery A initialCode →
      List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
        (In₂ := In₂)) → StreamingQuery A initialCode
  | query, [] => query
  | query, letter :: history =>
      profiledOpenWitnessedStreamingStrictQueryRunFrom
        (profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
          letter) history

/-- Finish the carried accumulator on a simultaneous close.  Pivots retain
both row alternatives in the surrounding recut set; this deterministic
distinguished member uses the canonical `.first` pivot. -/
noncomputable def profiledOpenWitnessedStreamingClosingQuery
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (query : StreamingQuery A initialCode)
    (inputOne : In₁) (inputTwo : In₂) : StreamingQuery A initialCode :=
  let tag := query.1.2
  let accumulator := profiledOpenWitnessedAccumulatorOfDirectionTag A tag
  let pivot : IndexedLineageCandidate I := (default, .first)
  let side := phase.tier.activeSide.getD .right
  profiledOpenWitnessedTableQueryWithDirection A initialCode query side
    ⟨tag.1, accumulator.finish A pivot (inputTwo, inputOne)
      pivot (inputOne, inputTwo)⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Closing an initialized streaming tag is exactly the extensional direction
summary of its strict history. -/
theorem profiledOpenWitnessedStreamingClosingQuery_eq_summary
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (query : StreamingQuery A initialCode)
    (inputOne : In₁) (inputTwo : In₂)
    (htag : query.1.2 =
      let pivot : IndexedLineageCandidate I := (default, .first)
      ⟨move,
        (profiledOpenPhysicalStrictAccumulatorRun A initialCode move history
          ).finish A pivot (default, default) pivot (default, default)⟩) :
    let pivot : IndexedLineageCandidate I := (default, .first)
    let side := phase.tier.activeSide.getD .right
    profiledOpenWitnessedStreamingClosingQuery A initialCode phase query
        inputOne inputTwo =
      profiledOpenWitnessedTableQueryWithDirection A initialCode query side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          (profiledOpenPhysicalStrictHistoryDirection history pivot pivot
            inputOne inputTwo)⟩ := by
  dsimp only
  unfold profiledOpenWitnessedStreamingClosingQuery
  rw [htag]
  simp only [profiledOpenWitnessedAccumulatorOfDirectionTag_finish]
  rw [← profiledOpenPhysicalStrictAccumulatorRun_finish_eq_summary
    A initialCode move history (default, .first) (default, .first) inputOne
      inputTwo]
  rfl

/-- Total concrete query accumulator.  Strict rounds stream; `both` closes.
All branch, bank, receipt, and controller arguments are deliberately ignored:
the finite data needed here is already the query and the proof-side phase. -/
noncomputable def profiledOpenWitnessedStreamingQueryAccumulator
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂) :
    ProfiledOpenWitnessedQueryAccumulator A strategy hwin basis initialCode
      policy semanticState initialRoot package controller where
  accumulate := fun _ _ phase _ _ query _ _ round _ _ =>
    match hgraph : round.graph with
    | .right =>
        profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
          { side := .right
            lineage := default
            inputOne := round.inputOne
            inputTwo := round.inputTwo }
    | .left =>
        profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
          { side := .left
            lineage := default
            inputOne := round.inputOne
            inputTwo := round.inputTwo }
    | .both =>
        profiledOpenWitnessedStreamingClosingQuery A initialCode phase query
          round.inputOne round.inputTwo

/-- Concrete adapter specialized to the streaming query projection. -/
noncomputable def profiledOpenWitnessedStreamingEpochAdapter
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂) :
    FiniteEpochQueryAdapter In₁ In₂
      (StreamingBranch A strategy hwin basis initialCode policy semanticState
        initialRoot package)
      (StreamingBank A initialCode) (StreamingQuery A initialCode)
      (ProfiledOpenPhysicalRecutPhase A) controller :=
  profiledOpenWitnessedConcreteEpochAdapter A strategy hwin basis initialCode
    policy semanticState initialRoot package controller
    (profiledOpenWitnessedStreamingQueryAccumulator A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)

/-- On a simultaneous physical round, the adapter's literal completed query
is the summary of whichever canonical strict history its current tag records.
This theorem contains the only unfolding of the controller-facing adapter. -/
theorem profiledOpenWitnessedStreaming_completedQuery_eq_summary
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (physicalState : StreamingState A strategy hwin basis initialCode policy
      semanticState initialRoot package controller)
    (closingRound : EnvironmentRound In₁ In₂)
    (hboth : closingRound.graph = .both)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (htag : physicalState.query.1.2 =
      let pivot : IndexedLineageCandidate I := (default, .first)
      ⟨move,
        (profiledOpenPhysicalStrictAccumulatorRun A initialCode move history
          ).finish A pivot (default, default) pivot (default, default)⟩) :
    let pivot : IndexedLineageCandidate I := (default, .first)
    let side := physicalState.phase.tier.activeSide.getD .right
    physicalState.completedQuery controller
        (profiledOpenWitnessedStreamingEpochAdapter A strategy hwin basis
          initialCode policy semanticState initialRoot package controller)
        closingRound =
      profiledOpenWitnessedTableQueryWithDirection A initialCode
        physicalState.query side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          (profiledOpenPhysicalStrictHistoryDirection history pivot pivot
            closingRound.inputOne closingRound.inputTwo)⟩ := by
  rcases closingRound with ⟨inputOne, inputTwo, graph⟩
  dsimp only at hboth ⊢
  subst graph
  change profiledOpenWitnessedStreamingClosingQuery A initialCode
      physicalState.phase physicalState.query inputOne inputTwo = _
  exact profiledOpenWitnessedStreamingClosingQuery_eq_summary A initialCode
    move history physicalState.phase physicalState.query inputOne inputTwo htag

/-! ## Exact pure-query invariant -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Streaming preserves a supplied move and boundary shell while advancing
exactly the two-lane accumulator on the canonical lineage history. -/
theorem profiledOpenWitnessedStreamingStrictQueryRunFrom_tag
    (query : StreamingQuery A initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (accumulator : ProfiledOpenIndexedDirectionAccumulator A move)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (rightInput : In₂ × In₁) (leftInput : In₁ × In₂)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (htag : query.1.2 =
      ⟨move, accumulator.finish A rightPivot rightInput leftPivot
        leftInput⟩) :
    (profiledOpenWitnessedStreamingStrictQueryRunFrom A initialCode query
      history).1.2 =
      ⟨move,
        (profiledOpenPhysicalStrictAccumulatorRunFrom A initialCode move
          accumulator
          (profiledOpenPhysicalCanonicalLineageHistory history)).finish A
            rightPivot rightInput leftPivot leftInput⟩ := by
  induction history generalizing query accumulator with
  | nil => exact htag
  | cons letter history ih =>
      let canonical := letter.canonicalizeLineage
      let next := profiledOpenPhysicalStrictAccumulatorStep A initialCode move
        accumulator canonical
      have hstep :
          (profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
            letter).1.2 =
            ⟨move, next.finish A rightPivot rightInput leftPivot leftInput⟩ := by
        simp only [profiledOpenWitnessedStreamingStrictQueryStep,
          profiledOpenWitnessedTableQueryWithDirection_tag]
        rw [htag]
        rfl
      have htail := ih
        (profiledOpenWitnessedStreamingStrictQueryStep A initialCode query
          letter) next hstep
      simpa only [profiledOpenWitnessedStreamingStrictQueryRunFrom,
        profiledOpenPhysicalCanonicalLineageHistory, List.map_cons,
        profiledOpenPhysicalStrictAccumulatorRunFrom, canonical, next] using
        htail

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Initialization specializes the invariant to the empty accumulator at the
supplied move. -/
theorem profiledOpenWitnessedStreamingStrictQueryRunFrom_initial_tag
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    (profiledOpenWitnessedStreamingStrictQueryRunFrom A initialCode
      (profiledOpenWitnessedInitialQueryForMove A initialCode move)
      history).1.2 =
      let pivot : IndexedLineageCandidate I := (default, .first)
      ⟨move,
        (profiledOpenPhysicalStrictAccumulatorRun A initialCode move
          (profiledOpenPhysicalCanonicalLineageHistory history)).finish A
            pivot (default, default) pivot (default, default)⟩ := by
  let pivot : IndexedLineageCandidate I := (default, .first)
  apply profiledOpenWitnessedStreamingStrictQueryRunFrom_tag A initialCode
    (profiledOpenWitnessedInitialQueryForMove A initialCode move) move
    (profiledOpenIndexedDirectionAccumulatorInitial A move) pivot pivot
    (default, default) (default, default) history
  rfl

/-! ## The physical-state query invariant -/

/-- The query coordinate of the concrete physical state follows exactly the
pure streaming scan through every strict history. -/
theorem profiledOpenWitnessedPhysicalStrictStateRunFrom_streaming_query
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (physicalState : StreamingState A strategy hwin basis initialCode policy
      semanticState initialRoot package controller)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    (profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      (profiledOpenWitnessedStreamingQueryAccumulator A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      physicalState history).query =
      profiledOpenWitnessedStreamingStrictQueryRunFrom A initialCode
        physicalState.query history := by
  induction history generalizing physicalState with
  | nil => rfl
  | cons letter history ih =>
      let accumulator := profiledOpenWitnessedStreamingQueryAccumulator A
        strategy hwin basis initialCode policy semanticState initialRoot package
        controller
      let adapter := profiledOpenWitnessedStreamingEpochAdapter A strategy hwin
        basis initialCode policy semanticState initialRoot package controller
      let label := profiledOpenWitnessedDistinguishedLabel A strategy hwin basis
        initialCode policy semanticState initialRoot package
      let branchStep := profiledOpenWitnessedDistinguishedBranchStep A strategy
        hwin basis initialCode policy semanticState initialRoot package
      let next := physicalState.step controller adapter label branchStep
        letter.round
      have hclose :
          profiledOpenPhysicalClosesEpoch letter.round.graph = false := by
        cases hside : letter.side <;>
          simp [ProfiledOpenPhysicalStrictLetter.round, hside]
      have hnext : next.query =
          profiledOpenWitnessedStreamingStrictQueryStep A initialCode
            physicalState.query letter := by
        rw [show next.query =
          physicalState.completedQuery controller adapter letter.round by
            exact FiniteEpochPhysicalState.step_query_of_not_closes controller
              adapter label branchStep physicalState letter.round hclose]
        cases hside : letter.side <;>
          simp only [FiniteEpochPhysicalState.completedQuery, adapter,
            profiledOpenWitnessedStreamingEpochAdapter,
            profiledOpenWitnessedConcreteEpochAdapter,
            profiledOpenWitnessedStreamingQueryAccumulator,
            ProfiledOpenPhysicalStrictLetter.round, hside]
        · simpa only [ProfiledOpenPhysicalStrictLetter.canonicalizeLineage,
              hside] using
            (profiledOpenWitnessedStreamingStrictQueryStep_canonicalize
              A initialCode physicalState.query letter)
        · simpa only [ProfiledOpenPhysicalStrictLetter.canonicalizeLineage,
              hside] using
            (profiledOpenWitnessedStreamingStrictQueryStep_canonicalize
              A initialCode physicalState.query letter)
      change
        (profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
          initialCode policy semanticState initialRoot package controller
          accumulator next history).query = _
      rw [ih, hnext]
      rfl

/-- If an epoch starts at the adapter's branch-indexed empty query, then the
physical query after any strict history carries exactly the canonical
proof-side accumulator for that branch's old move. -/
theorem profiledOpenWitnessedPhysicalStrictStateRunFrom_streaming_initial_tag
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (epochStart : StreamingState A strategy hwin basis initialCode policy
      semanticState initialRoot package controller)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (hquery : epochStart.query =
      profiledOpenWitnessedInitialQueryForBranch A strategy hwin basis
        initialCode policy semanticState initialRoot package
        epochStart.branch) :
    let move := profiledOpenWitnessedDistinguishedMove A strategy hwin basis
      initialCode policy semanticState initialRoot package epochStart.branch
    let pivot : IndexedLineageCandidate I := (default, .first)
    (profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      (profiledOpenWitnessedStreamingQueryAccumulator A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      epochStart history).query.1.2 =
      ⟨move,
        (profiledOpenPhysicalStrictAccumulatorRun A initialCode move
          (profiledOpenPhysicalCanonicalLineageHistory history)).finish A
            pivot (default, default) pivot (default, default)⟩ := by
  dsimp only
  rw [profiledOpenWitnessedPhysicalStrictStateRunFrom_streaming_query]
  rw [hquery]
  exact profiledOpenWitnessedStreamingStrictQueryRunFrom_initial_tag
    A initialCode
      (profiledOpenWitnessedDistinguishedMove A strategy hwin basis
        initialCode policy semanticState initialRoot package epochStart.branch)
      history

/-! ## Unconditional closing projection -/

/-- The concrete streaming accumulator supplies the
`completedQuery_eq` field.

The returned proof history is the canonical-lineage copy of the supplied
strict history.  It describes exactly the same physical rounds, because the
physical transition never reads the proof-side lineage coordinate.  Thus the
construction neither detects a strict leader nor sends an orientation bit to
either local process. -/
noncomputable def profiledOpenWitnessedStreamingStrictRunClosingProjection
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (epochStart : StreamingState A strategy hwin basis initialCode policy
      semanticState initialRoot package controller)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (closingRound : EnvironmentRound In₁ In₂)
    (hboth : closingRound.graph = .both)
    (hphase : epochStart.phase =
      profiledOpenPhysicalRecutPhaseInitial A Finset.univ)
    (hquery : epochStart.query =
      profiledOpenWitnessedInitialQueryForBranch A strategy hwin basis
        initialCode policy semanticState initialRoot package
        epochStart.branch) :
    ProfiledOpenWitnessedStrictRunClosingProjection A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      (profiledOpenWitnessedStreamingQueryAccumulator A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      epochStart (profiledOpenPhysicalCanonicalLineageHistory history)
      closingRound := by
  let canonicalHistory := profiledOpenPhysicalCanonicalLineageHistory history
  let accumulator := profiledOpenWitnessedStreamingQueryAccumulator A strategy
    hwin basis initialCode policy semanticState initialRoot package controller
  let physicalState :=
    profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      accumulator epochStart canonicalHistory
  let move := profiledOpenWitnessedDistinguishedMove A strategy hwin basis
    initialCode policy semanticState initialRoot package epochStart.branch
  let pivot : IndexedLineageCandidate I := (default, .first)
  let side := physicalState.phase.tier.activeSide.getD .right
  have htagRaw :=
    profiledOpenWitnessedPhysicalStrictStateRunFrom_streaming_initial_tag
      A strategy hwin basis initialCode policy semanticState initialRoot package
      controller epochStart canonicalHistory hquery
  have htag : physicalState.query.1.2 =
      ⟨move,
        (profiledOpenPhysicalStrictAccumulatorRun A initialCode move
          canonicalHistory).finish A pivot (default, default) pivot
            (default, default)⟩ := by
    simpa only [profiledOpenPhysicalCanonicalLineageHistory_idem,
      canonicalHistory, physicalState, move, pivot, accumulator] using htagRaw
  refine
    { graph_eq := hboth
      epochStart_phase_eq := hphase
      move := move
      carriedQuery := physicalState.query
      side := side
      rightPivot := pivot
      leftPivot := pivot
      completedQuery_eq := ?_ }
  dsimp only
  exact profiledOpenWitnessedStreaming_completedQuery_eq_summary A strategy
    hwin basis initialCode policy semanticState initialRoot package controller
    physicalState closingRound hboth move canonicalHistory htag

/-! ## Epoch-start invariants are automatic -/

/-- The finite global machine using the concrete streaming query adapter. -/
noncomputable def profiledOpenWitnessedStreamingPhysicalMachine
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂) :
    FiniteGlobalRoundMachine In₁ In₂ :=
  finiteEpochPhysicalGlobalMachine controller
    (profiledOpenWitnessedStreamingEpochAdapter A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (profiledOpenWitnessedDistinguishedInitial A strategy hwin basis
      initialCode policy semanticState initialRoot package)
    (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis initialCode
      policy semanticState initialRoot package)
    (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
      initialCode policy semanticState initialRoot package)

/-- The machine's literal initial state has exactly the phase and query
expected by the closing projection. -/
theorem profiledOpenWitnessedStreamingPhysicalMachine_initial_epochStart
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂) :
    let epochStart :=
      (profiledOpenWitnessedStreamingPhysicalMachine A strategy hwin basis
        initialCode policy semanticState initialRoot package controller).initial
    epochStart.phase =
        profiledOpenPhysicalRecutPhaseInitial A Finset.univ ∧
      epochStart.query =
        profiledOpenWitnessedInitialQueryForBranch A strategy hwin basis
          initialCode policy semanticState initialRoot package
          epochStart.branch := by
  exact ⟨rfl, rfl⟩

/-- Every simultaneous round resets both epoch-start invariants, regardless
of the preceding state and controller controls. -/
theorem profiledOpenWitnessedStreaming_step_epochStart
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (physicalState : StreamingState A strategy hwin basis initialCode policy
      semanticState initialRoot package controller)
    (closingRound : EnvironmentRound In₁ In₂)
    (hboth : closingRound.graph = .both) :
    let next := physicalState.step controller
      (profiledOpenWitnessedStreamingEpochAdapter A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis
        initialCode policy semanticState initialRoot package)
      (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
        initialCode policy semanticState initialRoot package)
      closingRound
    next.phase = profiledOpenPhysicalRecutPhaseInitial A Finset.univ ∧
      next.query =
        profiledOpenWitnessedInitialQueryForBranch A strategy hwin basis
          initialCode policy semanticState initialRoot package next.branch := by
  rcases closingRound with ⟨inputOne, inputTwo, graph⟩
  dsimp only at hboth ⊢
  subst graph
  exact ⟨rfl, rfl⟩

/-- In particular, the very first open epoch has an unconditional closing
projection for every strict physical history and every simultaneous close. -/
noncomputable def
    profiledOpenWitnessedStreamingInitialStrictRunClosingProjection
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (closingRound : EnvironmentRound In₁ In₂)
    (hboth : closingRound.graph = .both) :
    let epochStart :=
      (profiledOpenWitnessedStreamingPhysicalMachine A strategy hwin basis
        initialCode policy semanticState initialRoot package controller).initial
    ProfiledOpenWitnessedStrictRunClosingProjection A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      (profiledOpenWitnessedStreamingQueryAccumulator A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      epochStart (profiledOpenPhysicalCanonicalLineageHistory history)
      closingRound := by
  let epochStart :=
    (profiledOpenWitnessedStreamingPhysicalMachine A strategy hwin basis
      initialCode policy semanticState initialRoot package controller).initial
  have hstart :=
    profiledOpenWitnessedStreamingPhysicalMachine_initial_epochStart A strategy
      hwin basis initialCode policy semanticState initialRoot package controller
  exact profiledOpenWitnessedStreamingStrictRunClosingProjection A strategy
    hwin basis initialCode policy semanticState initialRoot package controller
    epochStart history closingRound hboth hstart.1 hstart.2

/-- The same projection is automatic after every earlier simultaneous
boundary.  This is the induction step needed to cover all epochs, not merely
the initial one. -/
noncomputable def
    profiledOpenWitnessedStreamingAfterClosingStrictRunClosingProjection
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (physicalState : StreamingState A strategy hwin basis initialCode policy
      semanticState initialRoot package controller)
    (previousClosingRound : EnvironmentRound In₁ In₂)
    (hprevious : previousClosingRound.graph = .both)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (closingRound : EnvironmentRound In₁ In₂)
    (hboth : closingRound.graph = .both) :
    let epochStart := physicalState.step controller
      (profiledOpenWitnessedStreamingEpochAdapter A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis
        initialCode policy semanticState initialRoot package)
      (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
        initialCode policy semanticState initialRoot package)
      previousClosingRound
    ProfiledOpenWitnessedStrictRunClosingProjection A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      (profiledOpenWitnessedStreamingQueryAccumulator A strategy hwin basis
        initialCode policy semanticState initialRoot package controller)
      epochStart (profiledOpenPhysicalCanonicalLineageHistory history)
      closingRound := by
  let epochStart := physicalState.step controller
    (profiledOpenWitnessedStreamingEpochAdapter A strategy hwin basis
      initialCode policy semanticState initialRoot package controller)
    (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis initialCode
      policy semanticState initialRoot package)
    (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
      initialCode policy semanticState initialRoot package)
    previousClosingRound
  have hstart := profiledOpenWitnessedStreaming_step_epochStart A strategy hwin
    basis initialCode policy semanticState initialRoot package controller
    physicalState previousClosingRound hprevious
  exact profiledOpenWitnessedStreamingStrictRunClosingProjection A strategy
    hwin basis initialCode policy semanticState initialRoot package controller
    epochStart history closingRound hboth hstart.1 hstart.2

end


end DetParityAutomaton

end DistributedSynthesis
