/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPhysicalQueryCoverage

/-!
# Concrete epoch adapter for the witnessed distinguished branch

This file installs `ProfiledOpenPhysicalRecutPhase` as the literal `Phase` of
`FiniteEpochQueryAdapter`, with all table moves and lineages retained in
`Finset.univ`.  The branch is the finite witnessed distinguished recurrence,
its bank is the witnessed common table bank, and its query is the honest
reachable sidewise query alphabet.

There is one deliberately exposed parameter: the physical controller's
single-query accumulator.  The recut phase itself only produces a finite set
of compatible closing queries.  Choosing one of them arbitrarily would not
show that the distinguished semantic branch consumes the actual query.
Accordingly `ProfiledOpenWitnessedQueryAccumulator` is the exact remaining
projection supplied by the physical controller installation; it is not
hidden behind a default or a leader/orientation test.

`ProfiledOpenWitnessedClosingClockWitness` states the proof-only invariant
needed of that projection at a closing round.  The main theorem proves that
this invariant gives the concrete `ProfiledOpenWitnessedPhysicalEpochQueryCovered`
fact, the exact distinguished branch step, and the phase restart.  All side,
lineage, and sticky-row coordinates occur only in the existential proof
witness and never in a process-local transition.
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

private abbrev WitnessedPhysicalBranch :=
  ProfiledOpenWitnessedDistinguishedState A strategy hwin basis initialCode
    policy semanticState initialRoot package

private abbrev WitnessedPhysicalBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev WitnessedPhysicalQuery :=
  ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
    max i u v x y s, max i u v x y s} A initialCode

private abbrev WitnessedPhysicalPhase :=
  ProfiledOpenPhysicalRecutPhase A

/-! ## The exact single-query projection parameter -/

/-- A physical controller's query projection.  Its type is exactly the
`accumulateQuery` field of the concrete epoch adapter.  It may use the finite
global proof coordinates, but it is never a local transition map and cannot
change the controller's Moore outputs.

No law is silently bundled here.  The closing law is the separate
`ProfiledOpenWitnessedClosingClockWitness` below. -/
structure ProfiledOpenWitnessedQueryAccumulator
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂) where
  accumulate :
    WitnessedPhysicalBranch A strategy hwin basis initialCode policy
        semanticState initialRoot package →
      Option (WitnessedPhysicalBank A initialCode) →
      WitnessedPhysicalPhase A → Bool → Bool →
      WitnessedPhysicalQuery A initialCode →
      controller.OneControl → controller.TwoControl →
      EnvironmentRound In₁ In₂ →
      controller.OneControl → controller.TwoControl →
      WitnessedPhysicalQuery A initialCode

/-! ## Distinguished branch and concrete recut adapter -/

/-- The common bank label stored at a distinguished branch state. -/
noncomputable def profiledOpenWitnessedDistinguishedLabel
    (current : WitnessedPhysicalBranch A strategy hwin basis initialCode
      policy semanticState initialRoot package) :
    Option (WitnessedPhysicalBank A initialCode) :=
  package.table.toTransitionRationalTree.labelOf current.1.1.1

/-- Short wrapper around the already proved distinguished recurrence. -/
noncomputable def profiledOpenWitnessedDistinguishedBranchStep
    (current : WitnessedPhysicalBranch A strategy hwin basis initialCode
      policy semanticState initialRoot package)
    (query : WitnessedPhysicalQuery A initialCode) :
    WitnessedPhysicalBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package :=
  profiledOpenWitnessedDistinguishedStep A strategy hwin basis initialCode
    policy semanticState initialRoot package current query

/-- The old finite move identity stored by the distinguished actual
candidate.  This is a proof-machine projection; it is never installed in a
process-local controller. -/
noncomputable def profiledOpenWitnessedDistinguishedMove
    (current : WitnessedPhysicalBranch A strategy hwin basis initialCode
      policy semanticState initialRoot package) :
    ProfiledOpenIndexedBiBeliefMove A :=
  current.1.2.2.2.2

/-- Empty-word reachable query whose direction accumulator is initialized at
the supplied old move.  All pivots and boundary inputs are harmless
placeholders until the closing round overwrites them. -/
noncomputable def profiledOpenWitnessedInitialQueryForMove
    (move : ProfiledOpenIndexedBiBeliefMove A) :
    WitnessedPhysicalQuery A initialCode :=
  let pivot : IndexedLineageCandidate I := (default, .first)
  let candidate :=
    profiledOpenPhysicalDirectionAccumulatorCandidateInitial A move
  profiledOpenWitnessedTableQueryWithDirection A initialCode default .right
    (candidate.finish A pivot pivot default default)

/-- Branch-indexed initialization at its literal old move. -/
noncomputable def profiledOpenWitnessedInitialQueryForBranch
    (current : WitnessedPhysicalBranch A strategy hwin basis initialCode
      policy semanticState initialRoot package) :
    WitnessedPhysicalQuery A initialCode :=
  profiledOpenWitnessedInitialQueryForMove A initialCode
    (profiledOpenWitnessedDistinguishedMove A strategy hwin basis initialCode
      policy semanticState initialRoot package current)

/-- Concrete finite epoch adapter.  The query is reset to the canonical
empty-word reachable query at every epoch boundary.  The recut phase is reset
to all finite table moves, and each strict physical round advances every
lineage. -/
noncomputable def profiledOpenWitnessedConcreteEpochAdapter
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller) :
    FiniteEpochQueryAdapter In₁ In₂
      (WitnessedPhysicalBranch A strategy hwin basis initialCode policy
        semanticState initialRoot package)
      (WitnessedPhysicalBank A initialCode)
      (WitnessedPhysicalQuery A initialCode)
      (WitnessedPhysicalPhase A) controller where
  initialQuery := profiledOpenWitnessedInitialQueryForBranch A strategy hwin
    basis initialCode policy semanticState initialRoot package
    (profiledOpenWitnessedDistinguishedInitial A strategy hwin basis
      initialCode policy semanticState initialRoot package)
  initialPhase := profiledOpenPhysicalRecutPhaseInitial A Finset.univ
  accumulateQuery := queryAccumulator.accumulate
  advancePhase := fun _ _ phase _ _ _ _ _ round _ _ =>
    phase.advance A initialCode Finset.univ Finset.univ round
  restartQuery := fun branch _ _ _ _ _ =>
    profiledOpenWitnessedInitialQueryForBranch A strategy hwin basis
      initialCode policy semanticState initialRoot package branch
  restartPhase := fun _ _ _ _ _ _ =>
    profiledOpenPhysicalRecutPhaseInitial A Finset.univ

@[simp] theorem profiledOpenWitnessedConcreteEpochAdapter_initialPhase
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller) :
    (profiledOpenWitnessedConcreteEpochAdapter A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      queryAccumulator).initialPhase =
      profiledOpenPhysicalRecutPhaseInitial A Finset.univ :=
  rfl

@[simp] theorem profiledOpenWitnessedConcreteEpochAdapter_advancePhase
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (branch : WitnessedPhysicalBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package)
    (bank : Option (WitnessedPhysicalBank A initialCode))
    (phase : WitnessedPhysicalPhase A)
    (receivedOne receivedTwo : Bool)
    (query : WitnessedPhysicalQuery A initialCode)
    (one : controller.OneControl) (two : controller.TwoControl)
    (round : EnvironmentRound In₁ In₂)
    (nextOne : controller.OneControl) (nextTwo : controller.TwoControl) :
    (profiledOpenWitnessedConcreteEpochAdapter A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      queryAccumulator).advancePhase branch bank phase receivedOne receivedTwo
        query one two round nextOne nextTwo =
      phase.advance A initialCode Finset.univ Finset.univ round :=
  rfl

@[simp] theorem profiledOpenWitnessedConcreteEpochAdapter_restartPhase
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (branch : WitnessedPhysicalBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package)
    (bank : Option (WitnessedPhysicalBank A initialCode))
    (phase : WitnessedPhysicalPhase A)
    (receivedOne receivedTwo : Bool)
    (query : WitnessedPhysicalQuery A initialCode) :
    (profiledOpenWitnessedConcreteEpochAdapter A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      queryAccumulator).restartPhase branch bank phase receivedOne receivedTwo
        query = profiledOpenPhysicalRecutPhaseInitial A Finset.univ :=
  rfl

/-! ## The exact adapter-clock invariant -/

private abbrev WitnessedPhysicalState
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂) :=
  FiniteEpochPhysicalState
    (WitnessedPhysicalBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package)
    (WitnessedPhysicalBank A initialCode)
    (WitnessedPhysicalQuery A initialCode)
    (WitnessedPhysicalPhase A) controller

/-- Run the concrete global physical state through a strict history.  The
proof-side letters merely reconstruct the public strict graph and its actual
lineage witness; the state transition itself receives only `letter.round`. -/
noncomputable def profiledOpenWitnessedPhysicalStrictStateRunFrom
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller) :
    WitnessedPhysicalState A strategy hwin basis initialCode policy
        semanticState initialRoot package controller →
      List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
        (In₂ := In₂)) →
      WitnessedPhysicalState A strategy hwin basis initialCode policy
        semanticState initialRoot package controller
  | physicalState, [] => physicalState
  | physicalState, letter :: history =>
      profiledOpenWitnessedPhysicalStrictStateRunFrom controller
        queryAccumulator
        (physicalState.step controller
          (profiledOpenWitnessedConcreteEpochAdapter A strategy hwin basis
            initialCode policy semanticState initialRoot package controller
            queryAccumulator)
          (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis
            initialCode policy semanticState initialRoot package)
          (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
            initialCode policy semanticState initialRoot package)
          letter.round)
        history

/-- The phase/history equality is automatic for the concrete adapter; it is
not part of the model-specific query projection. -/
theorem profiledOpenWitnessedPhysicalStrictStateRunFrom_phase
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (physicalState : WitnessedPhysicalState A strategy hwin basis initialCode
      policy semanticState initialRoot package controller)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))) :
    (profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      queryAccumulator physicalState history).phase =
      profiledOpenPhysicalStrictPhaseRunFrom A initialCode physicalState.phase
        history := by
  induction history generalizing physicalState with
  | nil => rfl
  | cons letter history ih =>
      let adapter := profiledOpenWitnessedConcreteEpochAdapter A strategy hwin
        basis initialCode policy semanticState initialRoot package controller
        queryAccumulator
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
      have hnext : next.phase = physicalState.phase.advance A initialCode
          Finset.univ Finset.univ letter.round := by
        rw [show next.phase =
          physicalState.completedPhase controller adapter letter.round by
            exact FiniteEpochPhysicalState.step_phase_of_not_closes controller
              adapter label branchStep physicalState letter.round hclose]
        rfl
      change
        (profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
          initialCode policy semanticState initialRoot package controller
          queryAccumulator next history).phase = _
      rw [ih, hnext]
      rfl

/-- Epoch-start specialization: after the adapter's canonical phase reset,
the physical state's phase is literally the universal strict-history run. -/
theorem profiledOpenWitnessedPhysicalStrictStateRunFrom_phase_of_initial
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (physicalState : WitnessedPhysicalState A strategy hwin basis initialCode
      policy semanticState initialRoot package controller)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (hphase : physicalState.phase =
      profiledOpenPhysicalRecutPhaseInitial A Finset.univ) :
    (profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      queryAccumulator physicalState history).phase =
      profiledOpenPhysicalStrictPhaseRun A initialCode history := by
  rw [profiledOpenWitnessedPhysicalStrictStateRunFrom_phase, hphase]
  rfl

/-- Proof-only witness that the single query emitted by the physical query
accumulator is the actual member of the universal recut set.

`phase_eq` is the routine clock invariant.  `completedQuery_eq` is the one
substantive projection field: it says which retained move, lineage history,
side, and sticky-row pivots produced the literal query consumed by the
distinguished branch.  None of those witnesses is available to a local
process. -/
structure ProfiledOpenWitnessedClosingClockWitness
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (physicalState : WitnessedPhysicalState A strategy hwin basis initialCode
      policy semanticState initialRoot package controller)
    (closingRound : EnvironmentRound In₁ In₂) where
  graph_eq : closingRound.graph = .both
  move : ProfiledOpenIndexedBiBeliefMove A
  history : List (ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
    (In₂ := In₂))
  carriedQuery : WitnessedPhysicalQuery A initialCode
  side : IndexedLineageSide
  rightPivot : IndexedLineageCandidate I
  leftPivot : IndexedLineageCandidate I
  phase_eq : physicalState.phase =
    profiledOpenPhysicalStrictPhaseRun A initialCode history
  completedQuery_eq :
    physicalState.completedQuery controller
        (profiledOpenWitnessedConcreteEpochAdapter A strategy hwin basis
          initialCode policy semanticState initialRoot package controller
          queryAccumulator) closingRound =
      profiledOpenWitnessedTableQueryWithDirection A initialCode carriedQuery
        side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          (profiledOpenPhysicalStrictHistoryDirection history rightPivot
            leftPivot closingRound.inputOne closingRound.inputTwo)⟩

/-- Stronger induction-facing projection.  The closing physical state is
definitionally the run from an epoch-start state, so the phase equality is
proved by the adapter and the only model-specific semantic field left is
`completedQuery_eq`. -/
structure ProfiledOpenWitnessedStrictRunClosingProjection
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (epochStart : WitnessedPhysicalState A strategy hwin basis initialCode
      policy semanticState initialRoot package controller)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (closingRound : EnvironmentRound In₁ In₂) where
  graph_eq : closingRound.graph = .both
  epochStart_phase_eq : epochStart.phase =
    profiledOpenPhysicalRecutPhaseInitial A Finset.univ
  move : ProfiledOpenIndexedBiBeliefMove A
  carriedQuery : WitnessedPhysicalQuery A initialCode
  side : IndexedLineageSide
  rightPivot : IndexedLineageCandidate I
  leftPivot : IndexedLineageCandidate I
  completedQuery_eq :
    let physicalState :=
      profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
        initialCode policy semanticState initialRoot package controller
        queryAccumulator epochStart history
    physicalState.completedQuery controller
        (profiledOpenWitnessedConcreteEpochAdapter A strategy hwin basis
          initialCode policy semanticState initialRoot package controller
          queryAccumulator) closingRound =
      profiledOpenWitnessedTableQueryWithDirection A initialCode carriedQuery
        side
        ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
          (profiledOpenPhysicalStrictHistoryDirection history rightPivot
            leftPivot closingRound.inputOne closingRound.inputTwo)⟩

/-- Convert the induction-facing projection into the generic clock witness;
the phase field is discharged by the strict-state-run theorem. -/
noncomputable def ProfiledOpenWitnessedStrictRunClosingProjection.clockWitness
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (epochStart : WitnessedPhysicalState A strategy hwin basis initialCode
      policy semanticState initialRoot package controller)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (closingRound : EnvironmentRound In₁ In₂)
    (projection : ProfiledOpenWitnessedStrictRunClosingProjection A strategy
      hwin basis initialCode policy semanticState initialRoot package controller
      queryAccumulator epochStart history closingRound) :
    ProfiledOpenWitnessedClosingClockWitness A strategy hwin basis initialCode
      policy semanticState initialRoot package controller queryAccumulator
      (profiledOpenWitnessedPhysicalStrictStateRunFrom A strategy hwin basis
        initialCode policy semanticState initialRoot package controller
        queryAccumulator epochStart history) closingRound where
  graph_eq := projection.graph_eq
  move := projection.move
  history := history
  carriedQuery := projection.carriedQuery
  side := projection.side
  rightPivot := projection.rightPivot
  leftPivot := projection.leftPivot
  phase_eq :=
    profiledOpenWitnessedPhysicalStrictStateRunFrom_phase_of_initial A strategy
      hwin basis initialCode policy semanticState initialRoot package controller
      queryAccumulator epochStart history projection.epochStart_phase_eq
  completedQuery_eq := projection.completedQuery_eq

/-- The clock witness discharges the complete closing-query coverage field at
the adapter's literal `completedPhase` and `completedQuery`. -/
theorem ProfiledOpenWitnessedClosingClockWitness.covered
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (physicalState : WitnessedPhysicalState A strategy hwin basis initialCode
      policy semanticState initialRoot package controller)
    (closingRound : EnvironmentRound In₁ In₂)
    (witness : ProfiledOpenWitnessedClosingClockWitness A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      queryAccumulator physicalState closingRound) :
    let adapter := profiledOpenWitnessedConcreteEpochAdapter A strategy hwin
      basis initialCode policy semanticState initialRoot package controller
      queryAccumulator
    let completedPhase := physicalState.completedPhase controller adapter
      closingRound
    completedPhase.tier = .boundary ∧
      ProfiledOpenWitnessedPhysicalEpochQueryCovered A initialCode
        completedPhase witness.carriedQuery
        (physicalState.completedQuery controller adapter closingRound)
        witness.side Finset.univ Finset.univ closingRound := by
  let adapter := profiledOpenWitnessedConcreteEpochAdapter A strategy hwin
    basis initialCode policy semanticState initialRoot package controller
    queryAccumulator
  have hcoverage :=
    profiledOpenWitnessedPhysicalEpochQueryCovered_after_closingRound A
      initialCode witness.move witness.history witness.carriedQuery witness.side
      witness.rightPivot witness.leftPivot closingRound witness.graph_eq
  simpa only [adapter, FiniteEpochPhysicalState.completedPhase,
    profiledOpenWitnessedConcreteEpochAdapter_advancePhase, witness.phase_eq,
    witness.completedQuery_eq] using hcoverage

/-- Full closing adapter step.  Besides coverage, the branch consumes the
literal completed query exactly once and the recut phase restarts to all
finite moves. -/
theorem ProfiledOpenWitnessedClosingClockWitness.step_bundle
    (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
      In₁ In₂ Out₁ Out₂)
    (queryAccumulator : ProfiledOpenWitnessedQueryAccumulator A strategy hwin
      basis initialCode policy semanticState initialRoot package controller)
    (physicalState : WitnessedPhysicalState A strategy hwin basis initialCode
      policy semanticState initialRoot package controller)
    (closingRound : EnvironmentRound In₁ In₂)
    (witness : ProfiledOpenWitnessedClosingClockWitness A strategy hwin basis
      initialCode policy semanticState initialRoot package controller
      queryAccumulator physicalState closingRound) :
    let adapter := profiledOpenWitnessedConcreteEpochAdapter A strategy hwin
      basis initialCode policy semanticState initialRoot package controller
      queryAccumulator
    let next := physicalState.step controller adapter
      (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis
        initialCode policy semanticState initialRoot package)
      (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
        initialCode policy semanticState initialRoot package)
      closingRound
    let completed := physicalState.completedQuery controller adapter
      closingRound
    next.branch = profiledOpenWitnessedDistinguishedBranchStep A strategy hwin
        basis initialCode policy semanticState initialRoot package
        physicalState.branch completed ∧
      next.phase = profiledOpenPhysicalRecutPhaseInitial A Finset.univ ∧
      (physicalState.completedPhase controller adapter closingRound).tier =
          .boundary ∧
      ProfiledOpenWitnessedPhysicalEpochQueryCovered A initialCode
        (physicalState.completedPhase controller adapter closingRound)
        witness.carriedQuery completed witness.side Finset.univ Finset.univ
        closingRound := by
  let adapter := profiledOpenWitnessedConcreteEpochAdapter A strategy hwin
    basis initialCode policy semanticState initialRoot package controller
    queryAccumulator
  have hclose : profiledOpenPhysicalClosesEpoch closingRound.graph = true := by
    simpa [witness.graph_eq]
  have hbranch := FiniteEpochPhysicalState.step_branch_of_closes controller
    adapter
    (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis initialCode
      policy semanticState initialRoot package)
    (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
      initialCode policy semanticState initialRoot package)
    physicalState closingRound hclose
  have hphase := FiniteEpochPhysicalState.step_phase_of_closes controller
    adapter
    (profiledOpenWitnessedDistinguishedLabel A strategy hwin basis initialCode
      policy semanticState initialRoot package)
    (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
      initialCode policy semanticState initialRoot package)
    physicalState closingRound hclose
  have hcovered := witness.covered A strategy hwin basis initialCode policy
    semanticState initialRoot package controller queryAccumulator physicalState
    closingRound
  dsimp only
  refine ⟨hbranch, ?_, hcovered⟩
  simpa only [adapter,
    profiledOpenWitnessedConcreteEpochAdapter_restartPhase] using hphase

end

end DetParityAutomaton

end DistributedSynthesis
