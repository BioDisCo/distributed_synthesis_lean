/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReceiptFilteredCandidateState
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedConcreteEpochAdapter

/-!
# Projecting the witnessed streaming branch into receipt-filtered candidates

The concrete distinguished branch stores a source-aware encoded candidate.
This file checks the exact type seam needed by the receipt-filtered carrier:
decoding the current and next distinguished candidates turns the encoded
distinguished step into the witnessed candidate `Good` relation used by the
receipt saturation.

The bank below is the public table label at the represented cursor.  Choosing
the proof cursor does not select a side, leader, orientation, or lineage; the
label equality theorem shows that the same bank is already stored by the
finite rational table control.
-/

namespace DistributedSynthesis

universe i u v x y s

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
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
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

private abbrev ProjectionBranch :=
  ProfiledOpenWitnessedDistinguishedState A strategy hwin basis initialCode
    policy semanticState initialRoot package

private abbrev ProjectionCandidate :=
  ProfiledOpenActiveLaneTaggedCandidate A initialCode

private abbrev ProjectionEncodedCandidate :=
  ProfiledOpenWitnessedEncodedCandidate A initialCode

private abbrev ProjectionBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev ProjectionQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private abbrev ProjectionEncodedLive :=
  SourceAwareRelationalLive
    (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode)

private abbrev ProjectionEncodedValid :=
  SourceAwareRelationalCandidateValid
    (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)

private abbrev ProjectionEncodedEdge :=
  sourceAwareRelationalExactEdge
    (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
      basis initialCode)

private abbrev ProjectionEncodedControlStep :=
  sourceAwareRelationalControlStep
    (Family := ProfiledOpenWitnessedTableFamily A initialCode)
    (ProfiledOpenWitnessedTableControlStep A initialCode)

private abbrev ProjectionBaseGood
    (source : ProjectionCandidate A initialCode)
    (bank : ProjectionBank A initialCode)
    (query : ProjectionQuery A initialCode)
    (target : ProjectionCandidate A initialCode) : Prop :=
  SourceAwareRelationalFamilyCandidateGood
    (profiledOpenActiveLaneWitnessedCandidateEdge A strategy hwin basis
      initialCode)
    (ProfiledOpenWitnessedTableControlStep A initialCode)
    source bank query target

/-! ## Literal projection and represented table label -/

/-- Forget only the redundant source-family copy. -/
def profiledOpenWitnessedDistinguishedProjectedCandidate
    (current : ProjectionBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package) :
    ProjectionCandidate A initialCode :=
  sourceAwareRelationalCandidateDecode current.1.2

/-- The bank at the proof-erased represented cursor. -/
noncomputable def profiledOpenWitnessedDistinguishedRepresentedBank
    (current : ProjectionBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package) :
    ProjectionBank A initialCode :=
  (Classical.choose current.property).move package.branch

/-- The chosen represented bank is exactly the public finite table label. -/
theorem profiledOpenWitnessedDistinguishedLabel_eq_some_representedBank
    (current : ProjectionBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package) :
    profiledOpenWitnessedDistinguishedLabel A strategy hwin basis initialCode
        policy semanticState initialRoot package current =
      some (profiledOpenWitnessedDistinguishedRepresentedBank A strategy hwin
        basis initialCode policy semanticState initialRoot package current) := by
  let cursor := Classical.choose current.property
  have hcursor := Classical.choose_spec current.property
  change package.table.toTransitionRationalTree.labelOf current.1.1.1 =
    some (cursor.move package.branch)
  rw [← hcursor.1]
  change package.table.toTransitionRationalTree.labeledTree cursor.node = _
  rw [← package.branch_tree_eq]
  exact cursor.tree_eq_some_move package.branch

/-! ## The distinguished step really is the base witnessed edge -/

/-- At the cursor level, the selected next actual candidate satisfies the
encoded candidate `Good` relation. -/
theorem profiledOpenWitnessedCursorDistinguishedStep_actual_good
    (cursor : package.branch.Cursor)
    (query : ProjectionQuery A initialCode) :
    SourceAwareRelationalFamilyCandidateGood
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (ProjectionEncodedControlStep A initialCode)
      cursor.actual (cursor.move package.branch) query
      (profiledOpenWitnessedCursorDistinguishedStep A
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (policy := policy) (state := semanticState) (initialRoot := initialRoot)
        initialCode package cursor query).actual := by
  let bank := cursor.move package.branch
  let target := profiledOpenWitnessedDistinguishedCandidateSuccessor A
    (strategy := strategy) (hwin := hwin) (basis := basis)
    initialCode cursor.actual bank query
  have hvalid : ProjectionEncodedValid A strategy hwin basis initialCode
      cursor.actual.2 cursor.actual.1 bank :=
    cursor.move_valid_actual package.branch
  have hgood : SourceAwareRelationalFamilyCandidateGood
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (ProjectionEncodedControlStep A initialCode) cursor.actual bank query
        target :=
    sourceAwareRelationalDistinguishedSuccessor_good
      (ProjectionEncodedLive A strategy hwin basis initialCode)
      (ProjectionEncodedValid A strategy hwin basis initialCode)
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (ProjectionEncodedControlStep A initialCode)
      (profiledOpenWitnessedEncodedCandidate_liveSuccessorCoverage A
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (policy := policy) (state := semanticState) (initialRoot := initialRoot)
        initialCode package)
      cursor.actual bank query cursor.actual_live hvalid
  simpa only [profiledOpenWitnessedCursorDistinguishedStep, target, bank] using
    hgood

/-- A live source-aware encoded `Good` edge decodes to the exact witnessed
base-candidate `Good` edge. -/
theorem profiledOpenWitnessedEncodedGood_decode
    {source target : ProjectionEncodedCandidate A initialCode}
    {bank : ProjectionBank A initialCode}
    {query : ProjectionQuery A initialCode}
    (hsourceLive : ProjectionEncodedLive A strategy hwin basis initialCode
      source.2 source.1)
    (hgood : SourceAwareRelationalFamilyCandidateGood
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (ProjectionEncodedControlStep A initialCode)
      source bank query target) :
    ProjectionBaseGood A strategy hwin basis initialCode
      (sourceAwareRelationalCandidateDecode source) bank query
      (sourceAwareRelationalCandidateDecode target) := by
  rcases hgood with ⟨hedge, hcontrol⟩
  rcases hedge with ⟨hbase, _htargetFamily⟩
  constructor
  · simpa only [sourceAwareRelationalCandidateDecode, hsourceLive.1] using
      hbase
  · exact hcontrol

/-- **Concrete seam check.**  Projecting the actual current and next
distinguished candidates gives precisely the witnessed `Good` relation
consumed by the receipt-filtered saturation. -/
theorem profiledOpenWitnessedDistinguishedStep_projected_good
    (current : ProjectionBranch A strategy hwin basis initialCode policy
      semanticState initialRoot package)
    (query : ProjectionQuery A initialCode) :
    let next := profiledOpenWitnessedDistinguishedBranchStep A strategy hwin
      basis initialCode policy semanticState initialRoot package current query
    ProjectionBaseGood A strategy hwin basis initialCode
      (profiledOpenWitnessedDistinguishedProjectedCandidate A strategy hwin
        basis initialCode policy semanticState initialRoot package current)
      (profiledOpenWitnessedDistinguishedRepresentedBank A strategy hwin basis
        initialCode policy semanticState initialRoot package current)
      query
      (profiledOpenWitnessedDistinguishedProjectedCandidate A strategy hwin
        basis initialCode policy semanticState initialRoot package next) := by
  let cursor := Classical.choose current.property
  have hcursor := Classical.choose_spec current.property
  let nextCursor := profiledOpenWitnessedCursorDistinguishedStep A
    (strategy := strategy) (hwin := hwin) (basis := basis)
    (policy := policy) (state := semanticState) (initialRoot := initialRoot)
    initialCode package cursor query
  have hencoded :=
    profiledOpenWitnessedCursorDistinguishedStep_actual_good A strategy hwin
      basis initialCode policy semanticState initialRoot package cursor query
  have hdecoded := profiledOpenWitnessedEncodedGood_decode A strategy hwin
    basis initialCode cursor.actual_live hencoded
  change ProjectionBaseGood A strategy hwin basis initialCode
    (sourceAwareRelationalCandidateDecode current.1.2)
    (cursor.move package.branch) query
    (sourceAwareRelationalCandidateDecode
      (profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
        initialCode policy semanticState initialRoot package current query).1.2)
  rw [← hcursor.2]
  change ProjectionBaseGood A strategy hwin basis initialCode
    (sourceAwareRelationalCandidateDecode cursor.actual)
    (cursor.move package.branch) query
    (sourceAwareRelationalCandidateDecode
      (profiledOpenWitnessedDistinguishedStep A strategy hwin basis initialCode
        policy semanticState initialRoot package current query).1.2)
  change ProjectionBaseGood A strategy hwin basis initialCode
    (sourceAwareRelationalCandidateDecode cursor.actual)
    (cursor.move package.branch) query
    (sourceAwareRelationalCandidateDecode nextCursor.actual)
  exact hdecoded

/-! ## The concrete branch extended by the filtered carrier -/

/-- The existing distinguished branch plus the receipt-filtered candidate
set which contains its decoded actual candidate.  The membership field is a
proof-only coverage invariant. -/
structure ProfiledOpenWitnessedReceiptFilteredBranchState where
  branch : ProjectionBranch A strategy hwin basis initialCode policy
    semanticState initialRoot package
  filtered : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode
  projected_mem :
    profiledOpenWitnessedDistinguishedProjectedCandidate A strategy hwin basis
        initialCode policy semanticState initialRoot package branch ∈
      filtered.candidates

noncomputable instance
    profiledOpenWitnessedReceiptFilteredBranchState_fintype :
    Fintype (ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package) := by
  classical
  let encode : ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package →
      ProjectionBranch A strategy hwin basis initialCode policy semanticState
          initialRoot package ×
        ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode :=
    fun state ↦ (state.branch, state.filtered)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftBranch, leftFiltered, _⟩
    rcases right with ⟨rightBranch, rightFiltered, _⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-- The concrete distinguished initial branch, with its projected candidate
as the literal singleton receipt state. -/
noncomputable def profiledOpenWitnessedReceiptFilteredBranchInitial :
    ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin basis
      initialCode policy semanticState initialRoot package := by
  let branch := profiledOpenWitnessedDistinguishedInitial A strategy hwin basis
    initialCode policy semanticState initialRoot package
  let candidate :=
    profiledOpenWitnessedDistinguishedProjectedCandidate A strategy hwin basis
      initialCode policy semanticState initialRoot package branch
  exact
    { branch := branch
      filtered :=
        profiledOpenWitnessedReceiptFilteredCandidateInitial A initialCode
          candidate
      projected_mem :=
        profiledOpenWitnessedReceiptFilteredCandidateInitial_candidate_mem A
          initialCode candidate }

/-- Advance the distinguished branch and simultaneously retain every
witnessed successor at the next distinguished candidate's literal receipt
pair.  The receipt pair is finite global proof data here; no process is told
an active side, leader, orientation, or lineage. -/
noncomputable def ProfiledOpenWitnessedReceiptFilteredBranchState.step
    (current : ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package)
    (query : ProjectionQuery A initialCode) :
    ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin basis
      initialCode policy semanticState initialRoot package := by
  let bank := profiledOpenWitnessedDistinguishedRepresentedBank A strategy hwin
    basis initialCode policy semanticState initialRoot package current.branch
  let nextBranch := profiledOpenWitnessedDistinguishedBranchStep A strategy
    hwin basis initialCode policy semanticState initialRoot package
      current.branch query
  let source := profiledOpenWitnessedDistinguishedProjectedCandidate A strategy
    hwin basis initialCode policy semanticState initialRoot package
      current.branch
  let target := profiledOpenWitnessedDistinguishedProjectedCandidate A strategy
    hwin basis initialCode policy semanticState initialRoot package nextBranch
  let nextFiltered := current.filtered.step A strategy hwin basis initialCode
    bank query target.1.1.1 target.1.1.2
  have hgood : ProjectionBaseGood A strategy hwin basis initialCode source bank
      query target :=
    profiledOpenWitnessedDistinguishedStep_projected_good A strategy hwin basis
      initialCode policy semanticState initialRoot package current.branch query
  have htarget : target ∈ nextFiltered.candidates :=
    current.filtered.target_mem_step_literalReceipts A strategy hwin basis
      initialCode bank query source target current.projected_mem hgood
  exact
    { branch := nextBranch
      filtered := nextFiltered
      projected_mem := htarget }

@[simp] theorem
    ProfiledOpenWitnessedReceiptFilteredBranchState.step_branch
    (current : ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package)
    (query : ProjectionQuery A initialCode) :
    (current.step A strategy hwin basis initialCode policy semanticState
      initialRoot package query).branch =
      profiledOpenWitnessedDistinguishedBranchStep A strategy hwin basis
        initialCode policy semanticState initialRoot package current.branch
          query :=
  rfl

@[simp] theorem
    ProfiledOpenWitnessedReceiptFilteredBranchState.step_rightReceipt
    (current : ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package)
    (query : ProjectionQuery A initialCode) :
    let nextBranch := profiledOpenWitnessedDistinguishedBranchStep A strategy
      hwin basis initialCode policy semanticState initialRoot package
        current.branch query
    (current.step A strategy hwin basis initialCode policy semanticState
      initialRoot package query).filtered.rightReceipt =
      (profiledOpenWitnessedDistinguishedProjectedCandidate A strategy hwin
        basis initialCode policy semanticState initialRoot package
          nextBranch).1.1.1 := by
  rfl

@[simp] theorem
    ProfiledOpenWitnessedReceiptFilteredBranchState.step_leftReceipt
    (current : ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package)
    (query : ProjectionQuery A initialCode) :
    let nextBranch := profiledOpenWitnessedDistinguishedBranchStep A strategy
      hwin basis initialCode policy semanticState initialRoot package
        current.branch query
    (current.step A strategy hwin basis initialCode policy semanticState
      initialRoot package query).filtered.leftReceipt =
      (profiledOpenWitnessedDistinguishedProjectedCandidate A strategy hwin
        basis initialCode policy semanticState initialRoot package
          nextBranch).1.1.2 := by
  rfl

/-- Every concrete extended branch step inherits the unconditional
process-one candidate-set coherence theorem. -/
theorem
    ProfiledOpenWitnessedReceiptFilteredBranchState.step_rightCoherent
    (current : ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package)
    (query : ProjectionQuery A initialCode) :
    ProfiledOpenWitnessedRightCandidateSetCoherent A strategy hwin basis
      initialCode
      (current.step A strategy hwin basis initialCode policy semanticState
        initialRoot package query).filtered.candidates := by
  apply ProfiledOpenWitnessedReceiptFilteredCandidateState.step_rightCoherent

/-- Process-two concrete coherence. -/
theorem
    ProfiledOpenWitnessedReceiptFilteredBranchState.step_leftCoherent
    (current : ProfiledOpenWitnessedReceiptFilteredBranchState A strategy hwin
      basis initialCode policy semanticState initialRoot package)
    (query : ProjectionQuery A initialCode) :
    ProfiledOpenWitnessedLeftCandidateSetCoherent A strategy hwin basis
      initialCode
      (current.step A strategy hwin basis initialCode policy semanticState
        initialRoot package query).filtered.candidates := by
  apply ProfiledOpenWitnessedReceiptFilteredCandidateState.step_leftCoherent

end

end DetParityAutomaton

end DistributedSynthesis
