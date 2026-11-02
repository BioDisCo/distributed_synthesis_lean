/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenancePhysicalAdapter

/-!
# A finite distinguished state for the provenance table

The generic relational-table cursor contains its complete query node.  That
node is useful in the extraction proof, but it is not finite-state runtime
data.  This file projects the cursor to exactly the finite public table
control, the finite saturated candidate set, and one proof-side actual
candidate.  Representation by a cursor is retained only as a proposition.

The actual candidate is never exposed to either process.  Its transition is
the distinguished live successor supplied by the policy-retagged coverage
theorem; the public candidate set still takes the complete saturation.  Thus
the construction supplies one coherent anti-mosaic thread without removing
any locally possible alternative.
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
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable
  (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot)

/-- The finite encoded candidate literally carried by the provenance table. -/
abbrev ProfiledOpenProvenancePolicyEncodedCandidate :=
  ProfiledOpenWitnessedEncodedCandidate A initialCode

/-- Policy-strengthened liveness on encoded candidates. -/
abbrev ProfiledOpenProvenancePolicyEncodedLive :=
  SourceAwareRelationalLive
    (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
      codePolicy)

/-- Candidate validity for the current common table bank. -/
abbrev ProfiledOpenProvenancePolicyEncodedValid :=
  SourceAwareRelationalCandidateValid
    (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)

/-- The descriptor edge stored by the policy-retagged table. -/
abbrev ProfiledOpenProvenancePolicyEncodedDescriptorEdge :=
  sourceAwareRelationalExactEdge
    (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy)

/-- The encoded descriptor control transition. -/
abbrev ProfiledOpenProvenancePolicyEncodedControlStep :=
  sourceAwareRelationalControlStep
    (Family := ProfiledOpenWitnessedTableFamily A initialCode)
    (ProfiledOpenWitnessedTableControlStep A initialCode)

/-- Candidate-level presentation of the encoded retagged edge. -/
def profiledOpenProvenancePolicyEncodedCandidateEdge
    (source : ProfiledOpenProvenancePolicyEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (target : ProfiledOpenProvenancePolicyEncodedCandidate A initialCode) :
    Prop :=
  ProfiledOpenProvenancePolicyEncodedDescriptorEdge A strategy hwin basis
    initialCode codePolicy source.2 bank query target.1 target.2

/-- The complete finite public table recurrence state. -/
abbrev ProfiledOpenProvenancePolicyDistinguishedPublicState :=
  ProfiledOpenProvenancePolicyRetaggedBranchState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

/-- The runtime-shaped raw product: public state and one finite proof-side
actual candidate.  There is no cursor node or query list in this type. -/
abbrev ProfiledOpenProvenancePolicyDistinguishedRawState :=
  ProfiledOpenProvenancePolicyDistinguishedPublicState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package ×
    ProfiledOpenProvenancePolicyEncodedCandidate A initialCode

/-- Project the finite part of a generic proof cursor. -/
noncomputable def profiledOpenProvenancePolicyPublicStateOfCursor
    (cursor : package.branch.Cursor) :
    ProfiledOpenProvenancePolicyDistinguishedPublicState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package :=
  (package.table.toTransitionRationalTree.controlAt cursor.node,
    cursor.candidates)

/-- Cursor representation is proof-only.  It is deliberately a proposition,
so the cursor node and its unbounded query history are erased from data. -/
def ProfiledOpenProvenancePolicyDistinguishedRepresented
    (current : ProfiledOpenProvenancePolicyDistinguishedRawState A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package) :
    Prop :=
  ∃ cursor : package.branch.Cursor,
    profiledOpenProvenancePolicyPublicStateOfCursor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package cursor =
      current.1 ∧
    cursor.actual = current.2

/-- Finite distinguished state.  Only the raw finite product is data. -/
abbrev ProfiledOpenProvenancePolicyDistinguishedState :=
  { current : ProfiledOpenProvenancePolicyDistinguishedRawState A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package //
    ProfiledOpenProvenancePolicyDistinguishedRepresented A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current }

noncomputable instance
    profiledOpenProvenancePolicyDistinguishedState_fintype :
    Fintype (ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :=
  Fintype.ofFinite _

/-- Public-state projection. -/
def profiledOpenProvenancePolicyDistinguishedPublic
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    ProfiledOpenProvenancePolicyDistinguishedPublicState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package :=
  current.1.1

/-- Proof-side actual-candidate projection. -/
def profiledOpenProvenancePolicyDistinguishedActual
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    ProfiledOpenProvenancePolicyEncodedCandidate A initialCode :=
  current.1.2

/-- Base descriptor of the actual encoded candidate. -/
def profiledOpenProvenancePolicyDistinguishedDescriptor
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    ProfiledOpenWitnessedTableBaseDescriptor A initialCode :=
  current.1.2.2.2

@[simp] theorem profiledOpenProvenancePolicyDistinguishedDescriptor_code
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current).code =
      current.1.2.2.2.code :=
  rfl

@[simp] theorem profiledOpenProvenancePolicyDistinguishedDescriptor_move
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
      ).moveIdentity = current.1.2.2.2.moveIdentity :=
  rfl

/-- Initial finite distinguished state. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedInitial :
    ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package := by
  let cursor := package.branch.initialCursor
  refine ⟨(profiledOpenProvenancePolicyRetaggedBranchInitial A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package,
      cursor.actual), ?_⟩
  exact ⟨cursor, rfl, rfl⟩

/-! ## The literal distinguished successor -/

omit [Inhabited I] in
/-- Encoded table coverage, exposed at candidate level for the deterministic
proof-side successor selector. -/
theorem profiledOpenProvenancePolicyEncodedCandidate_liveSuccessorCoverage :
    SourceAwareRelationalCandidateLiveSuccessorCoverage
      (ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
        initialCode)
      (profiledOpenProvenancePolicyEncodedCandidateEdge A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode) := by
  intro source bank query hlive hvalid
  obtain ⟨target, hgood, htargetLive⟩ :=
    profiledOpenProvenancePolicyRetagged_encodedLiveSuccessorCoverage A
      strategy hwin basis initialCode codePolicy source bank query hlive hvalid
  exact ⟨target, hgood, htargetLive⟩

/-- Deterministic omniscient target.  It depends only on finite source, bank,
and query data and is not exposed as a process-local choice. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedCandidateSuccessor
    (source : ProfiledOpenProvenancePolicyEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    ProfiledOpenProvenancePolicyEncodedCandidate A initialCode :=
  sourceAwareRelationalDistinguishedSuccessor
    (ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis initialCode
      codePolicy)
    (profiledOpenProvenancePolicyEncodedCandidateEdge A strategy hwin basis
      initialCode codePolicy)
    (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode)
    source bank query

/-- Cursor update whose public candidate set is the full saturation and whose
actual coordinate is the distinguished retagged successor. -/
noncomputable def profiledOpenProvenancePolicyCursorDistinguishedStep
    (cursor : package.branch.Cursor)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    package.branch.Cursor := by
  let bank := cursor.move package.branch
  let nextCandidates := relationalFamilySaturation
    (ProfiledOpenProvenancePolicyEncodedDescriptorEdge A strategy hwin basis
      initialCode codePolicy)
    (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode)
    cursor.candidates bank query
  let target :=
    profiledOpenProvenancePolicyDistinguishedCandidateSuccessor A strategy hwin
      basis initialCode codePolicy cursor.actual bank query
  have hvalid : ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
      initialCode cursor.actual.2 cursor.actual.1 bank :=
    cursor.move_valid_actual package.branch
  have hgood : SourceAwareRelationalFamilyCandidateGood
      (profiledOpenProvenancePolicyEncodedCandidateEdge A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode)
      cursor.actual bank query target :=
    sourceAwareRelationalDistinguishedSuccessor_good
      (ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
        initialCode)
      (profiledOpenProvenancePolicyEncodedCandidateEdge A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode)
      (profiledOpenProvenancePolicyEncodedCandidate_liveSuccessorCoverage A
        strategy hwin basis initialCode codePolicy)
      cursor.actual bank query cursor.actual_live hvalid
  have htargetMem : target ∈ nextCandidates := by
    apply (mem_relationalFamilySaturation_iff
      (ProfiledOpenProvenancePolicyEncodedDescriptorEdge A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode)
      cursor.candidates bank query target).2
    exact ⟨cursor.actual, cursor.actual_mem, hgood⟩
  have htargetLive : ProfiledOpenProvenancePolicyEncodedLive A strategy hwin
      basis initialCode codePolicy target.2 target.1 :=
    sourceAwareRelationalDistinguishedSuccessor_live
      (ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
        initialCode)
      (profiledOpenProvenancePolicyEncodedCandidateEdge A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode)
      (profiledOpenProvenancePolicyEncodedCandidate_liveSuccessorCoverage A
        strategy hwin basis initialCode codePolicy)
      cursor.actual bank query cursor.actual_live hvalid
  exact
    { node := cursor.node ++ [(query, nextCandidates)]
      candidates := nextCandidates
      actual := target
      treeLabel := package.branch.tree
        (cursor.node ++ [(query, nextCandidates)])
      treeLabel_eq := rfl
      candidates_eq := by simp [nextCandidates, observableAt]
      actual_mem := htargetMem
      actual_live := htargetLive }

/-- The custom cursor update follows one literal policy-retagged exact edge. -/
theorem profiledOpenProvenancePolicyCursorDistinguishedStep_exact
    (cursor : package.branch.Cursor)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy cursor.actual.2.1 cursor.actual.2.2
      (cursor.move package.branch) query
      (profiledOpenProvenancePolicyCursorDistinguishedStep A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        cursor query).actual.1
      (profiledOpenProvenancePolicyCursorDistinguishedStep A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        cursor query).actual.2.2 := by
  let bank := cursor.move package.branch
  have hvalid : ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
      initialCode cursor.actual.2 cursor.actual.1 bank :=
    cursor.move_valid_actual package.branch
  have hgood := sourceAwareRelationalDistinguishedSuccessor_good
    (ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis initialCode
      codePolicy)
    (ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
      initialCode)
    (profiledOpenProvenancePolicyEncodedCandidateEdge A strategy hwin basis
      initialCode codePolicy)
    (ProfiledOpenProvenancePolicyEncodedControlStep A initialCode)
    (profiledOpenProvenancePolicyEncodedCandidate_liveSuccessorCoverage A
      strategy hwin basis initialCode codePolicy)
    cursor.actual bank query cursor.actual_live hvalid
  exact hgood.1.1

/-- The public coordinate of the custom cursor update is exactly the existing
retagged table recurrence. -/
theorem profiledOpenProvenancePolicyPublicStateOfCursor_distinguishedStep
    (cursor : package.branch.Cursor)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    profiledOpenProvenancePolicyPublicStateOfCursor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyCursorDistinguishedStep A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          cursor query) =
      profiledOpenProvenancePolicyRetaggedBranchStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyPublicStateOfCursor A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package cursor)
        query := by
  have hlabel : package.table.toTransitionRationalTree.labelOf
        (package.table.toTransitionRationalTree.controlAt cursor.node) =
      some (cursor.move package.branch) := by
    change package.table.toTransitionRationalTree.labeledTree cursor.node = _
    rw [← package.branch_tree_eq]
    exact cursor.tree_eq_some_move package.branch
  have hlabel' : package.table.toTransitionRationalTree.labelOf
        (profiledOpenProvenancePolicyPublicStateOfCursor A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          cursor).1 = some (cursor.move package.branch) := by
    simpa only [profiledOpenProvenancePolicyPublicStateOfCursor] using hlabel
  rw [profiledOpenProvenancePolicyRetaggedBranchStep, hlabel']
  apply Prod.ext
  · simp only [profiledOpenProvenancePolicyPublicStateOfCursor,
      profiledOpenProvenancePolicyCursorDistinguishedStep]
    rw [TransitionRationalTree.controlAt_append]
    rfl
  · rfl

/-! ## Total finite recurrence and its projections -/

/-- Total transition on the finite distinguished state. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedStep
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package := by
  let cursor := Classical.choose current.property
  let nextCursor :=
    profiledOpenProvenancePolicyCursorDistinguishedStep A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package cursor query
  exact ⟨(profiledOpenProvenancePolicyPublicStateOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package nextCursor,
      nextCursor.actual), ⟨nextCursor, rfl, rfl⟩⟩

/-- Public branch recurrence equality. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_public
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package current
          query) =
      profiledOpenProvenancePolicyRetaggedBranchStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package current)
        query := by
  let cursor := Classical.choose current.property
  have hcursor := Classical.choose_spec current.property
  change profiledOpenProvenancePolicyPublicStateOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyCursorDistinguishedStep A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          cursor query) = _
  rw [profiledOpenProvenancePolicyPublicStateOfCursor_distinguishedStep]
  rw [hcursor.1]
  rfl

/-- One finite common bank read from the represented public table state. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedBank
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    ProfiledOpenWitnessedTableBank A initialCode :=
  (Classical.choose current.property).move package.branch

/-- The public control labels the distinguished state's selected common bank. -/
theorem profiledOpenProvenancePolicyDistinguished_label
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    package.table.toTransitionRationalTree.labelOf
        (profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          current).1 =
      some (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        current) := by
  let cursor := Classical.choose current.property
  have hcursor := Classical.choose_spec current.property
  change package.table.toTransitionRationalTree.labelOf current.1.1.1 =
    some (cursor.move package.branch)
  rw [← hcursor.1]
  change package.table.toTransitionRationalTree.labeledTree cursor.node = _
  rw [← package.branch_tree_eq]
  exact cursor.tree_eq_some_move package.branch

/-- Membership, policy liveness, and validity at the current common bank are
all preserved by the finite recurrence. -/
theorem profiledOpenProvenancePolicyDistinguished_mem_live_valid
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) :
    let actual := profiledOpenProvenancePolicyDistinguishedActual A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current
    actual ∈
        (profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          current).2 ∧
      ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis initialCode
        codePolicy actual.2 actual.1 ∧
      ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
        initialCode actual.2 actual.1
          (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package
            current) := by
  let cursor := Classical.choose current.property
  have hcursor := Classical.choose_spec current.property
  have hall : cursor.actual ∈
        (profiledOpenProvenancePolicyPublicStateOfCursor A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          cursor).2 ∧
      ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis initialCode
        codePolicy cursor.actual.2 cursor.actual.1 ∧
      ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
        initialCode cursor.actual.2 cursor.actual.1
          (cursor.move package.branch) :=
    ⟨cursor.actual_mem, cursor.actual_live,
      cursor.move_valid_actual package.branch⟩
  change current.1.2 ∈ current.1.1.2 ∧ _ ∧ _
  simpa only [profiledOpenProvenancePolicyDistinguishedActual,
    profiledOpenProvenancePolicyDistinguishedPublic,
    profiledOpenProvenancePolicyDistinguishedBank, cursor, hcursor.1,
    hcursor.2] using hall

/-- Literal retagged exact edge selected by one finite step. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_exact
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy
      ((profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
        ).2.1)
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        current)
      (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current)
      query
      (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next).1
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package next) :=
    by
  let cursor := Classical.choose current.property
  have hcursor := Classical.choose_spec current.property
  change ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
    initialCode codePolicy current.1.2.2.1 current.1.2.2.2
      (cursor.move package.branch) query _ _
  rw [← hcursor.2]
  exact profiledOpenProvenancePolicyCursorDistinguishedStep_exact A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
    cursor query

/-- The actual policy-state coordinate follows the selected rational code
policy exactly. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_policySuccessor
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next).1 =
      codePolicy.successor
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).1 query.1.2 := by
  exact profiledOpenProvenancePolicyRetaggedExactEdge_policySuccessor A
    strategy hwin basis initialCode codePolicy
      (profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
        query)

/-- Code projection of the exact policy successor. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_code
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next).code =
      (codePolicy.successor
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).1 query.1.2).1 := by
  exact congrArg Prod.fst
    (profiledOpenProvenancePolicyDistinguishedStep_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current query)

/-- Parity-control projection of the exact policy successor. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_control
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next).control =
      (codePolicy.successor
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).1 query.1.2).2 := by
  exact congrArg Prod.snd
    (profiledOpenProvenancePolicyDistinguishedStep_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current query)

/-- Source and target move identities both realize their respective policy
states. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_moveRealizes
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
    ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin basis
        initialCode codePolicy
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).moveIdentity ∧
      ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
        basis initialCode codePolicy
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          next).1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          next).moveIdentity := by
  exact profiledOpenProvenancePolicyRetaggedExactEdge_realizes A strategy hwin
    basis initialCode codePolicy
      (profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
        query)

/-- The post-state again satisfies the full finite distinguished invariant. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_mem_live_valid
    (current : ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
    let actual := profiledOpenProvenancePolicyDistinguishedActual A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        next
    actual ∈
        (profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package next).2 ∧
      ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis initialCode
        codePolicy actual.2 actual.1 ∧
      ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
        initialCode actual.2 actual.1
          (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package next) :=
  profiledOpenProvenancePolicyDistinguished_mem_live_valid A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package
      (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current query)

end

end DetParityAutomaton

end DistributedSynthesis
