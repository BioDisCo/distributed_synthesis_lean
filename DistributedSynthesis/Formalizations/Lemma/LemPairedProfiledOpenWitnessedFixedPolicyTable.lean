/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedCommonBank

/-!
# Source-aware fixed-policy table with witnessed shape-free tags

This is the end-to-end finite table adapter for the context-faithful route.
The base candidate carries only a finite tagged family and descriptor.  The
generic source-aware encoding copies that literal family into the finite
descriptor so an exact edge cannot silently select another same-descriptor
family.  Each target tag is the class of the literal semantic child supplied
by the witnessed edge.

The extracted exact thread decodes back to the base candidates.  Therefore
every edge uses the preceding candidate's literal public family and every tag
has an erased semantic witness.  The construction retains all finite
alternatives; it does not reconstruct a permanently hidden bit or tell either
process which side is currently informed.
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

abbrev ProfiledOpenWitnessedTableFamily :=
  SidewiseTaggedFamily
    (ProfiledOpenActiveLaneSideClass A initialCode)
    (ProfiledOpenActiveLaneSideClass A initialCode)
    (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode)

abbrev ProfiledOpenWitnessedTableBaseDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

abbrev ProfiledOpenWitnessedTableDescriptor :=
  SourceAwareRelationalDescriptor
    (ProfiledOpenWitnessedTableFamily A initialCode)
    (ProfiledOpenWitnessedTableBaseDescriptor A initialCode)

abbrev ProfiledOpenWitnessedTableCandidate :=
  RelationalFamilyCandidate (ProfiledOpenWitnessedTableFamily A initialCode)
    (ProfiledOpenWitnessedTableBaseDescriptor A initialCode)

abbrev ProfiledOpenWitnessedTableBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (ProfiledOpenActiveLaneSideClass A initialCode)
    (ProfiledOpenActiveLaneSideClass A initialCode)

abbrev ProfiledOpenWitnessedTableQuery :=
  ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode

abbrev ProfiledOpenWitnessedTableBaseLive :=
  ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
    (ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin basis
      initialCode)

abbrev ProfiledOpenWitnessedTableBaseValid :=
  ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
    initialCode
    (OneClass := ProfiledOpenActiveLaneSideClass A initialCode)
    (TwoClass := ProfiledOpenActiveLaneSideClass A initialCode)

abbrev ProfiledOpenWitnessedTableControlStep :=
  ProfiledOpenFixedSidewiseControlStep A initialCode

/-! ## Honest witnessed initialization -/

/-- The initial public candidate is tagged by the literal supplied semantic
state, not by a separately chosen representative. -/
noncomputable def profiledOpenActiveLaneWitnessedInitialCandidate
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenWitnessedTableCandidate A initialCode :=
  ((profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
      state,
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
      state),
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode state)

noncomputable def profiledOpenActiveLaneWitnessedInitialCandidateSet
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    Finset (ProfiledOpenWitnessedTableCandidate A initialCode) :=
  {profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
    initialCode state}

omit [Inhabited I] in
theorem profiledOpenActiveLaneWitnessedInitialCandidate_mem
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode state ∈
      profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
        initialCode state := by
  simp [profiledOpenActiveLaneWitnessedInitialCandidateSet]

omit [Inhabited I] in
theorem profiledOpenActiveLaneWitnessedInitialCandidate_live
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode
      (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode state).2
      (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode state).1 := by
  constructor
  · exact ⟨state, rfl, rfl⟩
  · exact ⟨state, rfl, rfl, rfl⟩

/-! ## One-arrow witnessed table -/

variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- The finite rational table with both source-family and literal-child tag
provenance. -/
theorem exists_profiledOpenActiveLaneWitnessedFixedPolicyTable
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitialRoot : initialRoot.state A policy = policy.run []) :
    ∃ package : FixedPolicyRelationalCandidateTablePackage A policy
        (SourceAwareRelationalLive
          (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis
            initialCode))
        (SourceAwareRelationalCandidateValid
          (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis
            initialCode))
        (sourceAwareRelationalExactEdge
          (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy
            hwin basis initialCode))
        (sourceAwareRelationalControlStep
          (ProfiledOpenWitnessedTableControlStep A initialCode))
        initialRoot
        (sourceAwareRelationalCandidatesEncode
          (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin
            basis initialCode state))
        (sourceAwareRelationalCandidateEncode
          (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin
            basis initialCode state)),
      ∀ query : Nat → ProfiledOpenWitnessedTableQuery A initialCode,
        Nonempty
          (SourceAwareRelationalFamilyExactThread
            (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy
              hwin basis initialCode)
            (ProfiledOpenWitnessedTableControlStep A initialCode)
            (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin
              basis initialCode state)
            (package.branch.moveAt query) query) := by
  let initial :=
    profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
      initialCode state
  let actual :=
    profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
      initialCode state
  have hmem : sourceAwareRelationalCandidateEncode actual ∈
      sourceAwareRelationalCandidatesEncode initial :=
    mem_sourceAwareRelationalCandidatesEncode initial actual
      (profiledOpenActiveLaneWitnessedInitialCandidate_mem A strategy hwin
        basis initialCode state)
  have hlive : SourceAwareRelationalLive
      (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode)
      (sourceAwareRelationalCandidateEncode actual).2
      (sourceAwareRelationalCandidateEncode actual).1 := by
    refine ⟨rfl, ?_⟩
    exact profiledOpenActiveLaneWitnessedInitialCandidate_live A strategy hwin
      basis initialCode state
  obtain ⟨package, hthreads⟩ :=
    exists_fixedPolicyRelationalCandidateTable A policy
      (SourceAwareRelationalLive
        (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode))
      (SourceAwareRelationalCandidateValid
        (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis
          initialCode))
      (sourceAwareRelationalExactEdge
        (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
          basis initialCode))
      (sourceAwareRelationalControlStep
        (ProfiledOpenWitnessedTableControlStep A initialCode))
      initialRoot hinitialRoot
      (sourceAwareRelationalCandidatesEncode initial)
      (sourceAwareRelationalCandidateEncode actual) hmem hlive
      (profiledOpenFixedSidewiseWitnessedReanchored_encodedLiveSuccessorCoverage
        A strategy hwin basis initialCode)
      (profiledOpenActiveLaneWitnessed_encodedCommonMoveExists A strategy hwin
        basis initialCode)
  refine ⟨package, ?_⟩
  intro query
  obtain ⟨thread⟩ := hthreads query
  exact ⟨sourceAwareRelationalFamilyExactThreadDecode
    (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin basis
      initialCode)
    (ProfiledOpenWitnessedTableControlStep A initialCode) initial
    (package.branch.moveAt query) query thread⟩

/-! ## Explicit finite branch recurrence -/

/-- Short name for the package type returned above. -/
abbrev ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy) :=
  FixedPolicyRelationalCandidateTablePackage A policy
    (SourceAwareRelationalLive
      (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode))
    (SourceAwareRelationalCandidateValid
      (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode))
    (sourceAwareRelationalExactEdge
      (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
        basis initialCode))
    (sourceAwareRelationalControlStep
      (ProfiledOpenWitnessedTableControlStep A initialCode))
    initialRoot
    (sourceAwareRelationalCandidatesEncode
      (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
        initialCode state))
    (sourceAwareRelationalCandidateEncode
      (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode state))

/-- The entire public recurrence state: finite rational-table control plus the
literal finite encoded candidate set. -/
abbrev ProfiledOpenActiveLaneWitnessedBranchState
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot) :=
  package.table.toTransitionRationalTree.Control ×
    Finset (RelationalFamilyCandidate
      (ProfiledOpenWitnessedTableFamily A initialCode)
      (ProfiledOpenWitnessedTableDescriptor A initialCode))

/-- Initial finite public recurrence state. -/
noncomputable def profiledOpenActiveLaneWitnessedBranchInitial
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot) :
    ProfiledOpenActiveLaneWitnessedBranchState A strategy hwin basis
      initialCode policy state initialRoot package :=
  (package.table.toTransitionRationalTree.initial,
    sourceAwareRelationalCandidatesEncode
      (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
        initialCode state))

/-- Total finite recurrence.  The `none` branch is the generic unreachable
completion.  On every branch containing the live actual candidate, the table
label is proved to be `some bank`. -/
noncomputable def profiledOpenActiveLaneWitnessedBranchStep
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot)
    (current : ProfiledOpenActiveLaneWitnessedBranchState A strategy hwin basis
      initialCode policy state initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    ProfiledOpenActiveLaneWitnessedBranchState A strategy hwin basis
      initialCode policy state initialRoot package :=
  match package.table.toTransitionRationalTree.labelOf current.1 with
  | none => current
  | some bank =>
      let nextCandidates := relationalFamilySaturation
        (sourceAwareRelationalExactEdge
          (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy
            hwin basis initialCode))
        (sourceAwareRelationalControlStep
          (ProfiledOpenWitnessedTableControlStep A initialCode))
        current.2 bank query
      (package.table.toTransitionRationalTree.step current.1
        (query, nextCandidates), nextCandidates)

/-- The public recurrence state reached by the proof-side branch at depth
`n`.  Unlike the branch cursor, this value contains no semantic actual
candidate. -/
noncomputable def profiledOpenActiveLaneWitnessedBranchStateAt
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (n : Nat) : ProfiledOpenActiveLaneWitnessedBranchState A strategy hwin
      basis initialCode policy state initialRoot package :=
  (package.table.toTransitionRationalTree.controlAt
      (package.branch.cursorAt query n).node,
    (package.branch.cursorAt query n).candidates)

/-- The table label at the explicit branch control is its genuine common
bank, never the unreachable `none` fallback. -/
theorem profiledOpenActiveLaneWitnessedBranchStateAt_label
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (n : Nat) :
    package.table.toTransitionRationalTree.labelOf
        (profiledOpenActiveLaneWitnessedBranchStateAt A strategy hwin basis
          initialCode policy state initialRoot package query n).1 =
      some (package.branch.moveAt query n) := by
  change package.table.toTransitionRationalTree.labeledTree
      (package.branch.cursorAt query n).node =
    some (package.branch.moveAt query n)
  rw [← package.branch_tree_eq]
  exact RelationalCandidateTreeBranchPackage.Cursor.tree_eq_some_move
    package.branch (package.branch.cursorAt query n)

@[simp] theorem profiledOpenActiveLaneWitnessedBranchStateAt_zero
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode) :
    profiledOpenActiveLaneWitnessedBranchStateAt A strategy hwin basis
        initialCode policy state initialRoot package query 0 =
      profiledOpenActiveLaneWitnessedBranchInitial A strategy hwin basis
        initialCode policy state initialRoot package := by
  rfl

/-- The explicit finite state follows the total recurrence exactly. -/
theorem profiledOpenActiveLaneWitnessedBranchStateAt_succ
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (n : Nat) :
    profiledOpenActiveLaneWitnessedBranchStateAt A strategy hwin basis
        initialCode policy state initialRoot package query (n + 1) =
      profiledOpenActiveLaneWitnessedBranchStep A strategy hwin basis
        initialCode policy state initialRoot package
        (profiledOpenActiveLaneWitnessedBranchStateAt A strategy hwin basis
          initialCode policy state initialRoot package query n)
        (query n) := by
  rw [profiledOpenActiveLaneWitnessedBranchStep,
    profiledOpenActiveLaneWitnessedBranchStateAt_label]
  apply Prod.ext
  · simp only [profiledOpenActiveLaneWitnessedBranchStateAt,
      FixedPolicyRelationalCandidateTablePackage.branch,
      RelationalCandidateTreeBranchPackage.cursorAt,
      RelationalCandidateTreeBranchPackage.Cursor.step]
    rw [TransitionRationalTree.controlAt_append]
    rfl
  · rfl

/-- The candidate-set component is exposed without the rational-table
control. -/
theorem profiledOpenActiveLaneWitnessedBranchStateAt_candidates
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (n : Nat) :
    (profiledOpenActiveLaneWitnessedBranchStateAt A strategy hwin basis
      initialCode policy state initialRoot package query n).2 =
      (package.branch.cursorAt query n).candidates :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
