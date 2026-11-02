/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDelayedBoundaryFork
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedRawState

/-!
# The finite provenance state at a delayed simultaneous boundary

The cursor construction proves that the direct cut and the
strict-close/zero-open cut are coherent continuations of one table branch.
A cursor itself is not runtime state: it contains its complete query node.
This file repeats exactly that recurrence on
`ProfiledOpenProvenancePolicyDistinguishedState`, whose data are only the
finite public table state and one finite actual candidate.

Strict histories are represented by their finite direction accumulators.
Their realizability by a concrete history is a proposition and is therefore
proof-erased.  Closing and zero-open tags are summarized at the current
actual descriptor's code, not at the initial code.  The side carried below is
also proof-side global data; neither process is told a leader, orientation,
or selected arm.
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
variable (point : ProfiledOpenIndexedOptionalControlledSemanticState A
  strategy hwin basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy
  hwin basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev FiniteForkState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev FiniteForkQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private abbrev FiniteForkDescriptor :=
  ProfiledOpenWitnessedTableBaseDescriptor A initialCode

/-- The finite accumulator type at the actual descriptor of `current`. -/
abbrev ProfiledOpenProvenancePolicyCurrentAccumulator
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :=
  ProfiledOpenIndexedDirectionAccumulator A
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package
      current).moveIdentity

/-- Both supplied pivots are present in the current finite code.  This is the
explicit guard needed by the defensive successor: realizability of a tag
alone does not imply that either pivot lineage survived root deduplication. -/
def ProfiledOpenProvenancePolicyPivotsActiveAt
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (rightPivot leftPivot : IndexedLineageCandidate I) : Prop :=
  let code :=
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current).code
  code.rightSlots rightPivot.1 ≠ none ∧ code.leftSlots leftPivot.1 ≠ none

/-- A finite active pivot pair.  Carrying this subtype is the safe interface
for an executable global witness; the two activity proofs are erased. -/
structure ProfiledOpenProvenancePolicyActivePivotsAt
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) where
  rightPivot : IndexedLineageCandidate I
  leftPivot : IndexedLineageCandidate I
  active : ProfiledOpenProvenancePolicyPivotsActiveAt A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package current
      rightPivot leftPivot

noncomputable instance profiledOpenProvenancePolicyActivePivotsAt_fintype
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    Fintype (ProfiledOpenProvenancePolicyActivePivotsAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current) := by
  classical
  let encode := fun pivots :
      ProfiledOpenProvenancePolicyActivePivotsAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current =>
    (pivots.rightPivot, pivots.leftPivot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    simp_all [encode])

/-- The side-specific condition actually needed to keep the cross-swapped
carrier nonempty.  Only the proof-side current side is tested; no local
process learns it. -/
def ProfiledOpenProvenancePolicyActiveReflexivePivotAt
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide) (pivot : IndexedLineageCandidate I) : Prop :=
  let code :=
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current).code
  match side with
  | .right =>
      code.rightSlots pivot.1 ≠ none ∧
        code.rightPattern.RowFunctionalAt pivot ∧
        code.rightPattern pivot pivot = true
  | .left =>
      code.leftSlots pivot.1 ≠ none ∧
        code.leftPattern.RowFunctionalAt pivot ∧
        code.leftPattern pivot pivot = true

/-- One finite, side-specific active reflexive pivot. -/
structure ProfiledOpenProvenancePolicyActivePivotAt
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide) where
  pivot : IndexedLineageCandidate I
  active : ProfiledOpenProvenancePolicyActiveReflexivePivotAt A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      side pivot

noncomputable instance profiledOpenProvenancePolicyActivePivotAt_fintype
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide) :
    Fintype (ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
        side) := by
  classical
  let encode := fun pivot :
      ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
          side => pivot.pivot
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    simp_all [encode])

/-- A current-code accumulator is honest when it is the fold of some finite
strict history.  The history is a proof witness and is not stored in the
finite state. -/
def ProfiledOpenProvenancePolicyCurrentAccumulator.Realizable
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (accumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current) : Prop :=
  ∃ history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)),
    profiledOpenPhysicalStrictAccumulatorRun A
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).moveIdentity history = accumulator

/-- Close one already-folded strict accumulator at the current physical
inputs.  Only the finite query bank is copied from `carriedQuery`. -/
noncomputable def profiledOpenProvenancePolicyClosingQueryOfState
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : FiniteForkQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (accumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current)
    (inputOne : In₁) (inputTwo : In₂) : FiniteForkQuery A initialCode :=
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  profiledOpenWitnessedTableQueryWithDirection A initialCode carriedQuery side
    ((ProfiledOpenPhysicalDirectionAccumulatorCandidate.mk
      descriptor.moveIdentity accumulator).finish A rightPivot leftPivot inputOne
        inputTwo)

@[simp] theorem profiledOpenProvenancePolicyClosingQueryOfState_side
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : FiniteForkQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (accumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledOpenProvenancePolicyClosingQueryOfState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
      carriedQuery side rightPivot leftPivot accumulator inputOne inputTwo
      ).1.1.1 = side := by
  rfl

@[simp] theorem profiledOpenProvenancePolicyClosingQueryOfState_move
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : FiniteForkQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (accumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledOpenProvenancePolicyClosingQueryOfState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
      carriedQuery side rightPivot leftPivot accumulator inputOne inputTwo
      ).1.2.1 =
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).moveIdentity := by
  rfl

/-- An honestly folded accumulator produces an honestly realizable closing
tag at the *current* descriptor code. -/
theorem profiledOpenProvenancePolicyClosingQueryOfState_realizableAt
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : FiniteForkQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (accumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current)
    (inputOne : In₁) (inputTwo : In₂)
    (hreal : ProfiledOpenProvenancePolicyCurrentAccumulator.Realizable A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current accumulator) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    (profiledOpenProvenancePolicyClosingQueryOfState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
      carriedQuery side rightPivot leftPivot accumulator inputOne inputTwo
      ).1.2.RealizableAt A descriptor.code descriptor.moveIdentity := by
  obtain ⟨history, hhistory⟩ := hreal
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  refine ⟨{
    move_eq := rfl
    raw := profiledOpenPhysicalStrictHistoryDirection history rightPivot
      leftPivot inputOne inputTwo
    summary_eq := ?_ }⟩
  simp only [profiledOpenProvenancePolicyClosingQueryOfState,
    profiledOpenWitnessedTableQueryWithDirection_tag,
    ProfiledOpenPhysicalDirectionAccumulatorCandidate.finish, descriptor]
  rw [← hhistory]
  rw [profiledOpenPhysicalStrictAccumulatorRun_eq_scan]
  exact (profiledOpenIndexedDirectionAccumulator_finish_scan A descriptor.code
    descriptor.moveIdentity
      (profiledOpenPhysicalStrictHistoryDirection history rightPivot leftPivot
        inputOne inputTwo)).symm

/-- The fresh empty accumulator is realizable by the empty strict history. -/
theorem profiledOpenProvenancePolicyCurrentAccumulator_initial_realizable
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    ProfiledOpenProvenancePolicyCurrentAccumulator.Realizable A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      (profiledOpenIndexedDirectionAccumulatorInitial A
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).moveIdentity) := by
  exact ⟨[], rfl⟩

/-- Realizability is closed under one strict accumulator step at the same
current code. -/
theorem profiledOpenProvenancePolicyCurrentAccumulator_step_realizable
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (accumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current)
    (letter : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂))
    (hreal : ProfiledOpenProvenancePolicyCurrentAccumulator.Realizable A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current accumulator) :
    ProfiledOpenProvenancePolicyCurrentAccumulator.Realizable A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      (profiledOpenPhysicalStrictAccumulatorStep A
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).moveIdentity accumulator letter) := by
  obtain ⟨history, hhistory⟩ := hreal
  refine ⟨history ++ [letter], ?_⟩
  rw [profiledOpenPhysicalStrictAccumulatorRun,
    profiledOpenPhysicalStrictAccumulatorRunFrom_append]
  simp only [profiledOpenPhysicalStrictAccumulatorRunFrom]
  rw [← profiledOpenPhysicalStrictAccumulatorRun]
  rw [hhistory]

/-- One real zero-open query on the finite distinguished state. -/
noncomputable def profiledOpenProvenancePolicyZeroOpenQueryOfState
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) : FiniteForkQuery A initialCode :=
  profiledOpenProvenancePolicyClosingQueryOfState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package current
    (profiledOpenWitnessedInitialQueryForMove A initialCode
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        current).moveIdentity)
    side rightPivot leftPivot
    (profiledOpenIndexedDirectionAccumulatorInitial A
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        current).moveIdentity)
    inputOne inputTwo

/-- A finite-state zero-open query has the literal empty-past realization. -/
theorem profiledOpenProvenancePolicyZeroOpenQueryOfState_realizableAt
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    (profiledOpenProvenancePolicyZeroOpenQueryOfState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side
      rightPivot leftPivot inputOne inputTwo).1.2.RealizableAt A descriptor.code
        descriptor.moveIdentity := by
  exact profiledOpenProvenancePolicyClosingQueryOfState_realizableAt A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
    current _ side rightPivot leftPivot _ inputOne inputTwo
      (profiledOpenProvenancePolicyCurrentAccumulator_initial_realizable A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current)

/-! ## Finite distinguished paths -/

/-- Execute a finite query word on the finite distinguished recurrence. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedRun :
    FiniteForkState A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package →
      List (FiniteForkQuery A initialCode) →
      FiniteForkState A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package
  | current, [] => current
  | current, query :: rest =>
      profiledOpenProvenancePolicyDistinguishedRun
        (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package current
          query) rest

@[simp] theorem profiledOpenProvenancePolicyDistinguishedRun_nil
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    profiledOpenProvenancePolicyDistinguishedRun A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current [] =
        current := by
  rfl

@[simp] theorem profiledOpenProvenancePolicyDistinguishedRun_cons
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : FiniteForkQuery A initialCode)
    (rest : List (FiniteForkQuery A initialCode)) :
    profiledOpenProvenancePolicyDistinguishedRun A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
          (query :: rest) =
      profiledOpenProvenancePolicyDistinguishedRun A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package current
            query) rest := by
  rfl

theorem profiledOpenProvenancePolicyDistinguishedRun_append
    (current : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (first second : List (FiniteForkQuery A initialCode)) :
    profiledOpenProvenancePolicyDistinguishedRun A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
          (first ++ second) =
      profiledOpenProvenancePolicyDistinguishedRun A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedRun A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package current
            first) second := by
  induction first generalizing current with
  | nil => rfl
  | cons query rest ih =>
      simp only [List.cons_append,
        profiledOpenProvenancePolicyDistinguishedRun_cons]
      exact ih _

/-- Common-prefix reachability without retaining a cursor node.  Its query
word is a proposition witness, hence erased from the finite data. -/
def ProfiledOpenProvenancePolicyDistinguishedReachableFrom
    (source target : FiniteForkState A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package) : Prop :=
  ∃ queries : List (FiniteForkQuery A initialCode),
    profiledOpenProvenancePolicyDistinguishedRun A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
        queries = target

theorem profiledOpenProvenancePolicyDistinguishedReachableFrom_refl
    (source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    ProfiledOpenProvenancePolicyDistinguishedReachableFrom A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        source := by
  exact ⟨[], rfl⟩

theorem profiledOpenProvenancePolicyDistinguishedReachableFrom_step
    {source current : FiniteForkState A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package}
    (hcurrent : ProfiledOpenProvenancePolicyDistinguishedReachableFrom A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package source current)
    (query : FiniteForkQuery A initialCode) :
    ProfiledOpenProvenancePolicyDistinguishedReachableFrom A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package current
          query) := by
  obtain ⟨queries, hqueries⟩ := hcurrent
  refine ⟨queries ++ [query], ?_⟩
  rw [profiledOpenProvenancePolicyDistinguishedRun_append, hqueries]
  rfl

/-! ## The finite delayed two-way fork -/

/-- Direct versus strict-close/zero-open continuations represented entirely
by finite distinguished states and finite queries. -/
structure ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork
    (source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) where
  oldSide : IndexedLineageSide
  sourceRightPivot : IndexedLineageCandidate I
  sourceLeftPivot : IndexedLineageCandidate I
  middleRightPivot : IndexedLineageCandidate I
  middleLeftPivot : IndexedLineageCandidate I
  directQuery : FiniteForkQuery A initialCode
  strictCloseQuery : FiniteForkQuery A initialCode
  zeroOpenQuery : FiniteForkQuery A initialCode
  middle : FiniteForkState A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package
  direct : FiniteForkState A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package
  repeated : FiniteForkState A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package
  middle_eq : middle =
    profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
        strictCloseQuery
  direct_eq : direct =
    profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
        directQuery
  repeated_eq : repeated =
    profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package middle
        zeroOpenQuery

/-- The pivot condition which the eventual physical-gap stream must preserve.
It is deliberately separate from tag realizability. -/
def ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork.PivotsActive
    {source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source) : Prop :=
  ProfiledOpenProvenancePolicyPivotsActiveAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package source
      fork.sourceRightPivot fork.sourceLeftPivot ∧
    ProfiledOpenProvenancePolicyPivotsActiveAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package fork.middle
      fork.middleRightPivot fork.middleLeftPivot

/-- Minimal side-specific pivot invariant for the delayed split.  The source
closes on `oldSide`; the middle zero-open step runs on `oldSide.other`. -/
def
    ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork.ActiveLineagePivots
    {source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source) : Prop :=
  (match fork.oldSide with
   | .right =>
      ProfiledOpenProvenancePolicyActiveReflexivePivotAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
          .right fork.sourceRightPivot
   | .left =>
      ProfiledOpenProvenancePolicyActiveReflexivePivotAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
          .left fork.sourceLeftPivot) ∧
  (match fork.oldSide.other with
   | .right =>
      ProfiledOpenProvenancePolicyActiveReflexivePivotAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.middle
          .right fork.middleRightPivot
   | .left =>
      ProfiledOpenProvenancePolicyActiveReflexivePivotAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.middle
          .left fork.middleLeftPivot)

noncomputable instance
    profiledOpenProvenancePolicyFiniteDelayedBoundaryFork_fintype
    (source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    Fintype (ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source) := by
  classical
  let encode := fun fork :
      ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          source =>
    (fork.oldSide, fork.sourceRightPivot, fork.sourceLeftPivot,
      fork.middleRightPivot, fork.middleLeftPivot, fork.directQuery,
      fork.strictCloseQuery, fork.zeroOpenQuery, fork.middle, fork.direct,
      fork.repeated)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    simp_all [encode])

/-- Build the finite fork from the accumulator before the retained last
strict letter.  The direct arm first folds that one letter.  The repeated arm
closes the old direction and then uses a fresh empty accumulator at the
middle state's new code. -/
noncomputable def profiledOpenProvenancePolicyFiniteDelayedBoundaryFork
    (source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : FiniteForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourceRightPivot sourceLeftPivot : IndexedLineageCandidate I)
    (middleRightPivot middleLeftPivot : IndexedLineageCandidate I)
    (prefixAccumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package source)
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
  let fullAccumulator := profiledOpenPhysicalStrictAccumulatorStep A
    descriptor.code descriptor.moveIdentity prefixAccumulator lastStrict
  let directQuery := profiledOpenProvenancePolicyClosingQueryOfState A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source fullQuery oldSide sourceRightPivot sourceLeftPivot fullAccumulator
        bothInputOne bothInputTwo
  let strictCloseQuery :=
    profiledOpenProvenancePolicyClosingQueryOfState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
        prefixQuery oldSide sourceRightPivot sourceLeftPivot prefixAccumulator
          lastStrict.inputOne lastStrict.inputTwo
  let middle := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package source
      strictCloseQuery
  let zeroOpenQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package middle oldSide.other middleRightPivot middleLeftPivot
        bothInputOne bothInputTwo
  exact {
    oldSide := oldSide
    sourceRightPivot := sourceRightPivot
    sourceLeftPivot := sourceLeftPivot
    middleRightPivot := middleRightPivot
    middleLeftPivot := middleLeftPivot
    directQuery := directQuery
    strictCloseQuery := strictCloseQuery
    zeroOpenQuery := zeroOpenQuery
    middle := middle
    direct := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        directQuery
    repeated := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package middle
        zeroOpenQuery
    middle_eq := rfl
    direct_eq := rfl
    repeated_eq := rfl }

/-- All three queries created by the finite constructor have honest raw
realizations.  The first two use the source code; the zero-open query uses
the post-close middle code. -/
theorem profiledOpenProvenancePolicyFiniteDelayedBoundaryFork_realizableAt
    (source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : FiniteForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourceRightPivot sourceLeftPivot : IndexedLineageCandidate I)
    (middleRightPivot middleLeftPivot : IndexedLineageCandidate I)
    (prefixAccumulator : ProfiledOpenProvenancePolicyCurrentAccumulator A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package source)
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I) (In₁ := In₁)
      (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂)
    (hprefix : ProfiledOpenProvenancePolicyCurrentAccumulator.Realizable A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package source prefixAccumulator) :
    let fork := profiledOpenProvenancePolicyFiniteDelayedBoundaryFork A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package source prefixQuery fullQuery oldSide sourceRightPivot
          sourceLeftPivot middleRightPivot middleLeftPivot prefixAccumulator
            lastStrict bothInputOne bothInputTwo
    let sourceDescriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
    let middleDescriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.middle
    fork.directQuery.1.2.RealizableAt A sourceDescriptor.code
        sourceDescriptor.moveIdentity ∧
      fork.strictCloseQuery.1.2.RealizableAt A sourceDescriptor.code
        sourceDescriptor.moveIdentity ∧
      fork.zeroOpenQuery.1.2.RealizableAt A middleDescriptor.code
        middleDescriptor.moveIdentity := by
  dsimp only [profiledOpenProvenancePolicyFiniteDelayedBoundaryFork]
  constructor
  · apply profiledOpenProvenancePolicyClosingQueryOfState_realizableAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package
    exact profiledOpenProvenancePolicyCurrentAccumulator_step_realizable A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package source prefixAccumulator lastStrict hprefix
  · constructor
    · exact profiledOpenProvenancePolicyClosingQueryOfState_realizableAt A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package source prefixQuery oldSide sourceRightPivot sourceLeftPivot
          prefixAccumulator lastStrict.inputOne lastStrict.inputTwo hprefix
    · exact profiledOpenProvenancePolicyZeroOpenQueryOfState_realizableAt A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package _ _ _ _ _ _

/-- Every endpoint is reached by the one finite recurrence, and both arms
share the literal source state. -/
theorem ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork.reachable
    {source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source) :
    ProfiledOpenProvenancePolicyDistinguishedReachableFrom A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        source fork.direct ∧
      ProfiledOpenProvenancePolicyDistinguishedReachableFrom A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        source fork.repeated := by
  constructor
  · rw [fork.direct_eq]
    exact profiledOpenProvenancePolicyDistinguishedReachableFrom_step A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package
        (profiledOpenProvenancePolicyDistinguishedReachableFrom_refl A strategy
          hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source) fork.directQuery
  · rw [fork.repeated_eq, fork.middle_eq]
    exact profiledOpenProvenancePolicyDistinguishedReachableFrom_step A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package
        (profiledOpenProvenancePolicyDistinguishedReachableFrom_step A strategy
          hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package
            (profiledOpenProvenancePolicyDistinguishedReachableFrom_refl A
              strategy hwin basis initialCode codePolicy fixedPolicy point
              initialRoot package source) fork.strictCloseQuery)
        fork.zeroOpenQuery

/-- The direct, strict-close, and zero-open finite steps are literal edges of
the same provenance-retagged table. -/
theorem ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork.exact
    {source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source) :
    (let next := fork.direct
     ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy
      ((profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
        ).2.1)
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        source)
      (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source)
      fork.directQuery
      (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next).1
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package next))
      ∧
    (let next := fork.middle
     ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy
      ((profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
        ).2.1)
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        source)
      (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source)
      fork.strictCloseQuery
      (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next).1
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package next))
      ∧
    (let next := fork.repeated
     ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy
      ((profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.middle
        ).2.1)
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.middle)
      (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.middle)
      fork.zeroOpenQuery
      (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next).1
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package next)) := by
  constructor
  · rw [fork.direct_eq]
    exact profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        fork.directQuery
  · constructor
    · rw [fork.middle_eq]
      exact profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package source
          fork.strictCloseQuery
    · rw [fork.repeated_eq]
      exact profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          fork.middle fork.zeroOpenQuery

/-! ## Consecutive simultaneous rounds on the finite fork -/

/-- Two opposite pending alternatives, both reached from one finite common
source.  The reachability witnesses are propositions and store no query list
at runtime. -/
structure ProfiledOpenProvenancePolicyFiniteBoundaryFork
    (root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) where
  first : FiniteForkState A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package
  second : FiniteForkState A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package
  firstSide : IndexedLineageSide
  secondSide : IndexedLineageSide
  sides : secondSide = firstSide.other
  first_reachable :
    ProfiledOpenProvenancePolicyDistinguishedReachableFrom A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root
        first
  second_reachable :
    ProfiledOpenProvenancePolicyDistinguishedReachableFrom A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root
        second

noncomputable instance profiledOpenProvenancePolicyFiniteBoundaryFork_fintype
    (root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    Fintype (ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root) :=
  by
  classical
  let encode := fun fork :
      ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package root =>
    (fork.first, fork.second, fork.firstSide, fork.secondSide)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    simp_all [encode])

/-- Forget the construction details of the first delayed split while keeping
its common finite source and opposite pending sides. -/
noncomputable def
    ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork.toBoundaryFork
    {source : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source) :
    ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source :=
  { first := fork.direct
    second := fork.repeated
    firstSide := fork.oldSide.other
    secondSide := fork.oldSide
    sides := by cases fork.oldSide <;> rfl
    first_reachable := fork.reachable A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package |>.1
    second_reachable := fork.reachable A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package |>.2 }

/-- Explicit active-pivot guard for one further paired zero-open step.  These
pivots are finite global witness data, not process-local leader information. -/
def ProfiledOpenProvenancePolicyFiniteBoundaryFork.PivotsActive
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (firstRightPivot firstLeftPivot secondRightPivot secondLeftPivot :
      IndexedLineageCandidate I) : Prop :=
  ProfiledOpenProvenancePolicyPivotsActiveAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package fork.first
        firstRightPivot firstLeftPivot ∧
    ProfiledOpenProvenancePolicyPivotsActiveAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package fork.second
        secondRightPivot secondLeftPivot

/-- Advance both alternatives through one actual simultaneous round.  Each
arm takes one real zero-open query at its own current descriptor code. -/
noncomputable def ProfiledOpenProvenancePolicyFiniteBoundaryFork.advanceBoth
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (firstRightPivot firstLeftPivot secondRightPivot secondLeftPivot :
      IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package root := by
  let firstQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      fork.first fork.firstSide firstRightPivot firstLeftPivot inputOne inputTwo
  let secondQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second fork.secondSide secondRightPivot secondLeftPivot
        inputOne inputTwo
  exact {
    first := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package fork.first
        firstQuery
    second := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.second secondQuery
    firstSide := fork.firstSide.other
    secondSide := fork.secondSide.other
    sides := by rw [fork.sides]
    first_reachable :=
      profiledOpenProvenancePolicyDistinguishedReachableFrom_step A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          fork.first_reachable firstQuery
    second_reachable :=
      profiledOpenProvenancePolicyDistinguishedReachableFrom_step A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          fork.second_reachable secondQuery }

/-- Both finite arm queries used by `advanceBoth` are honest empty-past tags
at their respective current codes. -/
theorem
    ProfiledOpenProvenancePolicyFiniteBoundaryFork.advanceBoth_realizableAt
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (firstRightPivot firstLeftPivot secondRightPivot secondLeftPivot :
      IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let firstDescriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.first
    let secondDescriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.second
    let firstQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.first fork.firstSide firstRightPivot firstLeftPivot inputOne
        inputTwo
    let secondQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second fork.secondSide secondRightPivot secondLeftPivot
        inputOne inputTwo
    firstQuery.1.2.RealizableAt A firstDescriptor.code
        firstDescriptor.moveIdentity ∧
      secondQuery.1.2.RealizableAt A secondDescriptor.code
        secondDescriptor.moveIdentity := by
  constructor
  · exact profiledOpenProvenancePolicyZeroOpenQueryOfState_realizableAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.first fork.firstSide firstRightPivot firstLeftPivot inputOne
        inputTwo
  · exact profiledOpenProvenancePolicyZeroOpenQueryOfState_realizableAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second fork.secondSide secondRightPivot secondLeftPivot
        inputOne inputTwo

/-- Each additional simultaneous round advances both arms by one exact
retagged edge and hence by the same installed code-policy recurrence. -/
theorem ProfiledOpenProvenancePolicyFiniteBoundaryFork.advanceBoth_exact
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (firstRightPivot firstLeftPivot secondRightPivot secondLeftPivot :
      IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let firstQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.first fork.firstSide firstRightPivot firstLeftPivot inputOne
        inputTwo
    let secondQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second fork.secondSide secondRightPivot secondLeftPivot
        inputOne inputTwo
    let next := fork.advanceBoth A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package firstRightPivot firstLeftPivot
        secondRightPivot secondLeftPivot inputOne inputTwo
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy
        ((profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          fork.first).2.1)
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          fork.first)
        (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          fork.first)
        firstQuery
        (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          next.first).1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          next.first) ∧
      ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy
        ((profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          fork.second).2.1)
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          fork.second)
        (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          fork.second)
        secondQuery
        (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          next.second).1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          next.second) := by
  dsimp only
  constructor
  · exact profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.first _
  · exact profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.second _

/-- Code-policy coordinates of the two finite arm steps. -/
theorem
    ProfiledOpenProvenancePolicyFiniteBoundaryFork.advanceBoth_policySuccessors
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (firstRightPivot firstLeftPivot secondRightPivot secondLeftPivot :
      IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let firstQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.first fork.firstSide firstRightPivot firstLeftPivot inputOne
        inputTwo
    let secondQuery := profiledOpenProvenancePolicyZeroOpenQueryOfState A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second fork.secondSide secondRightPivot secondLeftPivot
        inputOne inputTwo
    let next := fork.advanceBoth A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package firstRightPivot firstLeftPivot
        secondRightPivot secondLeftPivot inputOne inputTwo
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        next.first).1 =
      codePolicy.successor
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          fork.first).1 firstQuery.1.2 ∧
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        next.second).1 =
      codePolicy.successor
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          fork.second).1 secondQuery.1.2 := by
  dsimp only
  constructor
  · exact profiledOpenProvenancePolicyDistinguishedStep_policySuccessor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.first _
  · exact profiledOpenProvenancePolicyDistinguishedStep_policySuccessor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second _

/-- Safe active-pivot wrapper around `advanceBoth`.  This is the interface
the synchronized finite stream should call. -/
noncomputable def
    ProfiledOpenProvenancePolicyFiniteBoundaryFork.advanceBothActive
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (firstPivots : ProfiledOpenProvenancePolicyActivePivotsAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.first)
    (secondPivots : ProfiledOpenProvenancePolicyActivePivotsAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.second)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package root :=
  fork.advanceBoth A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package firstPivots.rightPivot firstPivots.leftPivot
      secondPivots.rightPivot secondPivots.leftPivot inputOne inputTwo

/-- Minimal safe wrapper: one active reflexive pivot on each arm's current
proof-side is enough.  The same finite candidate is placed in the unused
opposite pivot coordinate; that coordinate is not assumed active. -/
noncomputable def
    ProfiledOpenProvenancePolicyFiniteBoundaryFork.advanceBothActiveLineage
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (firstPivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.first fork.firstSide)
    (secondPivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.second fork.secondSide)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package root :=
  fork.advanceBoth A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package firstPivot.pivot firstPivot.pivot
      secondPivot.pivot secondPivot.pivot inputOne inputTwo

/-- A later strict side selects one whole finite arm.  There is no prefix
mosaic and no process-local test of the side. -/
noncomputable def ProfiledOpenProvenancePolicyFiniteBoundaryFork.selectSide
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (side : IndexedLineageSide) :
    FiniteForkState A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package :=
  if side = fork.firstSide then fork.first else fork.second

theorem
    ProfiledOpenProvenancePolicyFiniteBoundaryFork.selectSide_reachable
    {root : FiniteForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyFiniteBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (side : IndexedLineageSide) :
    ProfiledOpenProvenancePolicyDistinguishedReachableFrom A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root
        (fork.selectSide A strategy hwin basis initialCode codePolicy fixedPolicy
          point initialRoot package side) := by
  unfold ProfiledOpenProvenancePolicyFiniteBoundaryFork.selectSide
  split
  · exact fork.first_reachable
  · exact fork.second_reachable

end

end DetParityAutomaton

end DistributedSynthesis
