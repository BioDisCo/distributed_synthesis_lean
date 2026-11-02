/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenDelayedBoundarySplit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenancePhysicalAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedConcreteEpochAdapter
import DistributedSynthesis.Formalizations.Lemma.LemRelationalCandidateCursorReachability

/-!
# A provenance-policy fork at a delayed simultaneous boundary

The last strict letter of a homogeneous run has to be retained for one
letter.  At the following simultaneous round there are two exact cuts:

* the direct cut scans the retained letter and closes on the simultaneous
  inputs;
* the repeated-side cut closes on the retained strict letter and then takes
  one real zero-open direction on the simultaneous inputs.

Both alternatives below start from the *same* provenance-policy cursor.  The
second alternative is two literal steps of that same cursor recurrence; it is
not assembled from independently accepted words.  Further consecutive
simultaneous rounds advance both alternatives by one real zero-open query.
Thus the two cursors remain genuine continuations of their common prefix until
the next strict side selects one of them.

This is proof-side finite branching.  Neither local process is told the side,
row, lineage, or which alternative is retained.

The cursor-only constructors below use the canonical `(default, row)` pivot
and prove tag realizability and exact table recurrence only.  They do **not**
prove that this lineage remains active after root deduplication.  The
unconditional integration interface is the finite distinguished-state module,
which takes explicit active pivots; the default-pivot cursor layer is retained
as a proof/debug adapter.
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

private abbrev ForkQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private abbrev ForkBaseDescriptor :=
  ProfiledOpenWitnessedTableBaseDescriptor A initialCode

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable (point : ProfiledOpenIndexedOptionalControlledSemanticState A
  strategy hwin basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy
  hwin basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev ForkCursor := package.branch.Cursor

/-! ## Literal summarized queries at the current policy cursor -/

/-- The base descriptor carried by the cursor's literal source candidate. -/
def profiledOpenProvenancePolicyCursorDescriptor
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    ForkBaseDescriptor A initialCode :=
  cursor.actual.2.2

/-- Finish one retained finite strict accumulator at the supplied current
inputs.  Its move coordinate is read from the literal current policy
candidate, so the tag cannot silently fall into the mismatched-move fallback.
The reachable query bank is copied unchanged.  This constructor establishes
realizability, not activity of its canonical default pivot. -/
noncomputable def profiledOpenProvenancePolicyDirectionQueryOfCursor
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ForkQuery A initialCode)
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (currentInputOne : In₁) (currentInputTwo : In₂) :
    ForkQuery A initialCode :=
  let descriptor := profiledOpenProvenancePolicyCursorDescriptor A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      cursor
  let pivot : IndexedLineageCandidate I := (default, row)
  let direction := profiledOpenPhysicalStrictHistoryDirection history pivot
    pivot currentInputOne currentInputTwo
  profiledOpenWitnessedTableQueryWithDirection A initialCode carriedQuery side
    ⟨descriptor.moveIdentity,
      profiledOpenIndexedDirectionSummarize A descriptor.code
        descriptor.moveIdentity direction⟩

@[simp] theorem profiledOpenProvenancePolicyDirectionQueryOfCursor_side
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ForkQuery A initialCode)
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (currentInputOne : In₁) (currentInputTwo : In₂) :
    (profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package cursor
      carriedQuery side row history currentInputOne currentInputTwo).1.1.1 =
        side := by
  rfl

@[simp] theorem profiledOpenProvenancePolicyDirectionQueryOfCursor_move
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ForkQuery A initialCode)
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (currentInputOne : In₁) (currentInputTwo : In₂) :
    (profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package cursor
      carriedQuery side row history currentInputOne currentInputTwo).1.2.1 =
        (profiledOpenProvenancePolicyCursorDescriptor A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          cursor).moveIdentity := by
  rfl

/-- The summarized tag advertised by the delayed query has its literal raw
strict-history realization at the current code and move. -/
theorem profiledOpenProvenancePolicyDirectionQueryOfCursor_realizableAt
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ForkQuery A initialCode)
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (currentInputOne : In₁) (currentInputTwo : In₂) :
    let descriptor := profiledOpenProvenancePolicyCursorDescriptor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        cursor
    (profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package cursor
      carriedQuery side row history currentInputOne currentInputTwo).1.2
        |>.RealizableAt A descriptor.code descriptor.moveIdentity := by
  dsimp only [profiledOpenProvenancePolicyDirectionQueryOfCursor,
    profiledOpenProvenancePolicyCursorDescriptor]
  let pivot : IndexedLineageCandidate I := (default, row)
  let direction := profiledOpenPhysicalStrictHistoryDirection history pivot
    pivot currentInputOne currentInputTwo
  refine ⟨{
    move_eq := rfl
    raw := direction
    summary_eq := ?_ }⟩
  rfl

/-! ## Every literal query advances the same retagged recurrence -/

/-- The generic cursor step exposes the model's policy-retagged exact edge,
not merely membership of its target in a saturation. -/
theorem profiledOpenProvenancePolicyCursorStep_exact
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : ForkQuery A initialCode) :
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy cursor.actual.2.1 cursor.actual.2.2
      (cursor.move package.branch) query
      (cursor.step package.branch query).actual.1
      (cursor.step package.branch query).actual.2.2 := by
  exact (cursor.target_good package.branch query).1.1

/-- Therefore every cursor query is one transition of the single selected
provenance code policy. -/
theorem profiledOpenProvenancePolicyCursorStep_policySuccessor
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : ForkQuery A initialCode) :
    (cursor.step package.branch query).actual.2.2.1 =
      codePolicy.successor cursor.actual.2.2.1 query.1.2 := by
  exact
    profiledOpenProvenancePolicyRetaggedExactEdge_policySuccessor A strategy
      hwin basis initialCode codePolicy
      (profiledOpenProvenancePolicyCursorStep_exact A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package cursor
        query)

/-- One real zero-open query at an arbitrary cursor.  The query bank is the
empty-word bank for that cursor's literal move, while the physical inputs are
retained in the finite direction tag.  The finite active-pivot wrapper in
`LemPairedProfiledOpenProvenanceFiniteDelayedBoundaryFork` is required for the
unconditional stream. -/
noncomputable def profiledOpenProvenancePolicyZeroOpenQueryOfCursor
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) : ForkQuery A initialCode :=
  profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package cursor
    (profiledOpenWitnessedInitialQueryForMove A initialCode
      (profiledOpenProvenancePolicyCursorDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        cursor).moveIdentity)
    side row [] inputOne inputTwo

/-- A zero-open query has an honest empty-past realization at the current
policy state. -/
theorem profiledOpenProvenancePolicyZeroOpenQueryOfCursor_realizableAt
    (cursor : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide) (row : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor := profiledOpenProvenancePolicyCursorDescriptor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        cursor
    (profiledOpenProvenancePolicyZeroOpenQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package cursor side
      row inputOne inputTwo).1.2.RealizableAt A descriptor.code
        descriptor.moveIdentity := by
  exact profiledOpenProvenancePolicyDirectionQueryOfCursor_realizableAt A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
    package cursor
    (profiledOpenWitnessedInitialQueryForMove A initialCode
      (profiledOpenProvenancePolicyCursorDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        cursor).moveIdentity)
    side row [] inputOne inputTwo

/-! ## The delayed two-way boundary fork -/

/-- The two genuine cursor continuations at the first simultaneous round.
`direct` consumes the whole strict run and closes at the simultaneous inputs.
`repeated` first consumes the strict prefix ending at the held last letter and
then consumes the simultaneous inputs as a zero-open direction. -/
structure ProfiledOpenProvenancePolicyDelayedBoundaryFork
    (source : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) where
  oldSide : IndexedLineageSide
  oldRow : PairedEntryRow
  strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
    (In₁ := In₁) (In₂ := In₂))
  lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
    (In₁ := In₁) (In₂ := In₂)
  bothInputOne : In₁
  bothInputTwo : In₂
  /-- Query bank after the strict prefix but before the retained last
  letter. -/
  prefixQuery : ForkQuery A initialCode
  /-- Query bank after also scanning the retained last strict letter. -/
  fullQuery : ForkQuery A initialCode
  directQuery : ForkQuery A initialCode
  strictCloseQuery : ForkQuery A initialCode
  middle : ForkCursor A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package
  zeroOpenQuery : ForkQuery A initialCode
  direct : ForkCursor A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package
  repeated : ForkCursor A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package
  directQuery_eq : directQuery =
    profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
      fullQuery oldSide oldRow (strictPrefix ++ [lastStrict]) bothInputOne
        bothInputTwo
  strictCloseQuery_eq : strictCloseQuery =
    profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
      prefixQuery oldSide oldRow strictPrefix lastStrict.inputOne
        lastStrict.inputTwo
  middle_eq : middle = source.step package.branch strictCloseQuery
  zeroOpenQuery_eq : zeroOpenQuery =
    profiledOpenProvenancePolicyZeroOpenQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package middle
      oldSide.other .first bothInputOne bothInputTwo
  direct_eq : direct = source.step package.branch directQuery
  repeated_eq : repeated = middle.step package.branch zeroOpenQuery

/-- Construct the fork definitionally from one common policy cursor. -/
noncomputable def profiledOpenProvenancePolicyDelayedBoundaryFork
    (source : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ForkQuery A initialCode)
    (oldSide : IndexedLineageSide) (oldRow : PairedEntryRow)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    ProfiledOpenProvenancePolicyDelayedBoundaryFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source := by
  let directQuery :=
    profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
      fullQuery oldSide oldRow (strictPrefix ++ [lastStrict]) bothInputOne
        bothInputTwo
  let strictCloseQuery :=
    profiledOpenProvenancePolicyDirectionQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
      prefixQuery oldSide oldRow strictPrefix lastStrict.inputOne
        lastStrict.inputTwo
  let middle := source.step package.branch strictCloseQuery
  let zeroOpenQuery :=
    profiledOpenProvenancePolicyZeroOpenQueryOfCursor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package middle
      oldSide.other .first bothInputOne bothInputTwo
  exact {
    oldSide := oldSide
    oldRow := oldRow
    strictPrefix := strictPrefix
    lastStrict := lastStrict
    bothInputOne := bothInputOne
    bothInputTwo := bothInputTwo
    prefixQuery := prefixQuery
    fullQuery := fullQuery
    directQuery := directQuery
    strictCloseQuery := strictCloseQuery
    middle := middle
    zeroOpenQuery := zeroOpenQuery
    direct := source.step package.branch directQuery
    repeated := middle.step package.branch zeroOpenQuery
    directQuery_eq := rfl
    strictCloseQuery_eq := rfl
    middle_eq := rfl
    zeroOpenQuery_eq := rfl
    direct_eq := rfl
    repeated_eq := rfl }

/-- The direct and two-query endpoints are both finite continuations of the
same literal source cursor. -/
noncomputable def
    ProfiledOpenProvenancePolicyDelayedBoundaryFork.toCursorFork
    {source : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyDelayedBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
      source) :
    package.branch.CursorFork source := by
  refine {
    left := fork.direct
    right := fork.repeated
    left_reachable := ?_
    right_reachable := ?_ }
  · rw [fork.direct_eq]
    exact package.branch.cursorReachableFrom_step
      (package.branch.cursorReachableFrom_refl source) fork.directQuery
  · rw [fork.repeated_eq, fork.middle_eq]
    exact package.branch.cursorReachableFrom_step
      (package.branch.cursorReachableFrom_step
        (package.branch.cursorReachableFrom_refl source)
        fork.strictCloseQuery)
      fork.zeroOpenQuery

/-- Selecting either delayed cut keeps one genuine cursor prefix.  This is
the no-mosaic fact needed when the first later strict side resolves the fork. -/
theorem
    ProfiledOpenProvenancePolicyDelayedBoundaryFork.select_reachable
    {source : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyDelayedBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
      source)
    (chooseRepeated : Bool) :
    package.branch.CursorReachableFrom source
      (fork.toCursorFork A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package |>.select package.branch
          chooseRepeated) :=
  (fork.toCursorFork A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package).select_reachable package.branch chooseRepeated

/-- Both arms are made only from ordinary table-covered exact edges. -/
theorem ProfiledOpenProvenancePolicyDelayedBoundaryFork.exact
    {source : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyDelayedBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
      source) :
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy source.actual.2.1 source.actual.2.2
        (source.move package.branch) fork.directQuery fork.direct.actual.1
          fork.direct.actual.2.2 ∧
      ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy source.actual.2.1 source.actual.2.2
        (source.move package.branch) fork.strictCloseQuery
          fork.middle.actual.1 fork.middle.actual.2.2 ∧
      ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy fork.middle.actual.2.1
          fork.middle.actual.2.2 (fork.middle.move package.branch)
          fork.zeroOpenQuery fork.repeated.actual.1
          fork.repeated.actual.2.2 := by
  constructor
  · rw [fork.direct_eq]
    exact profiledOpenProvenancePolicyCursorStep_exact A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
        fork.directQuery
  · constructor
    · rw [fork.middle_eq]
      exact profiledOpenProvenancePolicyCursorStep_exact A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
          fork.strictCloseQuery
    · rw [fork.repeated_eq]
      exact profiledOpenProvenancePolicyCursorStep_exact A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
          fork.middle fork.zeroOpenQuery

/-- The two arms advance the same selected code policy by one and two
successors respectively. -/
theorem ProfiledOpenProvenancePolicyDelayedBoundaryFork.policySuccessors
    {source : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyDelayedBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
      source) :
    fork.direct.actual.2.2.1 =
        codePolicy.successor source.actual.2.2.1 fork.directQuery.1.2 ∧
      fork.middle.actual.2.2.1 =
        codePolicy.successor source.actual.2.2.1
          fork.strictCloseQuery.1.2 ∧
      fork.repeated.actual.2.2.1 =
        codePolicy.successor fork.middle.actual.2.2.1
          fork.zeroOpenQuery.1.2 := by
  constructor
  · rw [fork.direct_eq]
    exact profiledOpenProvenancePolicyCursorStep_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      source fork.directQuery
  · constructor
    · rw [fork.middle_eq]
      exact profiledOpenProvenancePolicyCursorStep_policySuccessor A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        source fork.strictCloseQuery
    · rw [fork.repeated_eq]
      exact profiledOpenProvenancePolicyCursorStep_policySuccessor A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.middle fork.zeroOpenQuery

/-! ## Any finite run of consecutive simultaneous rounds -/

/-- Two opposite-orientation cursor continuations of one genuine prefix.
The cursors are proof witnesses; the finite runtime projection is the
distinguished raw state (public table state plus actual encoded candidate). -/
structure ProfiledOpenProvenancePolicyBoundaryCursorFork
    (root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) where
  first : ForkCursor A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package
  second : ForkCursor A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package
  firstSide : IndexedLineageSide
  secondSide : IndexedLineageSide
  sides : secondSide = firstSide.other
  first_reachable : package.branch.CursorReachableFrom root first
  second_reachable : package.branch.CursorReachableFrom root second

/-- The one-step/two-step delayed split yields two opposite pending sides. -/
noncomputable def
    ProfiledOpenProvenancePolicyDelayedBoundaryFork.toBoundaryCursorFork
    {source : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyDelayedBoundaryFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
      source) :
    ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source :=
  { first := fork.direct
    second := fork.repeated
    firstSide := fork.oldSide.other
    secondSide := fork.oldSide
    sides := by cases fork.oldSide <;> rfl
    first_reachable :=
      (fork.toCursorFork A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package).left_reachable
    second_reachable :=
      (fork.toCursorFork A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package).right_reachable }

/-- One further actual simultaneous round advances each arm by one real
zero-open query in row `both`.  The arms remain opposite, and both remain
extensions of the original common cursor. -/
noncomputable def ProfiledOpenProvenancePolicyBoundaryCursorFork.advanceBoth
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package root := by
  let firstQuery := profiledOpenProvenancePolicyZeroOpenQueryOfCursor A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
    package fork.first fork.firstSide .both inputOne inputTwo
  let secondQuery := profiledOpenProvenancePolicyZeroOpenQueryOfCursor A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
    package fork.second fork.secondSide .both inputOne inputTwo
  exact {
    first := fork.first.step package.branch firstQuery
    second := fork.second.step package.branch secondQuery
    firstSide := fork.firstSide.other
    secondSide := fork.secondSide.other
    sides := by rw [fork.sides]
    first_reachable := package.branch.cursorReachableFrom_step
      fork.first_reachable firstQuery
    second_reachable := package.branch.cursorReachableFrom_step
      fork.second_reachable secondQuery }

/-- Every arm-step used for an additional simultaneous round is an ordinary
policy-retagged exact edge and advances the same rational code policy. -/
theorem
    ProfiledOpenProvenancePolicyBoundaryCursorFork.advanceBoth_exact
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (inputOne : In₁) (inputTwo : In₂) :
    let firstQuery := profiledOpenProvenancePolicyZeroOpenQueryOfCursor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.first fork.firstSide .both inputOne inputTwo
    let secondQuery := profiledOpenProvenancePolicyZeroOpenQueryOfCursor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second fork.secondSide .both inputOne inputTwo
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy fork.first.actual.2.1 fork.first.actual.2.2
        (fork.first.move package.branch) firstQuery
        (fork.advanceBoth A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo).first.actual.1
        (fork.advanceBoth A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo).first.actual.2.2
      ∧
      ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy fork.second.actual.2.1 fork.second.actual.2.2
        (fork.second.move package.branch) secondQuery
        (fork.advanceBoth A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo).second.actual.1
        (fork.advanceBoth A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo).second.actual.2.2 := by
  dsimp only
  constructor
  · exact profiledOpenProvenancePolicyCursorStep_exact A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package fork.first _
  · exact profiledOpenProvenancePolicyCursorStep_exact A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package fork.second _

/-- The two exact arm-steps used by `advanceBoth` are transitions of the
same selected rational code policy.  This is stated separately from
`advanceBoth_exact` so that a finite raw-state implementation can use the
policy recurrence without retaining either proof-only cursor. -/
theorem
    ProfiledOpenProvenancePolicyBoundaryCursorFork.advanceBoth_policySuccessors
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (inputOne : In₁) (inputTwo : In₂) :
    let firstQuery := profiledOpenProvenancePolicyZeroOpenQueryOfCursor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.first fork.firstSide .both inputOne inputTwo
    let secondQuery := profiledOpenProvenancePolicyZeroOpenQueryOfCursor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package fork.second fork.secondSide .both inputOne inputTwo
    (fork.advanceBoth A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package inputOne inputTwo).first.actual.2.2.1 =
      codePolicy.successor fork.first.actual.2.2.1 firstQuery.1.2 ∧
    (fork.advanceBoth A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package inputOne inputTwo).second.actual.2.2.1 =
      codePolicy.successor fork.second.actual.2.2.1 secondQuery.1.2 := by
  dsimp only
  constructor
  · exact profiledOpenProvenancePolicyCursorStep_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      fork.first _
  · exact profiledOpenProvenancePolicyCursorStep_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      fork.second _

/-- Iterate the paired zero-open recurrence through an arbitrary finite run
of additional simultaneous rounds.  The common root remains fixed in the
result type, so both returned cursors are certified genuine continuations of
the same pre-boundary prefix. -/
noncomputable def
    ProfiledOpenProvenancePolicyBoundaryCursorFork.advanceBothRun
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package} :
    ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package root →
      List (In₁ × In₂) →
      ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package root
  | fork, [] => fork
  | fork, inputs :: rest =>
      advanceBothRun
        (fork.advanceBoth A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputs.1 inputs.2) rest

@[simp] theorem
    ProfiledOpenProvenancePolicyBoundaryCursorFork.advanceBothRun_nil
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root) :
    fork.advanceBothRun A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package [] = fork := by
  rfl

@[simp] theorem
    ProfiledOpenProvenancePolicyBoundaryCursorFork.advanceBothRun_cons
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (inputs : In₁ × In₂) (rest : List (In₁ × In₂)) :
    fork.advanceBothRun A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package (inputs :: rest) =
      (fork.advanceBoth A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package inputs.1 inputs.2).advanceBothRun
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package rest := by
  rfl

/-- Whichever strict side arrives next, exactly one arm has that pending
orientation.  Selecting it preserves reachability from the common cursor. -/
noncomputable def ProfiledOpenProvenancePolicyBoundaryCursorFork.selectSide
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (side : IndexedLineageSide) :
    ForkCursor A strategy hwin basis initialCode codePolicy fixedPolicy point
      initialRoot package :=
  if side = fork.firstSide then fork.first else fork.second

theorem
    ProfiledOpenProvenancePolicyBoundaryCursorFork.selectSide_reachable
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (side : IndexedLineageSide) :
    package.branch.CursorReachableFrom root
      (fork.selectSide A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package side) := by
  unfold ProfiledOpenProvenancePolicyBoundaryCursorFork.selectSide
  split
  · exact fork.first_reachable
  · exact fork.second_reachable

theorem ProfiledOpenProvenancePolicyBoundaryCursorFork.selectSide_side
    {root : ForkCursor A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package}
    (fork : ProfiledOpenProvenancePolicyBoundaryCursorFork A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package root)
    (side : IndexedLineageSide) :
    (if side = fork.firstSide then fork.firstSide else fork.secondSide) =
      side := by
  by_cases hside : side = fork.firstSide
  · simp [hside]
  · simp only [hside, ↓reduceIte]
    rw [fork.sides]
    cases hfirst : fork.firstSide <;> cases hrequested : side <;>
      simp_all [IndexedLineageSide.other]

/-!
The finite strict-gap construction above deliberately does not claim the two
endpoint regimes.  A leading run of simultaneous rounds needs the guarded
initial pair (there is no preceding strict direction to split), while an
infinite simultaneous tail needs one coherent infinite zero-open arm.  Both
are separate acceptance cases; neither is discharged by assuming a later
strict resolver.
-/

end

end DetParityAutomaton

end DistributedSynthesis
