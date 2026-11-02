/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Library.Distributed.PhysicalControllers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedFixedPolicyTable
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefLocalPresentationReadback
import DistributedSynthesis.Formalizations.Lemma.LemSourceAwareRelationalFamilySaturation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOperationalReachableQuery
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedReanchoredRowProjection

/-!
# A physical-round carrier for the witnessed branch table

The witnessed fixed-policy table advances once per completed epoch,
whereas the model advances one physical communication graph per round.  This
file gives the small finite adapter between those two clocks.

The local part is deliberately an ordinary pair of finite controllers.  A
no-receive transition sees only the process's own controller and input; a
receive transition sees exactly the two delivered controllers and the two
inputs.  In particular it is never passed the proof-side active epoch, a
strict-leader flag, or a hidden shape bit.

The global proof machine additionally stores the witnessed branch state, its
current optional table label, the accumulated boundary query, and a finite
proof-side within-epoch phase.  These fields are allowed in the global machine;
they are hidden by the belief construction before a distributed strategy is
read back.  The two Boolean fields are *only* the actual previous-round
receive events.  They are definitionally recomputed from the public graph and
must not be confused with the permanently hidden bit.

No output-uniformity or acceptance premise is bundled into the adapter.  The
former remains the explicit `ReachableBeliefsUniform` theorem obligation and
the latter remains a theorem about the generated trace.  At the bottom of the
file, a reachable output collision is packaged as a kernel-checkable
fail-fast certificate.  This is important: a permanently lost bit may retain
unbounded strategic significance, so distinct compatible states are never
silently merged.
-/

namespace DistributedSynthesis

universe u v x y b k q p c₁ c₂

namespace DetParityAutomaton

/-- The physical epoch boundary used by `LemEpochArenaCuts`: precisely a
`both` round closes the current epoch.  An opposite strict round is a direct
reversal *inside* the epoch and is handled by the recut/reversed phase; it is
not an epoch boundary. -/
def profiledOpenPhysicalClosesEpoch : Graph → Bool
  | .left => false
  | .right => false
  | .both => true

@[simp] theorem profiledOpenPhysicalClosesEpoch_left :
    profiledOpenPhysicalClosesEpoch .left = false :=
  rfl

@[simp] theorem profiledOpenPhysicalClosesEpoch_right :
    profiledOpenPhysicalClosesEpoch .right = false :=
  rfl

@[simp] theorem profiledOpenPhysicalClosesEpoch_both :
    profiledOpenPhysicalClosesEpoch .both = true :=
  rfl

theorem profiledOpenPhysicalClosesEpoch_eq_true_iff (graph : Graph) :
    profiledOpenPhysicalClosesEpoch graph = true ↔ graph = .both := by
  cases graph <;> simp

theorem profiledOpenPhysicalClosesEpoch_eq_false_iff (graph : Graph) :
    profiledOpenPhysicalClosesEpoch graph = false ↔ graph ≠ .both := by
  cases graph <;> simp

/-! ## Exact finite adapter map -/

/-- The finite proof-side map required to couple a physical controller to an
epoch branch.  `accumulateQuery` and `advancePhase` record one physical round.
If that round is `both`, the resulting query is fed literally to the branch
step and the two restart maps initialize the next epoch.

These functions are proof-machine functions.  They may inspect the proof-side
branch, current optional bank label, and within-epoch phase.  They are never
used as local transition maps and hence reveal none of these values to a
process.

`Phase` is deliberately abstract.  A concrete instantiation owes the genuine
recut invariant: `advancePhase` must track ordinary blocks, reversed blocks,
and arbitrary re-reversals until the next `both` round.  In particular it may
not be instantiated by merely toggling an `IndexedLineageSide`, and it may not
discard either value of the permanently hidden bit. -/
structure FiniteEpochQueryAdapter
    (In₁ : Type u) (In₂ : Type v)
    (Branch : Type b) (Bank : Type k) (Query : Type q) (Phase : Type p)
    {Out₁ : Type x} {Out₂ : Type y}
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂) where
  initialQuery : Query
  initialPhase : Phase
  accumulateQuery :
    Branch → Option Bank → Phase → Bool → Bool → Query →
      controller.OneControl → controller.TwoControl →
        EnvironmentRound In₁ In₂ →
          controller.OneControl → controller.TwoControl → Query
  advancePhase :
    Branch → Option Bank → Phase → Bool → Bool → Query →
      controller.OneControl → controller.TwoControl →
        EnvironmentRound In₁ In₂ →
          controller.OneControl → controller.TwoControl → Phase
  restartQuery :
    Branch → Option Bank → Phase → Bool → Bool → Query → Query
  restartPhase :
    Branch → Option Bank → Phase → Bool → Bool → Query → Phase

/-- Finite global state connecting the physical and epoch clocks.  The bank
is stored explicitly so a later invariant can state that it is the current
table label without repeatedly unfolding the rational tree. -/
structure FiniteEpochPhysicalState
    (Branch : Type b) (Bank : Type k) (Query : Type q) (Phase : Type p)
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂) where
  branch : Branch
  bank : Option Bank
  query : Query
  phase : Phase
  receivedOne : Bool
  receivedTwo : Bool
  one : controller.OneControl
  two : controller.TwoControl

noncomputable instance finiteEpochPhysicalState_fintype
    {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Fintype Branch] [Fintype Bank] [Fintype Query] [Fintype Phase]
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂) :
    Fintype (FiniteEpochPhysicalState Branch Bank Query Phase controller) := by
  classical
  let encode := fun s : FiniteEpochPhysicalState Branch Bank Query Phase controller =>
    (s.branch, s.bank, s.query, s.phase, s.receivedOne, s.receivedTwo,
      s.one, s.two)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨lb, lk, lq, ls, lr1, lr2, l1, l2⟩
    rcases right with ⟨rb, rk, rq, rs, rr1, rr2, r1, r2⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl)

namespace FiniteEpochPhysicalState

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
variable (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂)
variable (adapter : FiniteEpochQueryAdapter In₁ In₂ Branch Bank Query Phase
  controller)
variable (label : Branch → Option Bank)
variable (branchStep : Branch → Query → Branch)

/-- Query after consuming the current physical round, before a possible
epoch restart.  This is the *literal* query passed to `branchStep`. -/
def completedQuery
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂) : Query :=
  let next := controller.advanceControls (state.one, state.two) round
  adapter.accumulateQuery state.branch state.bank state.phase
    state.receivedOne state.receivedTwo state.query state.one state.two round
      next.1 next.2

/-- Within-epoch phase after consuming the current physical round, before a
possible restart at the `both` boundary. -/
def completedPhase
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂) : Phase :=
  let next := controller.advanceControls (state.one, state.two) round
  adapter.advancePhase state.branch state.bank state.phase
    state.receivedOne state.receivedTwo state.query state.one state.two round
      next.1 next.2

/-- The exact global physical transition.  Branch and bank are frozen on
nonclosing rounds.  On a closing round, the completed query is consumed once,
the new bank is exactly the label of the new branch, and the query accumulator
is restarted once. -/
def step
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂) :
    FiniteEpochPhysicalState Branch Bank Query Phase controller :=
  let nextControls := controller.advanceControls (state.one, state.two) round
  let completed := state.completedQuery controller adapter round
  let completedPhase := state.completedPhase controller adapter round
  let closes := profiledOpenPhysicalClosesEpoch round.graph
  let nextBranch := if closes then branchStep state.branch completed
    else state.branch
  let nextBank := if closes then label nextBranch else state.bank
  let receivedOne := physicalReceivedOne round.graph
  let receivedTwo := physicalReceivedTwo round.graph
  let nextQuery := if closes then
      adapter.restartQuery nextBranch nextBank completedPhase receivedOne receivedTwo
        completed
    else completed
  let nextPhase := if closes then
      adapter.restartPhase nextBranch nextBank completedPhase receivedOne receivedTwo
        completed
    else completedPhase
  { branch := nextBranch
    bank := nextBank
    query := nextQuery
    phase := nextPhase
    receivedOne := receivedOne
    receivedTwo := receivedTwo
    one := nextControls.1
    two := nextControls.2 }

@[simp] theorem step_receivedOne
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂) :
    (state.step controller adapter label branchStep round).receivedOne =
      physicalReceivedOne round.graph :=
  rfl

@[simp] theorem step_receivedTwo
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂) :
    (state.step controller adapter label branchStep round).receivedTwo =
      physicalReceivedTwo round.graph :=
  rfl

@[simp] theorem step_one
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂) :
    (state.step controller adapter label branchStep round).one =
      (controller.advanceControls (state.one, state.two) round).1 :=
  rfl

@[simp] theorem step_two
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂) :
    (state.step controller adapter label branchStep round).two =
      (controller.advanceControls (state.one, state.two) round).2 :=
  rfl

theorem step_branch_of_not_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = false) :
    (state.step controller adapter label branchStep round).branch =
      state.branch := by
  simp [step, hclose]

theorem step_bank_of_not_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = false) :
    (state.step controller adapter label branchStep round).bank = state.bank := by
  simp [step, hclose]

theorem step_query_of_not_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = false) :
    (state.step controller adapter label branchStep round).query =
      state.completedQuery controller adapter round := by
  simp [step, hclose]

theorem step_phase_of_not_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = false) :
    (state.step controller adapter label branchStep round).phase =
      state.completedPhase controller adapter round := by
  simp [step, hclose]

theorem step_branch_of_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = true) :
    (state.step controller adapter label branchStep round).branch =
      branchStep state.branch
        (state.completedQuery controller adapter round) := by
  simp [step, hclose]

theorem step_bank_of_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = true) :
    (state.step controller adapter label branchStep round).bank =
      label (branchStep state.branch
        (state.completedQuery controller adapter round)) := by
  simp [step, hclose]

theorem step_query_of_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = true) :
    (state.step controller adapter label branchStep round).query =
      adapter.restartQuery
        (branchStep state.branch
          (state.completedQuery controller adapter round))
        (label (branchStep state.branch
          (state.completedQuery controller adapter round)))
        (state.completedPhase controller adapter round)
        (physicalReceivedOne round.graph)
        (physicalReceivedTwo round.graph)
        (state.completedQuery controller adapter round) := by
  simp [step, hclose]

theorem step_phase_of_closes
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (round : EnvironmentRound In₁ In₂)
    (hclose : profiledOpenPhysicalClosesEpoch round.graph = true) :
    (state.step controller adapter label branchStep round).phase =
      adapter.restartPhase
        (branchStep state.branch
          (state.completedQuery controller adapter round))
        (label (branchStep state.branch
          (state.completedQuery controller adapter round)))
        (state.completedPhase controller adapter round)
        (physicalReceivedOne round.graph)
        (physicalReceivedTwo round.graph)
        (state.completedQuery controller adapter round) := by
  simp [step, hclose]

end FiniteEpochPhysicalState

/-! ## Packaging as the finite global machine -/

/-- The finite global machine generated by the transparent physical and epoch
maps.  Its Moore outputs are *only* the outputs of the two local controls.
Thus any later proof that these outputs come from the selected fixed values
must establish that fact at the local controller interface; the proof-side
branch fields cannot affect the emitted output by definition. -/
noncomputable def finiteEpochPhysicalGlobalMachine
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
    [Fintype Branch] [Fintype Bank] [Fintype Query] [Fintype Phase]
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂)
    (adapter : FiniteEpochQueryAdapter In₁ In₂ Branch Bank Query Phase
      controller)
    (initialBranch : Branch)
    (label : Branch → Option Bank) (branchStep : Branch → Query → Branch) :
    FiniteGlobalRoundMachine In₁ In₂ where
  State := FiniteEpochPhysicalState Branch Bank Query Phase controller
  stateFinite := inferInstance
  initial :=
    { branch := initialBranch
      bank := label initialBranch
      query := adapter.initialQuery
      phase := adapter.initialPhase
      receivedOne := false
      receivedTwo := false
      one := controller.initialOne
      two := controller.initialTwo }
  step := FiniteEpochPhysicalState.step controller adapter label branchStep

/-- Process-one Moore output of the packaged global machine. -/
def finiteEpochPhysicalOutputOne
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂) :
    FiniteEpochPhysicalState Branch Bank Query Phase controller → Out₁ :=
  fun state => controller.outputOne state.one

/-- Process-two Moore output. -/
def finiteEpochPhysicalOutputTwo
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂) :
    FiniteEpochPhysicalState Branch Bank Query Phase controller → Out₂ :=
  fun state => controller.outputTwo state.two

/-! ## Automatic graph-blind local presentation -/

/-- The physical controller is already a local presentation of the generated
global machine.  Representation forgets every proof-side coordinate and
retains only the corresponding actual local control.

This theorem is the decisive locality check.  Its four simulation fields are
proved definitionally from `noRecvOne`, `noRecvTwo`, `recvOne`, and `recvTwo`.
Consequently no `ReachableBeliefsUniform` premise is needed: the generic local
presentation theorem derives it. -/
noncomputable def finiteEpochPhysicalLocalPresentation
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
    [Fintype Branch] [Fintype Bank] [Fintype Query] [Fintype Phase]
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂)
    (adapter : FiniteEpochQueryAdapter In₁ In₂ Branch Bank Query Phase
      controller)
    (initialBranch : Branch)
    (label : Branch → Option Bank) (branchStep : Branch → Query → Branch) :
    (finiteEpochPhysicalGlobalMachine controller adapter initialBranch label
        branchStep).LocalPresentation
      (finiteEpochPhysicalOutputOne controller)
      (finiteEpochPhysicalOutputTwo controller) where
  ControlOne := controller.OneControl
  ControlTwo := controller.TwoControl
  initialOne := controller.initialOne
  initialTwo := controller.initialTwo
  localOutputOne := controller.outputOne
  localOutputTwo := controller.outputTwo
  noRecvOne := controller.noRecvOne
  noRecvTwo := controller.noRecvTwo
  recv := fun one two inputOne inputTwo =>
    (controller.recvOne one inputOne two inputTwo,
      controller.recvTwo two inputTwo one inputOne)
  RepOne := fun control state => control = state.one
  RepTwo := fun control state => control = state.two
  initialRepOne := rfl
  initialRepTwo := rfl
  outputOne_eq := by
    intro control state hrep
    simpa [finiteEpochPhysicalOutputOne] using
      (congrArg controller.outputOne hrep).symm
  outputTwo_eq := by
    intro control state hrep
    simpa [finiteEpochPhysicalOutputTwo] using
      (congrArg controller.outputTwo hrep).symm
  noRecvOne_rep := by
    intro control state hrep inputOne hidden
    subst control
    rfl
  noRecvTwo_rep := by
    intro control state hrep inputTwo hidden
    subst control
    rfl
  recvOne_rep := by
    intro one two state hone htwo inputOne inputTwo graph hgraph
    subst one
    subst two
    rcases hgraph with rfl | rfl <;> rfl
  recvTwo_rep := by
    intro one two state hone htwo inputOne inputTwo graph hgraph
    subst one
    subst two
    rcases hgraph with rfl | rfl <;> rfl

/-- Therefore output uniformity is a theorem of the adapter maps, not an
additional construction hypothesis. -/
theorem finiteEpochPhysical_reachableBeliefsUniform
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Fintype In₁] [Fintype In₂]
    {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
    [Fintype Branch] [Fintype Bank] [Fintype Query] [Fintype Phase]
    (controller : FinitePairedPhysicalController In₁ In₂ Out₁ Out₂)
    (adapter : FiniteEpochQueryAdapter In₁ In₂ Branch Bank Query Phase
      controller)
    (initialBranch : Branch)
    (label : Branch → Option Bank) (branchStep : Branch → Query → Branch) :
    (finiteEpochPhysicalGlobalMachine controller adapter initialBranch
      label branchStep).ReachableBeliefsUniform
        (finiteEpochPhysicalOutputOne controller)
        (finiteEpochPhysicalOutputTwo controller) :=
  FiniteGlobalRoundMachine.LocalPresentation.reachableBeliefsUniform
    _ _ _
    (finiteEpochPhysicalLocalPresentation controller adapter initialBranch
      label branchStep)

/-! ## The witnessed distinguished-candidate recurrence -/

universe i s

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
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
  (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A policy)
variable
  (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
    strategy hwin basis initialCode policy state initialRoot)

/-- Encoded candidate type literally carried by the source-aware table. -/
abbrev ProfiledOpenWitnessedEncodedCandidate :=
  RelationalFamilyCandidate
    (ProfiledOpenWitnessedTableFamily A initialCode)
    (ProfiledOpenWitnessedTableDescriptor A initialCode)

/-- The finite public branch state together with one proof-side distinguished
actual candidate.  Unlike the generic cursor, this raw state stores no tree
node or unbounded query history. -/
abbrev ProfiledOpenWitnessedDistinguishedRawState :=
  ProfiledOpenActiveLaneWitnessedBranchState A strategy hwin basis
      initialCode policy state initialRoot package ×
    ProfiledOpenWitnessedEncodedCandidate A initialCode

/-- Read the finite public recurrence state represented by a generic branch
cursor.  The cursor's unbounded node occurs only in this proof-side map. -/
noncomputable def profiledOpenWitnessedBranchStateOfCursor
    (cursor : package.branch.Cursor) :
    ProfiledOpenActiveLaneWitnessedBranchState A strategy hwin basis
      initialCode policy state initialRoot package :=
  (package.table.toTransitionRationalTree.controlAt cursor.node,
    cursor.candidates)

/-- A raw finite distinguished state is represented when some proof-only
cursor has exactly its public state and actual candidate.  The existential
node is a proposition, not runtime data. -/
def ProfiledOpenWitnessedDistinguishedRepresented
    (current : ProfiledOpenWitnessedDistinguishedRawState A strategy hwin basis
      initialCode policy state initialRoot package) : Prop :=
  ∃ cursor : package.branch.Cursor,
    profiledOpenWitnessedBranchStateOfCursor A strategy hwin basis initialCode
        policy state initialRoot package cursor = current.1 ∧
      cursor.actual = current.2

/-- The actual finite distinguished-state type.  It is a subtype of a finite
raw product; the unbounded cursor witness is proof-erased. -/
abbrev ProfiledOpenWitnessedDistinguishedState :=
  { current : ProfiledOpenWitnessedDistinguishedRawState A strategy hwin basis
      initialCode policy state initialRoot package //
    ProfiledOpenWitnessedDistinguishedRepresented A strategy hwin basis
      initialCode policy state initialRoot package current }

noncomputable instance profiledOpenWitnessedDistinguishedState_fintype :
    Fintype (ProfiledOpenWitnessedDistinguishedState A strategy hwin basis
      initialCode policy state initialRoot package) :=
  Fintype.ofFinite _

/-- Initial distinguished state.  It is represented by the table branch's
initial cursor, definitionally. -/
noncomputable def profiledOpenWitnessedDistinguishedInitial :
    ProfiledOpenWitnessedDistinguishedState A strategy hwin basis initialCode
      policy state initialRoot package := by
  let cursor := package.branch.initialCursor
  refine ⟨(profiledOpenActiveLaneWitnessedBranchInitial A strategy hwin basis
      initialCode policy state initialRoot package, cursor.actual), ?_⟩
  exact ⟨cursor, rfl, rfl⟩

private abbrev WitnessedEncodedLive :=
  SourceAwareRelationalLive
    (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode)

private abbrev WitnessedEncodedValid :=
  SourceAwareRelationalCandidateValid
    (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)

private abbrev WitnessedEncodedDescriptorEdge :=
  sourceAwareRelationalExactEdge
    (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
      basis initialCode)

private abbrev WitnessedEncodedControlStep :
    ProfiledOpenWitnessedTableDescriptor A initialCode →
      ProfiledOpenWitnessedTableDescriptor A initialCode → Prop :=
  sourceAwareRelationalControlStep
    (Family := ProfiledOpenWitnessedTableFamily A initialCode)
    (ProfiledOpenWitnessedTableControlStep A initialCode)

/-- Candidate-level view of the encoded table edge, used by the generic
distinguished-successor selector. -/
def profiledOpenWitnessedEncodedCandidateEdge
    (source : ProfiledOpenWitnessedEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (target : ProfiledOpenWitnessedEncodedCandidate A initialCode) : Prop :=
  WitnessedEncodedDescriptorEdge A strategy hwin basis initialCode
    source.2 bank query target.1 target.2

/-- The already proved encoded coverage is exactly candidate-level
source-aware coverage after exposing the source family stored by the
candidate. -/
theorem profiledOpenWitnessedEncodedCandidate_liveSuccessorCoverage
    (package : ProfiledOpenActiveLaneWitnessedFixedPolicyTablePackage A
      strategy hwin basis initialCode policy state initialRoot) :
    SourceAwareRelationalCandidateLiveSuccessorCoverage
      (WitnessedEncodedLive A strategy hwin basis initialCode)
      (WitnessedEncodedValid A strategy hwin basis initialCode)
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (WitnessedEncodedControlStep A initialCode) := by
  intro source bank query hlive hvalid
  obtain ⟨target, hgood, htargetLive⟩ :=
    package.branch.coverage source bank query hlive hvalid
  exact ⟨target, hgood, htargetLive⟩

/-- Omniscient finite successor of the distinguished encoded candidate.  It
does not alter the full candidate set and is never exposed as a local choice. -/
noncomputable def profiledOpenWitnessedDistinguishedCandidateSuccessor
    (source : ProfiledOpenWitnessedEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    ProfiledOpenWitnessedEncodedCandidate A initialCode :=
  sourceAwareRelationalDistinguishedSuccessor
    (WitnessedEncodedLive A strategy hwin basis initialCode)
    (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
      initialCode)
    (WitnessedEncodedControlStep A initialCode) source bank query

/-- Replace the generic cursor's chosen target by the literal distinguished
selector while retaining the same full saturation and public node. -/
noncomputable def profiledOpenWitnessedCursorDistinguishedStep
    (cursor : package.branch.Cursor)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    package.branch.Cursor := by
  let bank := cursor.move package.branch
  let nextCandidates := relationalFamilySaturation
    (WitnessedEncodedDescriptorEdge A strategy hwin basis initialCode)
    (WitnessedEncodedControlStep A initialCode) cursor.candidates bank query
  let target := profiledOpenWitnessedDistinguishedCandidateSuccessor A
    (strategy := strategy) (hwin := hwin) (basis := basis)
    initialCode cursor.actual bank query
  have hvalid : WitnessedEncodedValid A strategy hwin basis initialCode
      cursor.actual.2 cursor.actual.1 bank :=
    cursor.move_valid_actual package.branch
  have hgood : SourceAwareRelationalFamilyCandidateGood
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (WitnessedEncodedControlStep A initialCode) cursor.actual bank query
        target :=
    sourceAwareRelationalDistinguishedSuccessor_good
      (WitnessedEncodedLive A strategy hwin basis initialCode)
      (WitnessedEncodedValid A strategy hwin basis initialCode)
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (WitnessedEncodedControlStep A initialCode)
      (profiledOpenWitnessedEncodedCandidate_liveSuccessorCoverage A
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (policy := policy) (state := state) (initialRoot := initialRoot)
        initialCode package)
      cursor.actual bank query cursor.actual_live hvalid
  have htargetMem : target ∈ nextCandidates := by
    apply (mem_relationalFamilySaturation_iff
      (WitnessedEncodedDescriptorEdge A strategy hwin basis initialCode)
      (WitnessedEncodedControlStep A initialCode) cursor.candidates bank query
      target).2
    exact ⟨cursor.actual, cursor.actual_mem, hgood⟩
  have htargetLive : WitnessedEncodedLive A strategy hwin basis initialCode
      target.2 target.1 :=
    sourceAwareRelationalDistinguishedSuccessor_live
      (WitnessedEncodedLive A strategy hwin basis initialCode)
      (WitnessedEncodedValid A strategy hwin basis initialCode)
      (profiledOpenWitnessedEncodedCandidateEdge A strategy hwin basis
        initialCode)
      (WitnessedEncodedControlStep A initialCode)
      (profiledOpenWitnessedEncodedCandidate_liveSuccessorCoverage A
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (policy := policy) (state := state) (initialRoot := initialRoot)
        initialCode package)
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

/-- The public finite recurrence of the distinguished cursor step is exactly
the already proved witnessed `BranchStep`. -/
theorem profiledOpenWitnessedBranchStateOfCursor_distinguishedStep
    (cursor : package.branch.Cursor)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    profiledOpenWitnessedBranchStateOfCursor A strategy hwin basis initialCode
        policy state initialRoot package
        (profiledOpenWitnessedCursorDistinguishedStep A
          (strategy := strategy) (hwin := hwin) (basis := basis)
          (policy := policy) (state := state) (initialRoot := initialRoot)
          initialCode package cursor query) =
      profiledOpenActiveLaneWitnessedBranchStep A strategy hwin basis
        initialCode policy state initialRoot package
        (profiledOpenWitnessedBranchStateOfCursor A strategy hwin basis
          initialCode policy state initialRoot package cursor) query := by
  have hlabel : package.table.toTransitionRationalTree.labelOf
        (package.table.toTransitionRationalTree.controlAt cursor.node) =
      some (cursor.move package.branch) := by
    change package.table.toTransitionRationalTree.labeledTree cursor.node = _
    rw [← package.branch_tree_eq]
    exact cursor.tree_eq_some_move package.branch
  have hlabel' : package.table.toTransitionRationalTree.labelOf
        (profiledOpenWitnessedBranchStateOfCursor A strategy hwin basis
          initialCode policy state initialRoot package cursor).1 =
      some (cursor.move package.branch) := by
    simpa only [profiledOpenWitnessedBranchStateOfCursor] using hlabel
  rw [profiledOpenActiveLaneWitnessedBranchStep, hlabel']
  apply Prod.ext
  · simp only [profiledOpenWitnessedBranchStateOfCursor,
      profiledOpenWitnessedCursorDistinguishedStep]
    rw [TransitionRationalTree.controlAt_append]
    rfl
  · rfl

/-- Total finite distinguished recurrence.  The chosen cursor exists only in
the proof of representation; the returned runtime value contains just the
finite public branch state and one finite actual candidate. -/
noncomputable def profiledOpenWitnessedDistinguishedStep
    (current : ProfiledOpenWitnessedDistinguishedState A strategy hwin basis
      initialCode policy state initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    ProfiledOpenWitnessedDistinguishedState A strategy hwin basis initialCode
      policy state initialRoot package := by
  let cursor := Classical.choose current.property
  let nextCursor := profiledOpenWitnessedCursorDistinguishedStep A
    (strategy := strategy) (hwin := hwin) (basis := basis)
    (policy := policy) (state := state) (initialRoot := initialRoot)
    initialCode package cursor query
  exact ⟨(profiledOpenWitnessedBranchStateOfCursor A strategy hwin basis
      initialCode policy state initialRoot package nextCursor,
      nextCursor.actual), ⟨nextCursor, rfl, rfl⟩⟩

/-- Exact branch/query coupling of the finite distinguished recurrence. -/
theorem profiledOpenWitnessedDistinguishedStep_branch
    (current : ProfiledOpenWitnessedDistinguishedState A strategy hwin basis
      initialCode policy state initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    (profiledOpenWitnessedDistinguishedStep A strategy hwin basis initialCode
      policy state initialRoot package current query).1.1 =
      profiledOpenActiveLaneWitnessedBranchStep A strategy hwin basis
        initialCode policy state initialRoot package current.1.1 query := by
  let cursor := Classical.choose current.property
  have hcursor := Classical.choose_spec current.property
  change profiledOpenWitnessedBranchStateOfCursor A strategy hwin basis
      initialCode policy state initialRoot package
        (profiledOpenWitnessedCursorDistinguishedStep A
          (strategy := strategy) (hwin := hwin) (basis := basis)
          (policy := policy) (state := state) (initialRoot := initialRoot)
          initialCode package cursor query) = _
  rw [profiledOpenWitnessedBranchStateOfCursor_distinguishedStep]
  rw [hcursor.1]

/-- The selected candidate remains a member of the complete public
saturation and remains live, because representation is preserved. -/
theorem profiledOpenWitnessedDistinguishedStep_mem_live
    (current : ProfiledOpenWitnessedDistinguishedState A strategy hwin basis
      initialCode policy state initialRoot package)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) :
    let next := profiledOpenWitnessedDistinguishedStep A strategy hwin basis
      initialCode policy state initialRoot package current query
    next.1.2 ∈ next.1.1.2 ∧
      WitnessedEncodedLive A strategy hwin basis initialCode next.1.2.2
        next.1.2.1 := by
  let next := profiledOpenWitnessedDistinguishedStep A strategy hwin basis
    initialCode policy state initialRoot package current query
  obtain ⟨cursor, hbranch, hactual⟩ := next.property
  change next.1.2 ∈ next.1.1.2 ∧ _
  rw [← hbranch, ← hactual]
  exact ⟨cursor.actual_mem, cursor.actual_live⟩

/-! ## Exact one-round maps of the two installed shadows -/

/-- Finite proof-side data needed to execute one right-oriented fixed value.
The member and root are used only by the full-information receiver row.  The
blind sender output and sender transition do not inspect them. -/
structure ProfiledOpenWitnessedRightRoundOverlay where
  value : ProfiledOpenFixedRightPinnedValue A initialCode
  query : ProfiledOpenFixedRightPinnedBlockQuery.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value
  reachable : ProfiledOpenFixedRightQueryReachable.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value query
  member : ProfiledOpenHiddenDescriptorRightCarrier A value.1
  root : ProfiledOpenHiddenDescriptorRightRoot A member.1
  /-- Sticky row copied from the completed direction's right pivot. -/
  entryRow : PairedEntryRow

/-- Left-oriented mirror. -/
structure ProfiledOpenWitnessedLeftRoundOverlay where
  value : ProfiledOpenFixedLeftPinnedValue A initialCode
  query : ProfiledOpenFixedLeftPinnedBlockQuery.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value
  reachable : ProfiledOpenFixedLeftQueryReachable.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value query
  member : ProfiledOpenHiddenDescriptorLeftCarrier A value.1
  root : ProfiledOpenHiddenDescriptorLeftRoot A member.1
  /-- Sticky row copied from the completed direction's left pivot. -/
  entryRow : PairedEntryRow

/-- Install one right overlay from the proof-erased semantic pivot supplied
by the re-anchored-row projection.  This is the safe constructor: the member
and root are not guessed independently. -/
noncomputable def profiledOpenWitnessedRightRoundOverlayOfEvaluation
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode :=
  { value := value
    query := query
    reachable := reachable
    member := evaluation.1.1
    root := evaluation.1.2
    entryRow := entryRow }

/-- Left safe constructor. -/
noncomputable def profiledOpenWitnessedLeftRoundOverlayOfEvaluation
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode :=
  { value := value
    query := query
    reachable := reachable
    member := evaluation.1.1
    root := evaluation.1.2
    entryRow := entryRow }

/-- Install the concrete right row directly from distinguished-candidate
liveness, validity, and the exact active-family premise.  Reachability of the
query alone is intentionally not used as a substitute for `hactive`. -/
noncomputable def profiledOpenWitnessedRightRoundOverlayOfSource
    (source : ProfiledOpenWitnessedEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (hlive : WitnessedEncodedLive A strategy hwin basis initialCode source.2
      source.1)
    (hvalid : WitnessedEncodedValid A strategy hwin basis initialCode source.2
      source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.1)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode :=
  let value := bank.1 source.1.1.1
  let evaluation := profiledOpenWitnessedRightReanchoredRowEvaluation A
    strategy hwin basis initialCode source bank query hlive hvalid hactive
  profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin basis
    initialCode (query.2.1 value) evaluation entryRow

/-- Left source-aware installation. -/
noncomputable def profiledOpenWitnessedLeftRoundOverlayOfSource
    (source : ProfiledOpenWitnessedEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (hlive : WitnessedEncodedLive A strategy hwin basis initialCode source.2
      source.1)
    (hvalid : WitnessedEncodedValid A strategy hwin basis initialCode source.2
      source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.2)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode :=
  let value := bank.2 source.1.1.2
  let evaluation := profiledOpenWitnessedLeftReanchoredRowEvaluation A
    strategy hwin basis initialCode source bank query hlive hvalid hactive
  profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin basis
    initialCode (query.2.2 value) evaluation entryRow

private noncomputable abbrev ProfiledOpenWitnessedRightRoundOverlayCode :=
  Σ value : ProfiledOpenFixedRightPinnedValue A initialCode,
    Σ query : ProfiledOpenFixedRightPinnedBlockQuery.{i, u, v, x, y, s,
      max i u v x y s} A initialCode value,
      Σ member : ProfiledOpenHiddenDescriptorRightCarrier A value.1,
        ProfiledOpenHiddenDescriptorRightRoot A member.1 × PairedEntryRow

private noncomputable abbrev ProfiledOpenWitnessedLeftRoundOverlayCode :=
  Σ value : ProfiledOpenFixedLeftPinnedValue A initialCode,
    Σ query : ProfiledOpenFixedLeftPinnedBlockQuery.{i, u, v, x, y, s,
      max i u v x y s} A initialCode value,
      Σ member : ProfiledOpenHiddenDescriptorLeftCarrier A value.1,
        ProfiledOpenHiddenDescriptorLeftRoot A member.1 × PairedEntryRow

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance profiledOpenWitnessedRightRoundOverlay_fintype :
    Fintype (ProfiledOpenWitnessedRightRoundOverlay A initialCode) := by
  classical
  let encode : ProfiledOpenWitnessedRightRoundOverlay A initialCode →
      ProfiledOpenWitnessedRightRoundOverlayCode A initialCode := fun overlay ↦
    Sigma.mk overlay.value
      (Sigma.mk overlay.query
        (Sigma.mk overlay.member (overlay.root, overlay.entryRow)))
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance profiledOpenWitnessedLeftRoundOverlay_fintype :
    Fintype (ProfiledOpenWitnessedLeftRoundOverlay A initialCode) := by
  classical
  let encode : ProfiledOpenWitnessedLeftRoundOverlay A initialCode →
      ProfiledOpenWitnessedLeftRoundOverlayCode A initialCode := fun overlay ↦
    Sigma.mk overlay.value
      (Sigma.mk overlay.query
        (Sigma.mk overlay.member (overlay.root, overlay.entryRow)))
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

/-- Literal realized record read by the right pinned-union monitor.  Its
sender component sees only process one's current input. -/
noncomputable def profiledOpenWitnessedRightRoundRecord
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    RealizedBlockRound
      ((Sigma fun member : ProfiledOpenHiddenDescriptorRightCarrier A
        overlay.value.1 ↦
          ProfiledOpenHiddenDescriptorRightRoot A member.1) × In₂)
      In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
  let label := overlay.value.2.2.1.toTransitionRationalTree.labelOf
    overlay.query.1
  (((⟨overlay.member, overlay.root⟩, inputTwo), inputOne),
    label.2 overlay.query.2
      (((⟨overlay.member, overlay.root⟩, inputTwo), inputOne)),
    label.1 inputOne)

/-- Left realized record.  Its sender component sees only process two's
current input. -/
noncomputable def profiledOpenWitnessedLeftRoundRecord
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    RealizedBlockRound
      ((Sigma fun member : ProfiledOpenHiddenDescriptorLeftCarrier A
        overlay.value.1 ↦
          ProfiledOpenHiddenDescriptorLeftRoot A member.1) × In₁)
      In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
  let label := overlay.value.2.2.1.toTransitionRationalTree.labelOf
    overlay.query.1
  (((⟨overlay.member, overlay.root⟩, inputOne), inputTwo),
    label.2 overlay.query.2
      (((⟨overlay.member, overlay.root⟩, inputOne), inputTwo)),
    label.1 inputTwo)

/-- Graph-blind process-one sender output of the right shadow. -/
noncomputable def profiledOpenWitnessedRightSenderOutput
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) : Out₁ :=
  (overlay.value.2.2.1.toTransitionRationalTree.labelOf overlay.query.1).1
    inputOne

/-- Full-information process-two receiver output of the right shadow.  The
row stored in the overlay is copied from the completed query's right pivot
and remains sticky for the whole block. -/
noncomputable def profiledOpenWitnessedRightReceiverOutput
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₂ :=
  pairedRightInformedForRow overlay.entryRow
    (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
      inputTwo).2.1.1.physical

/-- Process-two sender output of the left shadow. -/
noncomputable def profiledOpenWitnessedLeftSenderOutput
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputTwo : In₂) : Out₂ :=
  (overlay.value.2.2.1.toTransitionRationalTree.labelOf overlay.query.1).1
    inputTwo

/-- Process-one receiver output of the left shadow. -/
noncomputable def profiledOpenWitnessedLeftReceiverOutput
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ :=
  pairedLeftInformedForRow overlay.entryRow
    (profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
      inputTwo).2.1.1.physical

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The safe right constructor evaluates exactly the row projected by the
semantic re-anchoring theorem. -/
@[simp] theorem profiledOpenWitnessedRightReceiverOutput_ofEvaluation
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightReceiverOutput A initialCode
        (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable evaluation entryRow)
        inputOne inputTwo =
      profiledOpenFixedRightReanchoredReceiverOutput A strategy hwin basis
        initialCode evaluation entryRow inputOne inputTwo :=
  rfl

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left exact row-evaluation law. -/
@[simp] theorem profiledOpenWitnessedLeftReceiverOutput_ofEvaluation
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftReceiverOutput A initialCode
        (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable evaluation entryRow)
        inputOne inputTwo =
      profiledOpenFixedLeftReanchoredReceiverOutput A strategy hwin basis
        initialCode evaluation entryRow inputOne inputTwo :=
  rfl

/-- One right-shadow physical pair. -/
noncomputable def profiledOpenWitnessedRightPhysicalOutput
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × Out₂ :=
  (profiledOpenWitnessedRightSenderOutput A initialCode overlay inputOne,
    profiledOpenWitnessedRightReceiverOutput A initialCode overlay
      inputOne inputTwo)

/-- One left-shadow physical pair. -/
noncomputable def profiledOpenWitnessedLeftPhysicalOutput
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × Out₂ :=
  (profiledOpenWitnessedLeftReceiverOutput A initialCode overlay
      inputOne inputTwo,
    profiledOpenWitnessedLeftSenderOutput A initialCode overlay inputTwo)

/-- Advance the finite right query/monitor data by one physical input pair.

This definition is only the executable *candidate* update.  It deliberately
does not claim that the retained member/root remains a re-anchored semantic
evaluation of the advanced query.  A concrete use must either reinstall the
overlay through `profiledOpenWitnessedRightRoundOverlayOfSource` or prove the
corresponding row-behaviour preservation theorem. -/
noncomputable def ProfiledOpenWitnessedRightRoundOverlay.step
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode := by
  let monitor := ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A
    overlay.value.1 overlay.value.2.1
  let nextMonitor := monitor.step overlay.query.2
    (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
      inputTwo)
  let nextQuery := profiledOpenFixedRightQueryStep A initialCode overlay.value
    overlay.query inputOne nextMonitor
  exact
    { value := overlay.value
      query := nextQuery
      reachable := profiledOpenFixedRightQueryStep_reachable A initialCode
        overlay.value overlay.query overlay.reachable inputOne nextMonitor
      member := overlay.member
      root := overlay.root
      entryRow := overlay.entryRow }

/-- Left executable candidate update, with the same explicit semantic
preservation obligation as the right update. -/
noncomputable def ProfiledOpenWitnessedLeftRoundOverlay.step
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode := by
  let monitor := ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A
    overlay.value.1 overlay.value.2.1
  let nextMonitor := monitor.step overlay.query.2
    (profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
      inputTwo)
  let nextQuery := profiledOpenFixedLeftQueryStep A initialCode overlay.value
    overlay.query inputTwo nextMonitor
  exact
    { value := overlay.value
      query := nextQuery
      reachable := profiledOpenFixedLeftQueryStep_reachable A initialCode
        overlay.value overlay.query overlay.reachable inputTwo nextMonitor
      member := overlay.member
      root := overlay.root
      entryRow := overlay.entryRow }

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenWitnessedRightRoundOverlay_step_value
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    (overlay.step A initialCode inputOne inputTwo).value = overlay.value :=
  rfl

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenWitnessedLeftRoundOverlay_step_value
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    (overlay.step A initialCode inputOne inputTwo).value = overlay.value :=
  rfl

/-- Each process chooses a shadow using only its current local receipt event.
The sticky rows are already fields of the installed overlays, copied from the
completed query pivots; no graph, orientation, leader flag, or reconstructed
lost bit is an argument. -/
noncomputable def profiledOpenWitnessedOutputOfLocalEvents
    (right : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (left : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (receivedOne receivedTwo : Bool)
    (inputOne : In₁) (inputTwo : In₂) : Out₁ × Out₂ :=
  (if receivedOne then
      profiledOpenWitnessedLeftReceiverOutput A initialCode left
        inputOne inputTwo
    else
      profiledOpenWitnessedRightSenderOutput A initialCode right inputOne,
    if receivedTwo then
      profiledOpenWitnessedRightReceiverOutput A initialCode right
        inputOne inputTwo
    else
      profiledOpenWitnessedLeftSenderOutput A initialCode left inputTwo)

section
omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- On a strict-right graph, the two local event choices form exactly the
right physical pair. -/
@[simp] theorem profiledOpenWitnessedOutputOfLocalEvents_right
    (right : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (left : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedOutputOfLocalEvents A initialCode right left
        (physicalReceivedOne Graph.right) (physicalReceivedTwo Graph.right)
        inputOne inputTwo =
      profiledOpenWitnessedRightPhysicalOutput A initialCode right
        inputOne inputTwo :=
  rfl

/-- Strict-left mirror. -/
@[simp] theorem profiledOpenWitnessedOutputOfLocalEvents_left
    (right : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (left : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedOutputOfLocalEvents A initialCode right left
        (physicalReceivedOne Graph.left) (physicalReceivedTwo Graph.left)
        inputOne inputTwo =
      profiledOpenWitnessedLeftPhysicalOutput A initialCode left
        inputOne inputTwo :=
  rfl

/-- At a simultaneous graph, process one uses the left receiver shadow and
process two uses the right receiver shadow, exactly as in
`profiledBothPhysicalOutput`. -/
@[simp] theorem profiledOpenWitnessedOutputOfLocalEvents_both
    (right : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (left : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedOutputOfLocalEvents A initialCode right left
        (physicalReceivedOne Graph.both) (physicalReceivedTwo Graph.both)
        inputOne inputTwo =
      ((profiledOpenWitnessedLeftPhysicalOutput A initialCode left
          inputOne inputTwo).1,
        (profiledOpenWitnessedRightPhysicalOutput A initialCode right
          inputOne inputTwo).2) :=
  rfl

end

/-!
## Exact remaining concrete obligations

The construction above intentionally stops before two model-specific facts.

1. A concrete finite `Phase` must simulate the ordinary/reversed recut state
   and every re-reversal until `.both`.  Its adequacy proof must identify the
   accumulated query with the query consumed by the witnessed branch at that
   `.both` round.  A direction toggle is not such a proof.
2. The installed physical behaviour must be homogeneous on each *reachable
   local belief*.  Concretely this is
   `FiniteGlobalRoundMachine.ReachableBeliefsUniform` for the final machine and
   its two output maps.  This obligation quantifies over every compatible
   re-anchored evaluation and every compatible sticky `PairedEntryRow`; it
   does not ask for a unique row and does not reconstruct the hidden bit.

The source-aware constructors now discharge the dependent member/root
projection exactly, provided `ProfiledOpenWitnessedSourceActiveForQuery` (in
the corresponding side case).  Query reachability alone does not discharge
that active-family premise.  If either homogeneity component fails, the
collision certificates below preserve the two alternatives and refute the
claimed local presentation rather than merging them.
-/

/-! ## Lost-bit-safe fail-fast certificates -/

end DetParityAutomaton

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine In₁ In₂)

/-- Two states compatible with one reachable process-one belief but carrying
different outputs.  The states may differ by only one permanently hidden bit;
no recovery or eventual-merging assumption is made. -/
structure ReachableOneOutputCollision {Out₁ : Type x}
    (outputOne : G.State → Out₁) where
  rounds : List (EnvironmentRound In₁ In₂)
  left : G.State
  right : G.State
  left_mem : left ∈ (G.beliefsAfter rounds).1
  right_mem : right ∈ (G.beliefsAfter rounds).1
  separated : outputOne left ≠ outputOne right

/-- Process-two mirror. -/
structure ReachableTwoOutputCollision {Out₂ : Type y}
    (outputTwo : G.State → Out₂) where
  rounds : List (EnvironmentRound In₁ In₂)
  left : G.State
  right : G.State
  left_mem : left ∈ (G.beliefsAfter rounds).2
  right_mem : right ∈ (G.beliefsAfter rounds).2
  separated : outputTwo left ≠ outputTwo right

/-- A single reachable process-one collision refutes distributed belief
readback, irrespective of how a representative of the belief is chosen. -/
theorem not_reachableBeliefsUniform_of_oneOutputCollision
    {Out₁ : Type x} {Out₂ : Type y}
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (collision : G.ReachableOneOutputCollision outputOne) :
    ¬ G.ReachableBeliefsUniform outputOne outputTwo := by
  intro huniform
  exact collision.separated
    ((huniform collision.rounds).1 collision.left collision.left_mem
      collision.right collision.right_mem)

/-- Process-two collision refutation. -/
theorem not_reachableBeliefsUniform_of_twoOutputCollision
    {Out₁ : Type x} {Out₂ : Type y}
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (collision : G.ReachableTwoOutputCollision outputTwo) :
    ¬ G.ReachableBeliefsUniform outputOne outputTwo := by
  intro huniform
  exact collision.separated
    ((huniform collision.rounds).2 collision.left collision.left_mem
      collision.right collision.right_mem)

end FiniteGlobalRoundMachine

end DistributedSynthesis
