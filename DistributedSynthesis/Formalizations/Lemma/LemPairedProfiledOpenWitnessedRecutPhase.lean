/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedDirectionAccumulator
import DistributedSynthesis.Formalizations.Theorem.ThmArenaFold

/-!
# The finite physical recut phase of the witnessed adapter

This file supplies the finite `Phase` shape left abstract by
`FiniteEpochQueryAdapter`.  It deliberately separates two pieces.

* `ProfiledOpenPhysicalRecutTier` is the exact five-state quotient of the
  boundary-game tiers.  A strict round opens or continues one orientation;
  the first strict reversal enters the reversed tier and every later strict
  reversal switches between the two reversed tiers.  Only `Graph.both`
  returns to the boundary.
* `ProfiledOpenPhysicalRecutPhase` carries a `Finset` of dependent
  `ProfiledOpenIndexedDirectionAccumulator`s.  Thus a hidden lineage or
  `PairedEntryRow` is never guessed or recovered.  All compatible choices
  remain explicit until the closing `both` round.

The phase is proof-side global state.  Neither process-local transition is
given its tier, its selected accumulator, an orientation, a strict-leader
flag, or a row bit.  The executable local presentation still has to be
obtained from reachable output homogeneity.

The file proves three adequacy facts needed by the physical compiler:

1. the five-state tier is exactly the quotient of `arenaStep`, including
   direct reversals and arbitrary re-reversals;
2. the streaming right/left steps are exactly append steps of the already
   proved extensional direction scan;
3. closing a retained accumulator produces a literal
   `ProfiledOpenWitnessedTableQuery`, while retaining every supplied pivot
   (and hence every supplied sticky-row alternative).

What remains model-specific is named once at the bottom:
`ProfiledOpenWitnessedPhysicalEpochQueryCovered`.  It says that the literal
query selected by the witnessed semantic execution is among the finite
closing queries.  Discharging it requires the physical-history-to-lineage
coverage invariant; it does not assert uniqueness and cannot be proved by
recovering a permanently lost bit.
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
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

noncomputable local instance profiledOpenWitnessedTableQuery_decidableEq :
    DecidableEq (ProfiledOpenWitnessedTableQuery A initialCode) :=
  Classical.decEq _

/-! ## The exact five-state graph quotient -/

/-- Finite proof-side quotient of the ordinary and reversed boundary-game
tiers.  `ordinaryLeft` and `ordinaryRight` are the third and fourth summands
of `BoundaryGamePosition`; `reversedLeft` and `reversedRight` are its fifth
and sixth summands. -/
inductive ProfiledOpenPhysicalRecutTier where
  | boundary
  | ordinaryLeft
  | ordinaryRight
  | reversedLeft
  | reversedRight
deriving DecidableEq, Fintype

/-- Exact graph update of the recut tier.  Notice that an opposite strict
round never closes the epoch.  Once a direct reversal has occurred, every
later strict change of orientation remains in the reversed pair of tiers. -/
def ProfiledOpenPhysicalRecutTier.advance :
    ProfiledOpenPhysicalRecutTier → Graph → ProfiledOpenPhysicalRecutTier
  | _, .both => .boundary
  | .boundary, .left => .ordinaryLeft
  | .boundary, .right => .ordinaryRight
  | .ordinaryLeft, .left => .ordinaryLeft
  | .ordinaryLeft, .right => .reversedRight
  | .ordinaryRight, .left => .reversedLeft
  | .ordinaryRight, .right => .ordinaryRight
  | .reversedLeft, .left => .reversedLeft
  | .reversedLeft, .right => .reversedRight
  | .reversedRight, .left => .reversedLeft
  | .reversedRight, .right => .reversedRight

@[simp] theorem ProfiledOpenPhysicalRecutTier.advance_both
    (tier : ProfiledOpenPhysicalRecutTier) :
    tier.advance .both = .boundary := by
  cases tier <;> rfl

@[simp] theorem ProfiledOpenPhysicalRecutTier.advance_boundary_left :
    ProfiledOpenPhysicalRecutTier.boundary.advance .left = .ordinaryLeft :=
  rfl

@[simp] theorem ProfiledOpenPhysicalRecutTier.advance_boundary_right :
    ProfiledOpenPhysicalRecutTier.boundary.advance .right = .ordinaryRight :=
  rfl

/-- The side used by a closing proof-side row.  At a boundary-only epoch
there was no strict leader to observe, so `none` is retained rather than
inventing one. -/
def ProfiledOpenPhysicalRecutTier.activeSide :
    ProfiledOpenPhysicalRecutTier → Option IndexedLineageSide
  | .boundary => none
  | .ordinaryLeft => some .left
  | .ordinaryRight => some .right
  | .reversedLeft => some .left
  | .reversedRight => some .right

/-- Quotient a boundary-game position to the physical recut tier.  The
committed tier is absent because `arenaFoldSeq` never rests there. -/
def profiledOpenBoundaryPositionRecutTier
    {C_L C_R C_V : Type max u v x y s}
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    Option ProfiledOpenPhysicalRecutTier :=
  match position with
  | Sum.inl _ => some .boundary
  | Sum.inr (Sum.inl _) => none
  | Sum.inr (Sum.inr (Sum.inl _)) => some .ordinaryLeft
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => some .ordinaryRight
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) =>
      some .reversedLeft
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
      some .reversedRight

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The five-state phase is not an approximation of the arena clock: it is
its exact quotient on every non-committed position.  In particular all four
direct/re-reversal cases reduce to the corresponding `advance` equation. -/
theorem profiledOpenBoundaryPositionRecutTier_arenaStep
    {C_L C_R C_V : Type max u v x y s}
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (round : EnvironmentRound In₁ In₂)
    (tier : ProfiledOpenPhysicalRecutTier)
    (htier : profiledOpenBoundaryPositionRecutTier A position = some tier) :
    profiledOpenBoundaryPositionRecutTier A
        (arenaStep plans position round) =
      some (tier.advance round.graph) := by
  rcases position with boundary | committed | inLeft | inRight |
    reversedLeft | reversedRight
  · rcases boundary with ⟨state, minState⟩
    simp only [profiledOpenBoundaryPositionRecutTier,
      Option.some.injEq] at htier
    subst tier
    cases hgraph : round.graph <;>
      simp [arenaStep, hgraph, profiledOpenBoundaryPositionRecutTier,
        ProfiledOpenPhysicalRecutTier.advance, boundaryBothTarget,
        boundaryOpenLeftTarget, boundaryOpenRightTarget]
  · simp [profiledOpenBoundaryPositionRecutTier] at htier
  · rcases inLeft with ⟨plan, chain, control, state, minState⟩
    simp only [profiledOpenBoundaryPositionRecutTier,
      Option.some.injEq] at htier
    subst tier
    cases hgraph : round.graph <;>
      simp [arenaStep, hgraph, profiledOpenBoundaryPositionRecutTier,
        ProfiledOpenPhysicalRecutTier.advance, leftContinueTarget,
        leftReverseTarget, leftCloseTarget]
  · rcases inRight with ⟨plan, chain, control, state, minState⟩
    simp only [profiledOpenBoundaryPositionRecutTier,
      Option.some.injEq] at htier
    subst tier
    cases hgraph : round.graph <;>
      simp [arenaStep, hgraph, profiledOpenBoundaryPositionRecutTier,
        ProfiledOpenPhysicalRecutTier.advance, rightContinueTarget,
        rightReverseTarget, rightCloseTarget]
  · rcases reversedLeft with ⟨chain, control, entry, state, minState⟩
    simp only [profiledOpenBoundaryPositionRecutTier,
      Option.some.injEq] at htier
    subst tier
    cases hgraph : round.graph <;>
      simp [arenaStep, hgraph, profiledOpenBoundaryPositionRecutTier,
        ProfiledOpenPhysicalRecutTier.advance, revLeftContinueTarget,
        revLeftReverseTarget, revLeftCloseTarget]
  · rcases reversedRight with ⟨chain, control, entry, state, minState⟩
    simp only [profiledOpenBoundaryPositionRecutTier,
      Option.some.injEq] at htier
    subst tier
    cases hgraph : round.graph <;>
      simp [arenaStep, hgraph, profiledOpenBoundaryPositionRecutTier,
        ProfiledOpenPhysicalRecutTier.advance, revRightContinueTarget,
        revRightReverseTarget, revRightCloseTarget]

/-! ## A finite set of dependent streaming accumulators -/

/-- One retained proof-side move and its accumulator.  The dependency is
essential: controls belonging to two different classified table moves are
never cast or silently identified. -/
structure ProfiledOpenPhysicalDirectionAccumulatorCandidate where
  move : ProfiledOpenIndexedBiBeliefMove A
  accumulator : ProfiledOpenIndexedDirectionAccumulator A move

noncomputable instance
    profiledOpenPhysicalDirectionAccumulatorCandidate_fintype :
    Fintype (ProfiledOpenPhysicalDirectionAccumulatorCandidate A) := by
  classical
  let encode := fun candidate :
      ProfiledOpenPhysicalDirectionAccumulatorCandidate A =>
    Sigma.mk candidate.move candidate.accumulator
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

/-- Install one move at the two empty streaming controls. -/
noncomputable def profiledOpenPhysicalDirectionAccumulatorCandidateInitial
    (move : ProfiledOpenIndexedBiBeliefMove A) :
    ProfiledOpenPhysicalDirectionAccumulatorCandidate A :=
  ⟨move, profiledOpenIndexedDirectionAccumulatorInitial A move⟩

/-- Advance the right lane on one strict-right physical letter. -/
noncomputable def ProfiledOpenPhysicalDirectionAccumulatorCandidate.stepRight
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenPhysicalDirectionAccumulatorCandidate A :=
  ⟨candidate.move,
    profiledOpenIndexedDirectionAccumulatorStepRight A initialCode
      candidate.move candidate.accumulator
      (((lineage, inputTwo), inputOne))⟩

/-- Advance the left lane on one strict-left physical letter. -/
noncomputable def ProfiledOpenPhysicalDirectionAccumulatorCandidate.stepLeft
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenPhysicalDirectionAccumulatorCandidate A :=
  ⟨candidate.move,
    profiledOpenIndexedDirectionAccumulatorStepLeft A initialCode
      candidate.move candidate.accumulator
      (((lineage, inputOne), inputTwo))⟩

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- Right streaming is exactly append on the extensional two-list scan. -/
theorem profiledOpenIndexedDirectionAccumulatorScan_append_right
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightPast : List ((I × In₂) × In₁))
    (leftPast : List ((I × In₁) × In₂))
    (tagged : (I × In₂) × In₁) :
    profiledOpenIndexedDirectionAccumulatorStepRight A initialCode move
        (profiledOpenIndexedDirectionAccumulatorScan A initialCode move
          rightPast leftPast) tagged =
      profiledOpenIndexedDirectionAccumulatorScan A initialCode move
        (rightPast ++ [tagged]) leftPast := by
  simp [profiledOpenIndexedDirectionAccumulatorStepRight,
    profiledOpenIndexedDirectionAccumulatorScan,
    profiledOpenIndexedRightDirectionControlScan, List.foldl_append]

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- Left append law. -/
theorem profiledOpenIndexedDirectionAccumulatorScan_append_left
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightPast : List ((I × In₂) × In₁))
    (leftPast : List ((I × In₁) × In₂))
    (tagged : (I × In₁) × In₂) :
    profiledOpenIndexedDirectionAccumulatorStepLeft A initialCode move
        (profiledOpenIndexedDirectionAccumulatorScan A initialCode move
          rightPast leftPast) tagged =
      profiledOpenIndexedDirectionAccumulatorScan A initialCode move
        rightPast (leftPast ++ [tagged]) := by
  simp [profiledOpenIndexedDirectionAccumulatorStepLeft,
    profiledOpenIndexedDirectionAccumulatorScan,
    profiledOpenIndexedLeftDirectionControlScan, List.foldl_append]

/-- Concrete finite `Phase` for the witnessed physical adapter.  `candidates`
is a set, not a selected accumulator; its branching retains every compatible
hidden lineage and row alternative. -/
structure ProfiledOpenPhysicalRecutPhase where
  tier : ProfiledOpenPhysicalRecutTier
  candidates : Finset (ProfiledOpenPhysicalDirectionAccumulatorCandidate A)

noncomputable instance profiledOpenPhysicalRecutPhase_fintype :
    Fintype (ProfiledOpenPhysicalRecutPhase A) := by
  classical
  let encode := fun phase : ProfiledOpenPhysicalRecutPhase A =>
    (phase.tier, phase.candidates)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

/-- Install all currently compatible table moves. -/
noncomputable def profiledOpenPhysicalRecutPhaseInitial
    (moves : Finset (ProfiledOpenIndexedBiBeliefMove A)) :
    ProfiledOpenPhysicalRecutPhase A := by
  classical
  exact
    { tier := .boundary
      candidates := moves.image
        (profiledOpenPhysicalDirectionAccumulatorCandidateInitial A) }

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem mem_profiledOpenPhysicalRecutPhaseInitial
    (moves : Finset (ProfiledOpenIndexedBiBeliefMove A))
    (move : ProfiledOpenIndexedBiBeliefMove A) (hmove : move ∈ moves) :
    profiledOpenPhysicalDirectionAccumulatorCandidateInitial A move ∈
      (profiledOpenPhysicalRecutPhaseInitial A moves).candidates := by
  classical
  exact Finset.mem_image_of_mem _ hmove

/-- One physical round.  A strict graph advances the corresponding lane for
every compatible lineage.  A `both` graph advances no past lane: its current
inputs and row-carrying pivots are installed by `finishedTags` below. -/
noncomputable def ProfiledOpenPhysicalRecutPhase.advance
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (rightLineages leftLineages : Finset I)
    (round : EnvironmentRound In₁ In₂) :
    ProfiledOpenPhysicalRecutPhase A := by
  classical
  refine { tier := phase.tier.advance round.graph, candidates := ?_ }
  cases round.graph with
  | right =>
      exact phase.candidates.biUnion fun candidate ↦
        rightLineages.image fun lineage ↦
          candidate.stepRight A initialCode lineage round.inputOne
            round.inputTwo
  | left =>
      exact phase.candidates.biUnion fun candidate ↦
        leftLineages.image fun lineage ↦
          candidate.stepLeft A initialCode lineage round.inputOne
            round.inputTwo
  | both => exact phase.candidates

section
omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂]

@[simp] theorem ProfiledOpenPhysicalRecutPhase.advance_tier
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (rightLineages leftLineages : Finset I)
    (round : EnvironmentRound In₁ In₂) :
    (phase.advance A initialCode rightLineages leftLineages round).tier =
      phase.tier.advance round.graph := by
  rfl

@[simp] theorem ProfiledOpenPhysicalRecutPhase.advance_both_candidates
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (rightLineages leftLineages : Finset I)
    (inputOne : In₁) (inputTwo : In₂) :
    (phase.advance A initialCode rightLineages leftLineages
      { inputOne := inputOne, inputTwo := inputTwo, graph := .both }).candidates =
        phase.candidates := by
  rfl

theorem ProfiledOpenPhysicalRecutPhase.mem_advance_right
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (rightLineages leftLineages : Finset I)
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (inputOne : In₁) (inputTwo : In₂)
    (hcandidate : candidate ∈ phase.candidates)
    (hlineage : lineage ∈ rightLineages) :
    candidate.stepRight A initialCode lineage inputOne inputTwo ∈
      (phase.advance A initialCode rightLineages leftLineages
        { inputOne := inputOne, inputTwo := inputTwo,
          graph := .right }).candidates := by
  classical
  simp only [ProfiledOpenPhysicalRecutPhase.advance, Finset.mem_biUnion,
    Finset.mem_image]
  exact ⟨candidate, hcandidate, lineage, hlineage, rfl⟩

theorem ProfiledOpenPhysicalRecutPhase.mem_advance_left
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (rightLineages leftLineages : Finset I)
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (inputOne : In₁) (inputTwo : In₂)
    (hcandidate : candidate ∈ phase.candidates)
    (hlineage : lineage ∈ leftLineages) :
    candidate.stepLeft A initialCode lineage inputOne inputTwo ∈
      (phase.advance A initialCode rightLineages leftLineages
        { inputOne := inputOne, inputTwo := inputTwo,
          graph := .left }).candidates := by
  classical
  simp only [ProfiledOpenPhysicalRecutPhase.advance, Finset.mem_biUnion,
    Finset.mem_image]
  exact ⟨candidate, hcandidate, lineage, hlineage, rfl⟩

end

/-! ## Closing tags and literal table queries -/

/-- Finish one retained accumulator.  The two pivots retain their
`PairedEntryRow` coordinates literally. -/
noncomputable def ProfiledOpenPhysicalDirectionAccumulatorCandidate.finish
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenIndexedFiniteDirectionTag A (I := I) :=
  ⟨candidate.move,
    candidate.accumulator.finish A rightPivot (inputTwo, inputOne)
      leftPivot (inputOne, inputTwo)⟩

/-- All closing tags generated by the retained accumulators and all supplied
row-carrying pivots.  There is no distinguished row in this definition. -/
noncomputable def ProfiledOpenPhysicalRecutPhase.finishedTags
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (rightPivots leftPivots : Finset (IndexedLineageCandidate I))
    (inputOne : In₁) (inputTwo : In₂) :
    Finset (ProfiledOpenIndexedFiniteDirectionTag A (I := I)) := by
  classical
  exact phase.candidates.biUnion fun candidate ↦
    rightPivots.biUnion fun rightPivot ↦
      leftPivots.image fun leftPivot ↦
        candidate.finish A rightPivot leftPivot inputOne inputTwo

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
theorem ProfiledOpenPhysicalRecutPhase.mem_finishedTags
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (rightPivots leftPivots : Finset (IndexedLineageCandidate I))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂)
    (hcandidate : candidate ∈ phase.candidates)
    (hright : rightPivot ∈ rightPivots)
    (hleft : leftPivot ∈ leftPivots) :
    candidate.finish A rightPivot leftPivot inputOne inputTwo ∈
      phase.finishedTags A rightPivots leftPivots inputOne inputTwo := by
  classical
  simp only [ProfiledOpenPhysicalRecutPhase.finishedTags,
    Finset.mem_biUnion, Finset.mem_image]
  exact ⟨candidate, hcandidate, rightPivot, hright,
    leftPivot, hleft, rfl⟩

/-- Replace only the proof-side side and finite direction tag of a reachable
table query.  Its complete symmetric query bank is retained definitionally,
so reachability is unchanged. -/
noncomputable def profiledOpenWitnessedTableQueryWithDirection
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenWitnessedTableQuery A initialCode :=
  ⟨((side, query.1.1.2), tag), query.2⟩

section
omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenWitnessedTableQueryWithDirection_side
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenWitnessedTableQueryWithDirection A initialCode query side
      tag).1.1.1 = side :=
  rfl

@[simp] theorem profiledOpenWitnessedTableQueryWithDirection_bank
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenWitnessedTableQueryWithDirection A initialCode query side
      tag).1.1.2 = query.1.1.2 :=
  rfl

@[simp] theorem profiledOpenWitnessedTableQueryWithDirection_tag
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenWitnessedTableQueryWithDirection A initialCode query side
      tag).1.2 = tag :=
  rfl

end

/-- Closing queries for an explicitly chosen proof-side side.  This choice is
made in the global witness, not by either local process.  Boundary-only
epochs can retain both sides by taking the union of the two resulting sets. -/
noncomputable def ProfiledOpenPhysicalRecutPhase.finishedQueriesForSide
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivots leftPivots : Finset (IndexedLineageCandidate I))
    (inputOne : In₁) (inputTwo : In₂) :
    Finset (ProfiledOpenWitnessedTableQuery A initialCode) := by
  classical
  exact (phase.finishedTags A rightPivots leftPivots inputOne inputTwo).image
    (profiledOpenWitnessedTableQueryWithDirection A initialCode query side)

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledOpenPhysicalRecutPhase.mem_finishedQueriesForSide
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivots leftPivots : Finset (IndexedLineageCandidate I))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂)
    (hcandidate : candidate ∈ phase.candidates)
    (hright : rightPivot ∈ rightPivots)
    (hleft : leftPivot ∈ leftPivots) :
    profiledOpenWitnessedTableQueryWithDirection A initialCode query side
        (candidate.finish A rightPivot leftPivot inputOne inputTwo) ∈
      phase.finishedQueriesForSide A initialCode query side rightPivots
        leftPivots inputOne inputTwo := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨candidate.finish A rightPivot leftPivot inputOne inputTwo,
    phase.mem_finishedTags A rightPivots leftPivots candidate rightPivot
      leftPivot inputOne inputTwo hcandidate hright hleft,
    rfl⟩

/-! ## Kernel-checked reversal/re-reversal pair test -/

/-- The raw direction used by the decisive physical phase test: two ordinary
right rounds, one direct left reversal, one right re-reversal, and the
closing inputs/pivots subsequently installed by `both`. -/
def profiledOpenPhysicalRecutPairTestDirection
    (rightLineage₀ rightLineage₁ leftLineage rightLineage₂ : I)
    (rightInput₀ rightInput₁ leftInput rightInput₂ closingInput :
      In₁ × In₂)
    (rightPivot leftPivot : IndexedLineageCandidate I) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  { rightPivot := rightPivot
    rightTaggedPast :=
      [((rightLineage₀, rightInput₀.2), rightInput₀.1),
        ((rightLineage₁, rightInput₁.2), rightInput₁.1),
        ((rightLineage₂, rightInput₂.2), rightInput₂.1)]
    rightInput := (closingInput.2, closingInput.1)
    leftPivot := leftPivot
    leftTaggedPast := [((leftLineage, leftInput.1), leftInput.2)]
    leftInput := closingInput }

/-- The distinguished accumulator obtained by the physical order
`right; right; left; right`. -/
noncomputable def profiledOpenPhysicalRecutPairTestCandidate
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage₀ rightLineage₁ leftLineage rightLineage₂ : I)
    (rightInput₀ rightInput₁ leftInput rightInput₂ : In₁ × In₂) :
    ProfiledOpenPhysicalDirectionAccumulatorCandidate A :=
  ((((profiledOpenPhysicalDirectionAccumulatorCandidateInitial A move).stepRight
      A initialCode rightLineage₀ rightInput₀.1 rightInput₀.2).stepRight
      A initialCode rightLineage₁ rightInput₁.1 rightInput₁.2).stepLeft
      A initialCode leftLineage leftInput.1 leftInput.2).stepRight
      A initialCode rightLineage₂ rightInput₂.1 rightInput₂.2

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- The interleaved physical scan is definitionally the old two-list scan.
This is the accumulator part of the pair test. -/
theorem profiledOpenPhysicalRecutPairTestCandidate_accumulator
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage₀ rightLineage₁ leftLineage rightLineage₂ : I)
    (rightInput₀ rightInput₁ leftInput rightInput₂ : In₁ × In₂) :
    (profiledOpenPhysicalRecutPairTestCandidate A initialCode move
      rightLineage₀ rightLineage₁ leftLineage rightLineage₂
      rightInput₀ rightInput₁ leftInput rightInput₂).accumulator =
      profiledOpenIndexedDirectionAccumulatorScan A initialCode move
        [((rightLineage₀, rightInput₀.2), rightInput₀.1),
          ((rightLineage₁, rightInput₁.2), rightInput₁.1),
          ((rightLineage₂, rightInput₂.2), rightInput₂.1)]
        [((leftLineage, leftInput.1), leftInput.2)] := by
  rfl

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- The produced closing tag is exactly the pre-existing extensional
`profiledOpenIndexedDirectionSummarize`; there is no phase-specific surrogate
summary. -/
theorem profiledOpenPhysicalRecutPairTest_finish_eq_summary
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage₀ rightLineage₁ leftLineage rightLineage₂ : I)
    (rightInput₀ rightInput₁ leftInput rightInput₂ closingInput :
      In₁ × In₂)
    (rightPivot leftPivot : IndexedLineageCandidate I) :
    let candidate := profiledOpenPhysicalRecutPairTestCandidate A initialCode
      move rightLineage₀ rightLineage₁ leftLineage rightLineage₂
      rightInput₀ rightInput₁ leftInput rightInput₂
    let direction := profiledOpenPhysicalRecutPairTestDirection
      rightLineage₀ rightLineage₁ leftLineage rightLineage₂
      rightInput₀ rightInput₁ leftInput rightInput₂ closingInput
      rightPivot leftPivot
    candidate.finish A rightPivot leftPivot closingInput.1 closingInput.2 =
      ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
        direction⟩ := by
  dsimp only
  simp only [ProfiledOpenPhysicalDirectionAccumulatorCandidate.finish]
  rw [profiledOpenPhysicalRecutPairTestCandidate_accumulator]
  exact congrArg (Sigma.mk move)
    (profiledOpenIndexedDirectionAccumulator_finish_scan A initialCode move
      (profiledOpenPhysicalRecutPairTestDirection
        rightLineage₀ rightLineage₁ leftLineage rightLineage₂
        rightInput₀ rightInput₁ leftInput rightInput₂ closingInput
        rightPivot leftPivot))

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- **Decisive phase test.**  Starting from the boundary, the concrete phase
executes an ordinary right opening and continuation, a direct left reversal,
a right re-reversal, and a closing `both`.  The result is back at `boundary`,
and the literal query carrying the old summarized direction belongs to the
produced finite closing-query set.

All lineage and row choices are singleton parameters of this test, not
runtime observations.  The general phase replaces those singletons by the
full compatible finite sets. -/
theorem profiledOpenPhysicalRecutPairTest_passes
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage₀ rightLineage₁ leftLineage rightLineage₂ : I)
    (rightInput₀ rightInput₁ leftInput rightInput₂ closingInput :
      In₁ × In₂)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (carriedQuery : ProfiledOpenWitnessedTableQuery A initialCode) :
    let phase₀ := profiledOpenPhysicalRecutPhaseInitial A {move}
    let phase₁ := phase₀.advance A initialCode {rightLineage₀}
      {leftLineage}
      { inputOne := rightInput₀.1, inputTwo := rightInput₀.2,
        graph := .right }
    let phase₂ := phase₁.advance A initialCode {rightLineage₁}
      {leftLineage}
      { inputOne := rightInput₁.1, inputTwo := rightInput₁.2,
        graph := .right }
    let phase₃ := phase₂.advance A initialCode {rightLineage₂}
      {leftLineage}
      { inputOne := leftInput.1, inputTwo := leftInput.2, graph := .left }
    let phase₄ := phase₃.advance A initialCode {rightLineage₂}
      {leftLineage}
      { inputOne := rightInput₂.1, inputTwo := rightInput₂.2,
        graph := .right }
    let phase₅ := phase₄.advance A initialCode {rightLineage₂}
      {leftLineage}
      { inputOne := closingInput.1, inputTwo := closingInput.2, graph := .both }
    let direction := profiledOpenPhysicalRecutPairTestDirection
      rightLineage₀ rightLineage₁ leftLineage rightLineage₂
      rightInput₀ rightInput₁ leftInput rightInput₂ closingInput
      rightPivot leftPivot
    phase₅.tier = .boundary ∧
      profiledOpenWitnessedTableQueryWithDirection A initialCode carriedQuery
          .right
          ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
            direction⟩ ∈
        phase₅.finishedQueriesForSide A initialCode carriedQuery .right
          {rightPivot} {leftPivot} closingInput.1 closingInput.2 := by
  classical
  dsimp only
  constructor
  · rfl
  · let candidate₀ :=
      profiledOpenPhysicalDirectionAccumulatorCandidateInitial A move
    let candidate₁ := candidate₀.stepRight A initialCode rightLineage₀
      rightInput₀.1 rightInput₀.2
    let candidate₂ := candidate₁.stepRight A initialCode rightLineage₁
      rightInput₁.1 rightInput₁.2
    let candidate₃ := candidate₂.stepLeft A initialCode leftLineage
      leftInput.1 leftInput.2
    let candidate₄ := candidate₃.stepRight A initialCode rightLineage₂
      rightInput₂.1 rightInput₂.2
    have hc₀ : candidate₀ ∈
        (profiledOpenPhysicalRecutPhaseInitial A {move}).candidates :=
      mem_profiledOpenPhysicalRecutPhaseInitial A {move} move (by simp)
    have hc₁ := ProfiledOpenPhysicalRecutPhase.mem_advance_right
      A initialCode (profiledOpenPhysicalRecutPhaseInitial A {move})
      {rightLineage₀} {leftLineage} candidate₀ rightLineage₀
      rightInput₀.1 rightInput₀.2 hc₀ (by simp)
    have hc₂ := ProfiledOpenPhysicalRecutPhase.mem_advance_right
      A initialCode
      ((profiledOpenPhysicalRecutPhaseInitial A {move}).advance A initialCode
        {rightLineage₀} {leftLineage}
        { inputOne := rightInput₀.1, inputTwo := rightInput₀.2,
          graph := .right })
      {rightLineage₁} {leftLineage} candidate₁ rightLineage₁
      rightInput₁.1 rightInput₁.2 hc₁ (by simp)
    have hc₃ := ProfiledOpenPhysicalRecutPhase.mem_advance_left
      A initialCode
      (((profiledOpenPhysicalRecutPhaseInitial A {move}).advance A initialCode
        {rightLineage₀} {leftLineage}
        { inputOne := rightInput₀.1, inputTwo := rightInput₀.2,
          graph := .right }).advance A initialCode
        {rightLineage₁} {leftLineage}
        { inputOne := rightInput₁.1, inputTwo := rightInput₁.2,
          graph := .right })
      {rightLineage₂} {leftLineage} candidate₂ leftLineage
      leftInput.1 leftInput.2 hc₂ (by simp)
    have hc₄ := ProfiledOpenPhysicalRecutPhase.mem_advance_right
      A initialCode
      ((((profiledOpenPhysicalRecutPhaseInitial A {move}).advance A initialCode
        {rightLineage₀} {leftLineage}
        { inputOne := rightInput₀.1, inputTwo := rightInput₀.2,
          graph := .right }).advance A initialCode
        {rightLineage₁} {leftLineage}
        { inputOne := rightInput₁.1, inputTwo := rightInput₁.2,
          graph := .right }).advance A initialCode
        {rightLineage₂} {leftLineage}
        { inputOne := leftInput.1, inputTwo := leftInput.2,
          graph := .left })
      {rightLineage₂} {leftLineage} candidate₃ rightLineage₂
      rightInput₂.1 rightInput₂.2 hc₃ (by simp)
    let phase₄test :=
      ((((profiledOpenPhysicalRecutPhaseInitial A {move}).advance A initialCode
        {rightLineage₀} {leftLineage}
        { inputOne := rightInput₀.1, inputTwo := rightInput₀.2,
          graph := .right }).advance A initialCode
        {rightLineage₁} {leftLineage}
        { inputOne := rightInput₁.1, inputTwo := rightInput₁.2,
          graph := .right }).advance A initialCode
        {rightLineage₂} {leftLineage}
        { inputOne := leftInput.1, inputTwo := leftInput.2,
          graph := .left }).advance A initialCode
        {rightLineage₂} {leftLineage}
        { inputOne := rightInput₂.1, inputTwo := rightInput₂.2,
          graph := .right }
    change candidate₄ ∈ phase₄test.candidates at hc₄
    let phase₅test := phase₄test.advance A initialCode
      {rightLineage₂} {leftLineage}
      { inputOne := closingInput.1, inputTwo := closingInput.2,
        graph := .both }
    have hc₅ : candidate₄ ∈ phase₅test.candidates := by
      change candidate₄ ∈ phase₄test.candidates
      exact hc₄
    change
      profiledOpenWitnessedTableQueryWithDirection A initialCode carriedQuery
          .right
          ⟨move, profiledOpenIndexedDirectionSummarize A initialCode move
            (profiledOpenPhysicalRecutPairTestDirection
              rightLineage₀ rightLineage₁ leftLineage rightLineage₂
              rightInput₀ rightInput₁ leftInput rightInput₂ closingInput
              rightPivot leftPivot)⟩ ∈
        phase₅test.finishedQueriesForSide A initialCode carriedQuery .right
          {rightPivot} {leftPivot} closingInput.1 closingInput.2
    rw [← profiledOpenPhysicalRecutPairTest_finish_eq_summary A initialCode
      move rightLineage₀ rightLineage₁ leftLineage rightLineage₂
      rightInput₀ rightInput₁ leftInput rightInput₂ closingInput
      rightPivot leftPivot]
    exact ProfiledOpenPhysicalRecutPhase.mem_finishedQueriesForSide
      A initialCode _ carriedQuery .right {rightPivot} {leftPivot} candidate₄
      rightPivot leftPivot closingInput.1 closingInput.2 hc₅ (by simp)
      (by simp)

/-! ## The single honest model seam -/

/-- The exact remaining physical-history coverage statement.

At a closing `both` round, the literal reachable query consumed by the
witnessed branch must occur among the queries obtained by finishing the
retained accumulator candidates and the retained row-carrying pivots.  This
predicate asserts membership only.  It neither selects a unique accumulator
nor identifies the two `PairedEntryRow`s, and hence cannot hide the
permanently-lost-bit obstruction.

The concrete physical compiler should prove this invariant inductively using
`mem_advance_right`, `mem_advance_left`, and `mem_finishedQueriesForSide`.
Once proved, the proof-side distinguished candidate may select the literal
member while the local belief machine retains the whole finite set. -/
def ProfiledOpenWitnessedPhysicalEpochQueryCovered
    (phase : ProfiledOpenPhysicalRecutPhase A)
    (carriedQuery literalQuery : ProfiledOpenWitnessedTableQuery A initialCode)
    (side : IndexedLineageSide)
    (rightPivots leftPivots : Finset (IndexedLineageCandidate I))
    (closingRound : EnvironmentRound In₁ In₂) : Prop :=
  closingRound.graph = .both ∧
    literalQuery ∈ phase.finishedQueriesForSide A initialCode carriedQuery
      side rightPivots leftPivots closingRound.inputOne closingRound.inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
