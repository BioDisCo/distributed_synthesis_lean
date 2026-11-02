/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceFiniteDelayedBoundaryFork
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenActivePivotFromProvenance

/-!
# Selecting the active pivot of a finite provenance state

The delayed-boundary recurrence must never use a hard-wired lineage after
root deduplication.  This file selects one member of the current side's
finite active carrier, upgrades it to an active reflexive pivot using
provenance validity, and uses it in one zero-open distinguished step.

The side and selected lineage are proof-side global witness data.  Neither is
read by either local process.
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

private abbrev PivotState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev PivotQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

/-- The actual descriptor of every represented finite state is
provenance-valid.  This is the `MoveRealizesAt.valid` component already stored
in policy liveness. -/
theorem profiledOpenProvenancePolicyDistinguished_valid
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    ProfiledOpenIndexedProvenanceValid A strategy hwin basis descriptor.code
      descriptor.moveIdentity := by
  have hall := profiledOpenProvenancePolicyDistinguished_mem_live_valid A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current
  exact hall.2.1.2.2.2.1

omit [Inhabited I] [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- A realizable finite tag retains its literal right pivot in the selected
raw representative. -/
theorem profiledOpenIndexedRawDirectionOfFiniteTag_rightPivot_eq
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hreal : tag.RealizableAt A code move) :
    (profiledOpenIndexedRawDirectionOfFiniteTag A code move tag).rightPivot =
      tag.2.rightPivot := by
  rw [profiledOpenIndexedRawDirectionOfFiniteTag_eq_realization A code move
    tag hreal]
  let realization := profiledOpenIndexedFiniteDirectionRealization A code move
    tag hreal
  change realization.raw.rightPivot = tag.2.rightPivot
  rcases realization with ⟨hmove, raw, hsummary⟩
  cases hmove
  have hpivot := congrArg
    (fun summary : ProfiledOpenIndexedDirectionSummary A (I := I) tag.1 =>
      summary.rightPivot) hsummary
  simpa [profiledOpenIndexedDirectionSummarize] using hpivot

omit [Inhabited I] [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- Left-pivot mirror. -/
theorem profiledOpenIndexedRawDirectionOfFiniteTag_leftPivot_eq
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hreal : tag.RealizableAt A code move) :
    (profiledOpenIndexedRawDirectionOfFiniteTag A code move tag).leftPivot =
      tag.2.leftPivot := by
  rw [profiledOpenIndexedRawDirectionOfFiniteTag_eq_realization A code move
    tag hreal]
  let realization := profiledOpenIndexedFiniteDirectionRealization A code move
    tag hreal
  change realization.raw.leftPivot = tag.2.leftPivot
  rcases realization with ⟨hmove, raw, hsummary⟩
  cases hmove
  have hpivot := congrArg
    (fun summary : ProfiledOpenIndexedDirectionSummary A (I := I) tag.1 =>
      summary.leftPivot) hsummary
  simpa [profiledOpenIndexedDirectionSummarize] using hpivot

/-- A nonempty current-side carrier supplies a finite active reflexive pivot.
The row `.first` is harmless: provenance validity proves row-functionality
and reflexivity for every selected active candidate. -/
noncomputable def profiledOpenProvenancePolicyActivePivotOfCarrier
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (hnonempty : (profiledOpenIndexedActiveLineageCarrier A side
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        current).code).Nonempty) :
    ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package current side := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let lineage := Classical.choose hnonempty
  have hlineage := Classical.choose_spec hnonempty
  let pivot : IndexedLineageCandidate I := (lineage, .first)
  let direction := profiledOpenPhysicalStrictHistoryDirection
    (In₁ := In₁) (In₂ := In₂) [] pivot pivot default default
  refine ⟨pivot, ?_⟩
  cases side with
  | right =>
      rw [mem_profiledOpenIndexedActiveLineageCarrier_iff] at hlineage
      have hslot : descriptor.code.rightSlots direction.rightPivot.1 ≠ none :=
        by simpa [direction, pivot, lineage,
          profiledOpenIndexedBiBeliefCurrentSlots] using hlineage
      have hactive :=
        profiledOpenIndexedProvenanceValid_activeReflexiveRightPivot A strategy
          hwin basis descriptor.code descriptor.moveIdentity direction
            (profiledOpenProvenancePolicyDistinguished_valid A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
              current) hslot
      simpa [ProfiledOpenProvenancePolicyActiveReflexivePivotAt, direction,
        pivot, descriptor] using hactive
  | left =>
      rw [mem_profiledOpenIndexedActiveLineageCarrier_iff] at hlineage
      have hslot : descriptor.code.leftSlots direction.leftPivot.1 ≠ none :=
        by simpa [direction, pivot, lineage,
          profiledOpenIndexedBiBeliefCurrentSlots] using hlineage
      have hactive :=
        profiledOpenIndexedProvenanceValid_activeReflexiveLeftPivot A strategy
          hwin basis descriptor.code descriptor.moveIdentity direction
            (profiledOpenProvenancePolicyDistinguished_valid A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
              current) hslot
      simpa [ProfiledOpenProvenancePolicyActiveReflexivePivotAt, direction,
        pivot, descriptor] using hactive

/-! ## One active-pivot zero-open step -/

/-- Put the selected pivot in the relevant right coordinate. -/
def profiledOpenProvenancePolicySelectedRightPivot
    (side : IndexedLineageSide) (selected other : IndexedLineageCandidate I) :
    IndexedLineageCandidate I :=
  match side with
  | .right => selected
  | .left => other

/-- Put the selected pivot in the relevant left coordinate. -/
def profiledOpenProvenancePolicySelectedLeftPivot
    (side : IndexedLineageSide) (selected other : IndexedLineageCandidate I) :
    IndexedLineageCandidate I :=
  match side with
  | .right => other
  | .left => selected

omit [Fintype I] [Inhabited I] in
@[simp] theorem profiledOpenProvenancePolicySelectedRightPivot_self
    (side : IndexedLineageSide) (pivot : IndexedLineageCandidate I) :
    profiledOpenProvenancePolicySelectedRightPivot side pivot pivot = pivot := by
  cases side <;> rfl

omit [Fintype I] [Inhabited I] in
@[simp] theorem profiledOpenProvenancePolicySelectedLeftPivot_self
    (side : IndexedLineageSide) (pivot : IndexedLineageCandidate I) :
    profiledOpenProvenancePolicySelectedLeftPivot side pivot pivot = pivot := by
  cases side <;> rfl

/-- Zero-open query whose current-side pivot is the active selector and whose
unused opposite pivot is arbitrary finite data. -/
noncomputable def profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (other : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) : PivotQuery A initialCode :=
  profiledOpenProvenancePolicyZeroOpenQueryOfState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package current side
      (profiledOpenProvenancePolicySelectedRightPivot side selected.pivot other)
      (profiledOpenProvenancePolicySelectedLeftPivot side selected.pivot other)
      inputOne inputTwo

/-- The selected-pivot query remains an honest empty-past current-code tag. -/
theorem profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_realizableAt
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (other : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    (profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
      side selected other inputOne inputTwo).1.2.RealizableAt A descriptor.code
        descriptor.moveIdentity := by
  exact profiledOpenProvenancePolicyZeroOpenQueryOfState_realizableAt A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
    package current side
      (profiledOpenProvenancePolicySelectedRightPivot side selected.pivot other)
      (profiledOpenProvenancePolicySelectedLeftPivot side selected.pivot other)
      inputOne inputTwo

/-- Any finite distinguished step has the exact finite-tag child code. -/
theorem profiledOpenProvenancePolicyDistinguishedStep_code_eq_finiteTagNext
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : PivotQuery A initialCode) :
    let source :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next).code =
      profiledOpenIndexedBiBeliefNextFiniteTag A source.code
        source.moveIdentity query.1.2 := by
  let source :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
  have hstate :=
    profiledOpenProvenancePolicyDistinguishedStep_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current query
  have hmove :=
    (profiledOpenProvenancePolicyDistinguishedStep_moveRealizes A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query).1
  have hsuccessor := hmove.2 query.1.2
  exact congrArg Prod.fst (hstate.trans hsuccessor)

/-- The raw finite-tag representative of the selected query has an active
reflexive pivot on the proof-side current side. -/
theorem
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_raw_active
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (other : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    let query := profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current side selected other inputOne inputTwo
    ProfiledOpenIndexedActiveReflexivePivot A descriptor.code side
      (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
        descriptor.moveIdentity query.1.2) := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let query := profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current side selected other inputOne inputTwo
  have hreal :=
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_realizableAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current side selected other inputOne inputTwo
  have hmove :=
    (profiledOpenProvenancePolicyDistinguishedStep_moveRealizes A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query).1
  cases side with
  | right =>
      have hpivot := profiledOpenIndexedRawDirectionOfFiniteTag_rightPivot_eq A
        descriptor.code descriptor.moveIdentity query.1.2 hreal
      have hslot : descriptor.code.rightSlots
          (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
            descriptor.moveIdentity query.1.2).rightPivot.1 ≠ none := by
        rw [hpivot]
        exact selected.active.1
      exact
        profiledOpenIndexedProvenanceCodePolicyMoveRealizesAt_activeReflexivePivot
          A strategy hwin basis initialCode codePolicy descriptor.1
            descriptor.moveIdentity
            (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
              descriptor.moveIdentity query.1.2) .right hmove hslot
  | left =>
      have hpivot := profiledOpenIndexedRawDirectionOfFiniteTag_leftPivot_eq A
        descriptor.code descriptor.moveIdentity query.1.2 hreal
      have hslot : descriptor.code.leftSlots
          (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
            descriptor.moveIdentity query.1.2).leftPivot.1 ≠ none := by
        rw [hpivot]
        exact selected.active.1
      exact
        profiledOpenIndexedProvenanceCodePolicyMoveRealizesAt_activeReflexivePivot
          A strategy hwin basis initialCode codePolicy descriptor.1
            descriptor.moveIdentity
            (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
              descriptor.moveIdentity query.1.2) .left hmove hslot

/-- The exact finite distinguished successor has a nonempty carrier on the
opposite side.  This is the kernel-checked replacement for assuming that a
fixed default lineage survives deduplication. -/
theorem
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_nextCarrier_nonempty
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (other : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let query := profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current side selected other inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    (profiledOpenIndexedActiveLineageCarrier A side.other
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next).code
      ).Nonempty := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let query := profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current side selected other inputOne inputTwo
  let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
  let raw := profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
    descriptor.moveIdentity query.1.2
  have hactive : ProfiledOpenIndexedActiveReflexivePivot A descriptor.code side
      raw :=
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_raw_active A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current side selected other inputOne inputTwo
  have hcarrier :=
    profiledOpenIndexedActiveLineageCarrier_next_other_nonempty A
      descriptor.code descriptor.moveIdentity raw side hactive
  have hcode :=
    profiledOpenProvenancePolicyDistinguishedStep_code_eq_finiteTagNext A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current query
  change (profiledOpenIndexedActiveLineageCarrier A side.other
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next).code
    ).Nonempty
  rw [hcode]
  simpa only [profiledOpenIndexedBiBeliefNextFiniteTag, raw] using hcarrier

/-- Select the next finite active pivot from the nonempty opposite carrier.
The selected lineage may differ after deduplication, but remains proof-side
finite data. -/
noncomputable def
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_nextPivot
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (other : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let query := profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current side selected other inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package next side.other := by
  let query := profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current side selected other inputOne inputTwo
  let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
  exact profiledOpenProvenancePolicyActivePivotOfCarrier A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package next side.other
      (profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_nextCarrier_nonempty
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package current side selected other inputOne inputTwo)

/-! ## Finite proof-erased alternating selector -/

/-- The finite proof-side state needed to iterate active-pivot steps.  Its
`side` records which carrier the mathematical induction follows; it is not a
local observation and no process branches on it.  Likewise, `activePivot`
stores only one finite candidate plus a proposition, not a leader bit. -/
structure ProfiledOpenProvenancePolicyAlternatingActiveState where
  current : PivotState A strategy hwin basis initialCode codePolicy fixedPolicy
    point initialRoot package
  side : IndexedLineageSide
  activePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package current side

/-- The alternating selector is genuinely finite.  The active proof is erased;
the injective code retains only the raw distinguished state, side, and finite
pivot candidate. -/
noncomputable instance
    profiledOpenProvenancePolicyAlternatingActiveState_fintype :
    Fintype (ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package) := by
  classical
  let encode := fun state :
      ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package =>
    (state.current, state.side, state.activePivot.pivot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftCurrent, leftSide, leftPivot⟩
    rcases right with ⟨rightCurrent, rightSide, rightPivot⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, hpivot⟩
    cases leftPivot with
    | mk leftCandidate leftActive =>
        cases rightPivot with
        | mk rightCandidate rightActive =>
            dsimp only at hpivot
            cases hpivot
            rfl)

/-- Seed the finite alternating selector from one nonempty active carrier. -/
noncomputable def
    profiledOpenProvenancePolicyAlternatingActiveStateOfCarrier
    (current : PivotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (hnonempty : (profiledOpenIndexedActiveLineageCarrier A side
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        current).code).Nonempty) :
    ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package where
  current := current
  side := side
  activePivot := profiledOpenProvenancePolicyActivePivotOfCarrier A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current side hnonempty

/-- The one-letter query emitted from an alternating selector state.  The
selected pivot occupies the current-side coordinate; the unused coordinate is
filled by the same finite candidate and need not be active. -/
noncomputable def
    ProfiledOpenProvenancePolicyAlternatingActiveState.query
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) : PivotQuery A initialCode :=
  profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package state.current
      state.side state.activePivot state.activePivot.pivot inputOne inputTwo

/-- The literal physical direction represented by the zero-open query.  This
definition deliberately exposes the exact empty strict history, both closing
inputs, and the full selected lineage/row candidate. -/
def ProfiledOpenProvenancePolicyAlternatingActiveState.direction
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  profiledOpenPhysicalStrictHistoryDirection [] state.activePivot.pivot
    state.activePivot.pivot inputOne inputTwo

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.direction_rightPivot
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.direction A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package inputOne inputTwo).rightPivot =
      state.activePivot.pivot := rfl

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.direction_leftPivot
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.direction A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package inputOne inputTwo).leftPivot =
      state.activePivot.pivot := rfl

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.direction_rightInput
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.direction A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package inputOne inputTwo).rightInput =
      (inputTwo, inputOne) := rfl

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.direction_leftInput
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.direction A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package inputOne inputTwo).leftInput =
      (inputOne, inputTwo) := rfl

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.direction_rightPast
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.direction A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package inputOne inputTwo).rightTaggedPast = [] := rfl

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.direction_leftPast
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.direction A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package inputOne inputTwo).leftTaggedPast = [] := rfl

/-- The finite query tag is exactly the summary of the displayed physical
direction.  Thus the proof does not merely retain an activity bit: it retains
the selected row, the closing inputs, and the empty-history direction used to
compute the child anchor. -/
theorem ProfiledOpenProvenancePolicyAlternatingActiveState.query_tag
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor := profiledOpenProvenancePolicyDistinguishedDescriptor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package state.current
    (state.query A strategy hwin basis initialCode codePolicy fixedPolicy point
      initialRoot package inputOne inputTwo).1.2 =
      ⟨descriptor.moveIdentity,
        profiledOpenIndexedDirectionSummarize A descriptor.code
          descriptor.moveIdentity
            (state.direction A strategy hwin basis initialCode codePolicy
              fixedPolicy point initialRoot package inputOne inputTwo)⟩ := by
  let descriptor := profiledOpenProvenancePolicyDistinguishedDescriptor A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package state.current
  let direction := state.direction A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package inputOne inputTwo
  have hfinish := profiledOpenIndexedDirectionAccumulator_finish_scan A
    descriptor.code descriptor.moveIdentity direction
  have hsummary :
      (profiledOpenIndexedDirectionAccumulatorInitial A descriptor.moveIdentity
        ).finish A state.activePivot.pivot (inputTwo, inputOne)
          state.activePivot.pivot (inputOne, inputTwo) =
        profiledOpenIndexedDirectionSummarize A descriptor.code
          descriptor.moveIdentity direction := by
    simpa only [ProfiledOpenProvenancePolicyAlternatingActiveState.direction,
      profiledOpenIndexedDirectionAccumulatorScan, List.foldl_nil] using hfinish
  simpa only [ProfiledOpenProvenancePolicyAlternatingActiveState.query,
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot,
    profiledOpenProvenancePolicyZeroOpenQueryOfState,
    profiledOpenProvenancePolicyClosingQueryOfState,
    profiledOpenWitnessedTableQueryWithDirection_tag,
    ProfiledOpenPhysicalDirectionAccumulatorCandidate.finish,
    profiledOpenProvenancePolicySelectedRightPivot_self,
    profiledOpenProvenancePolicySelectedLeftPivot_self,
    ProfiledOpenProvenancePolicyAlternatingActiveState.direction] using
      congrArg (Sigma.mk descriptor.moveIdentity) hsummary

/-- Endpoint-bearing root computed at the selected lineage/row before root
deduplication. -/
noncomputable def
    ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) : ProfiledOpenClassifiedAnchor A :=
  let descriptor := profiledOpenProvenancePolicyDistinguishedDescriptor A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package state.current
  match state.side with
  | .right => profiledOpenIndexedRightChildAnchor A descriptor.code
      descriptor.moveIdentity
        (state.direction A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo)
        state.activePivot.pivot
  | .left => profiledOpenIndexedLeftChildAnchor A descriptor.code
      descriptor.moveIdentity
        (state.direction A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo)
        state.activePivot.pivot

/-- The side-relevant ordered child code, before root deduplication. -/
noncomputable def
    ProfiledOpenProvenancePolicyAlternatingActiveState.selectedRawChildCode
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  let descriptor := profiledOpenProvenancePolicyDistinguishedDescriptor A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package state.current
  match state.side with
  | .right => profiledOpenIndexedRightRawChildCode A descriptor.code
      descriptor.moveIdentity
        (state.direction A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo)
  | .left => profiledOpenIndexedLeftRawChildCode A descriptor.code
      descriptor.moveIdentity
        (state.direction A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo)

/-- Exact selected signature before deduplication: at the selected lineage the
raw child stores the selected `PairedEntryRow` together with the concrete
endpoint-bearing child anchor. -/
theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.selectedRawChildCode_apply
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    state.selectedRawChildCode A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package inputOne inputTwo
        state.activePivot.pivot.1 =
      some (state.activePivot.pivot.2,
        state.selectedChildAnchor A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package inputOne inputTwo) := by
  rcases state with ⟨current, side, selected⟩
  cases side with
  | right =>
      rcases selected.active with ⟨hpivot, hfunctional, hreflexive⟩
      simpa only [
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedRawChildCode,
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor,
        ProfiledOpenProvenancePolicyAlternatingActiveState.direction,
        profiledOpenIndexedRightRawChildCode] using
        ((profiledOpenIndexedGatedChildCode_eq_some_iff_of_active A
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.rightSlots
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.rightPattern
        (profiledOpenIndexedRightChildAnchor A
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            current).code
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            current).moveIdentity
          (profiledOpenPhysicalStrictHistoryDirection [] selected.pivot
            selected.pivot inputOne inputTwo))
          selected.pivot hfunctional selected.pivot.1 selected.pivot.2 hpivot
            hpivot).2 hreflexive)
  | left =>
      rcases selected.active with ⟨hpivot, hfunctional, hreflexive⟩
      simpa only [
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedRawChildCode,
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor,
        ProfiledOpenProvenancePolicyAlternatingActiveState.direction,
        profiledOpenIndexedLeftRawChildCode] using
        ((profiledOpenIndexedGatedChildCode_eq_some_iff_of_active A
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.leftSlots
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.leftPattern
        (profiledOpenIndexedLeftChildAnchor A
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            current).code
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            current).moveIdentity
          (profiledOpenPhysicalStrictHistoryDirection [] selected.pivot
            selected.pivot inputOne inputTwo))
          selected.pivot hfunctional selected.pivot.1 selected.pivot.2 hpivot
            hpivot).2 hreflexive)

/-- Root deduplication may change the representative lineage and stored row,
but it cannot erase the endpoint-bearing root emitted at the selected row. -/
theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor_survivesDeduplication
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.selectedRawChildCode A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package inputOne inputTwo).deduplicateRoots
        |>.RootOccurs
          (state.selectedChildAnchor A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package inputOne inputTwo) := by
  apply IndexedLineageChildCode.rootOccurs_deduplicateRoots
  exact ⟨state.activePivot.pivot.1, state.activePivot.pivot.2,
    state.selectedRawChildCode_apply A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package inputOne inputTwo⟩

/-- Normalized target-slot form consumed by the epoch-priority adapter.  The
slot may use a deduplicated representative lineage, while
`selectedRawChildCode_apply` above retains the original selected row needed to
identify the physical endpoint. -/
theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.exists_targetSlot
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor := profiledOpenProvenancePolicyDistinguishedDescriptor A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package state.current
    ∃ lineage : I,
      profiledOpenIndexedBiBeliefCurrentSlots A state.side.other
          (profiledOpenIndexedBiBeliefNext A descriptor.code
            descriptor.moveIdentity
            (state.direction A strategy hwin basis initialCode codePolicy
              fixedPolicy point initialRoot package inputOne inputTwo)) lineage =
        some (state.selectedChildAnchor A strategy hwin basis initialCode
          codePolicy fixedPolicy point initialRoot package inputOne inputTwo) := by
  rcases state with ⟨current, side, selected⟩
  cases side with
  | right =>
      rcases
        (ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor_survivesDeduplication
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package ⟨current, .right, selected⟩ inputOne inputTwo) with
        ⟨lineage, row, hslot⟩
      refine ⟨lineage, ?_⟩
      have hroot := IndexedLineageChildCode.rootSlots_eq_some_of _ hslot
      simpa only [IndexedLineageSide.other,
        profiledOpenIndexedBiBeliefCurrentSlots_left,
        profiledOpenIndexedBiBeliefNext_leftSlots,
        profiledOpenIndexedRightChildCode,
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedRawChildCode,
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor,
        ProfiledOpenProvenancePolicyAlternatingActiveState.direction] using hroot
  | left =>
      rcases
        (ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor_survivesDeduplication
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package ⟨current, .left, selected⟩ inputOne inputTwo) with
        ⟨lineage, row, hslot⟩
      refine ⟨lineage, ?_⟩
      have hroot := IndexedLineageChildCode.rootSlots_eq_some_of _ hslot
      simpa only [IndexedLineageSide.other,
        profiledOpenIndexedBiBeliefCurrentSlots_right,
        profiledOpenIndexedBiBeliefNext_rightSlots,
        profiledOpenIndexedLeftChildCode,
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedRawChildCode,
        ProfiledOpenProvenancePolicyAlternatingActiveState.selectedChildAnchor,
        ProfiledOpenProvenancePolicyAlternatingActiveState.direction] using hroot
/-- Advance the exact distinguished state and alternate the proof-side carrier.
The next active pivot is selected from the carrier whose nonemptiness follows
from the current pivot's active-reflexive law. -/
noncomputable def
    ProfiledOpenProvenancePolicyAlternatingActiveState.step
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package where
  current := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package state.current
      (state.query A strategy hwin basis initialCode codePolicy fixedPolicy point
        initialRoot package inputOne inputTwo)
  side := state.side.other
  activePivot :=
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_nextPivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        state.current state.side state.activePivot state.activePivot.pivot
          inputOne inputTwo

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.step_current
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.step A strategy hwin basis initialCode codePolicy fixedPolicy point
      initialRoot package inputOne inputTwo).current =
      profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package state.current
          (state.query A strategy hwin basis initialCode codePolicy fixedPolicy
            point initialRoot package inputOne inputTwo) := rfl

@[simp] theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.step_side
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    (state.step A strategy hwin basis initialCode codePolicy fixedPolicy point
      initialRoot package inputOne inputTwo).side = state.side.other := rfl

/-- The packaged step is the exact rational-policy successor, not merely a
state having an equivalent summary. -/
theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.step_policySuccessor
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    let query := state.query A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package inputOne inputTwo
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package
      (state.step A strategy hwin basis initialCode codePolicy fixedPolicy point
        initialRoot package inputOne inputTwo).current).1 =
      codePolicy.successor
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          state.current).1 query.1.2 := by
  dsimp only
  exact profiledOpenProvenancePolicyDistinguishedStep_policySuccessor A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      state.current _

/-- The code component of the packaged step is the canonical finite-tag next
code. -/
theorem
    ProfiledOpenProvenancePolicyAlternatingActiveState.step_code
    (state : ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (inputOne : In₁) (inputTwo : In₂) :
    let query := state.query A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package inputOne inputTwo
    let source := profiledOpenProvenancePolicyDistinguishedDescriptor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        state.current
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package
      (state.step A strategy hwin basis initialCode codePolicy fixedPolicy point
        initialRoot package inputOne inputTwo).current).code =
      profiledOpenIndexedBiBeliefNextFiniteTag A source.code
        source.moveIdentity query.1.2 := by
  dsimp only
  exact
    profiledOpenProvenancePolicyDistinguishedStep_code_eq_finiteTagNext A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package state.current _
end

end DetParityAutomaton

end DistributedSynthesis
