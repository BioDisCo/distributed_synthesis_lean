/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceFiniteActivePivotStep

/-!
# Active-pivot synchronization of the finite delayed boundary fork

This file connects a literal finite strict history to the delayed
direct-versus-repeated boundary fork.  One active pivot at the source is
enough: closing the strict prefix produces a nonempty opposite carrier at the
exact middle successor, from which the fresh zero-open pivot is selected.

All three tags retain their literal physical meanings:

* the direct tag summarizes `strictPrefix ++ [lastStrict]` and closes on the
  simultaneous inputs;
* the strict-close tag summarizes `strictPrefix` and closes on the retained
  strict letter;
* the middle tag has empty history and closes on the simultaneous inputs.

The side and pivots are finite proof-side data.  No process observes a strict
leader, orientation, or selected fork arm.
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

private abbrev ActiveForkState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev ActiveForkQuery :=
  ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
    max i u v x y s, max i u v x y s} A initialCode

/-- An active pivot whose lineage is known to store one specified physical
root.  The active pivot alone is enough for carrier persistence; `root_eq`
is the stronger synchronization datum needed to follow the actually emitted
recut through root deduplication. -/
structure ProfiledOpenProvenancePolicyRootAlignedActivePivotAt
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide) (root : ProfiledOpenClassifiedAnchor A) where
  activePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package current side
  root_eq :
    profiledOpenIndexedBiBeliefCurrentSlots A side
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            current).code activePivot.pivot.1 =
      some root

/-! ## A selected pivot through an arbitrary realizable query -/

/-- A realizable query whose relevant pivot is the selected active pivot has
an active-reflexive canonical raw representative. -/
theorem profiledOpenProvenancePolicyQuery_raw_active_of_selectedPivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (query : ActiveForkQuery A initialCode)
    (hreal : query.1.2.RealizableAt A
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current).code
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
        ).moveIdentity)
    (hpivot : match side with
      | .right => query.1.2.2.rightPivot = selected.pivot
      | .left => query.1.2.2.leftPivot = selected.pivot) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    ProfiledOpenIndexedActiveReflexivePivot A descriptor.code side
      (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
        descriptor.moveIdentity query.1.2) := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  have hmove :=
    (profiledOpenProvenancePolicyDistinguishedStep_moveRealizes A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query).1
  cases side with
  | right =>
      have hrawPivot :=
        profiledOpenIndexedRawDirectionOfFiniteTag_rightPivot_eq A
          descriptor.code descriptor.moveIdentity query.1.2 hreal
      have hslot : descriptor.code.rightSlots
          (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
            descriptor.moveIdentity query.1.2).rightPivot.1 ≠ none := by
        rw [hrawPivot, hpivot]
        exact selected.active.1
      exact
        profiledOpenIndexedProvenanceCodePolicyMoveRealizesAt_activeReflexivePivot
          A strategy hwin basis initialCode codePolicy descriptor.1
            descriptor.moveIdentity
            (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
              descriptor.moveIdentity query.1.2) .right hmove hslot
  | left =>
      have hrawPivot :=
        profiledOpenIndexedRawDirectionOfFiniteTag_leftPivot_eq A
          descriptor.code descriptor.moveIdentity query.1.2 hreal
      have hslot : descriptor.code.leftSlots
          (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
            descriptor.moveIdentity query.1.2).leftPivot.1 ≠ none := by
        rw [hrawPivot, hpivot]
        exact selected.active.1
      exact
        profiledOpenIndexedProvenanceCodePolicyMoveRealizesAt_activeReflexivePivot
          A strategy hwin basis initialCode codePolicy descriptor.1
            descriptor.moveIdentity
            (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
              descriptor.moveIdentity query.1.2) .left hmove hslot

/-- The exact query successor has a nonempty opposite carrier. -/
theorem profiledOpenProvenancePolicyQuery_nextCarrier_nonempty_of_selectedPivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (query : ActiveForkQuery A initialCode)
    (hreal : query.1.2.RealizableAt A
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current).code
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
        ).moveIdentity)
    (hpivot : match side with
      | .right => query.1.2.2.rightPivot = selected.pivot
      | .left => query.1.2.2.leftPivot = selected.pivot) :
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
  let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
  let raw := profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
    descriptor.moveIdentity query.1.2
  have hactive : ProfiledOpenIndexedActiveReflexivePivot A descriptor.code side
      raw :=
    profiledOpenProvenancePolicyQuery_raw_active_of_selectedPivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current side selected query hreal hpivot
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

/-- Select the active pivot at the exact opposite-side query successor. -/
noncomputable def profiledOpenProvenancePolicyQuery_nextPivot_of_selectedPivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (query : ActiveForkQuery A initialCode)
    (hreal : query.1.2.RealizableAt A
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current).code
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
        ).moveIdentity)
    (hpivot : match side with
      | .right => query.1.2.2.rightPivot = selected.pivot
      | .left => query.1.2.2.leftPivot = selected.pivot) :
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package next side.other := by
  let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
  exact profiledOpenProvenancePolicyActivePivotOfCarrier A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package next side.other
      (profiledOpenProvenancePolicyQuery_nextCarrier_nonempty_of_selectedPivot
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package current side selected query hreal hpivot)

/-! ## Literal strict-history closing query -/

/-- Physical direction with the selected row-carrying pivot in both finite
coordinates.  Only the `side` says which coordinate is semantically used. -/
def profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  profiledOpenPhysicalStrictHistoryDirection history selected.pivot
    selected.pivot inputOne inputTwo

/-- Endpoint-bearing child anchor of the selected row in a literal physical
direction. -/
noncomputable def
    profiledOpenProvenancePolicyPhysicalSelectedChildAnchor
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) : ProfiledOpenClassifiedAnchor A :=
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let direction :=
    profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side selected history inputOne inputTwo
  match side with
  | .right => profiledOpenIndexedRightChildAnchor A descriptor.code
      descriptor.moveIdentity direction selected.pivot
  | .left => profiledOpenIndexedLeftChildAnchor A descriptor.code
      descriptor.moveIdentity direction selected.pivot

/-- Side-relevant ordered child code before root deduplication. -/
noncomputable def
    profiledOpenProvenancePolicyPhysicalSelectedRawChildCode
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let direction :=
    profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side selected history inputOne inputTwo
  match side with
  | .right => profiledOpenIndexedRightRawChildCode A descriptor.code
      descriptor.moveIdentity direction
  | .left => profiledOpenIndexedLeftRawChildCode A descriptor.code
      descriptor.moveIdentity direction

/-- Exact pre-dedup physical signature.  In particular, the selected
`PairedEntryRow` is not replaced by a row recomputed at the closing round. -/
theorem
    profiledOpenProvenancePolicyPhysicalSelectedRawChildCode_apply
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenProvenancePolicyPhysicalSelectedRawChildCode A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        current side selected history inputOne inputTwo selected.pivot.1 =
      some (selected.pivot.2,
        profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current side selected history inputOne inputTwo) := by
  cases side with
  | right =>
      rcases selected.active with ⟨hpivot, hfunctional, hreflexive⟩
      simpa only [
        profiledOpenProvenancePolicyPhysicalSelectedRawChildCode,
        profiledOpenProvenancePolicyPhysicalSelectedChildAnchor,
        profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot,
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
            (profiledOpenPhysicalStrictHistoryDirection history selected.pivot
              selected.pivot inputOne inputTwo))
          selected.pivot hfunctional selected.pivot.1 selected.pivot.2 hpivot
            hpivot).2 hreflexive)
  | left =>
      rcases selected.active with ⟨hpivot, hfunctional, hreflexive⟩
      simpa only [
        profiledOpenProvenancePolicyPhysicalSelectedRawChildCode,
        profiledOpenProvenancePolicyPhysicalSelectedChildAnchor,
        profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot,
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
            (profiledOpenPhysicalStrictHistoryDirection history selected.pivot
              selected.pivot inputOne inputTwo))
          selected.pivot hfunctional selected.pivot.1 selected.pivot.2 hpivot
            hpivot).2 hreflexive)

/-- After deduplication, some target slot still stores the same selected
endpoint-bearing root. -/
theorem
    profiledOpenProvenancePolicyPhysicalSelected_exists_targetSlot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    ∃ lineage : I,
      profiledOpenIndexedBiBeliefCurrentSlots A side.other
          (profiledOpenIndexedBiBeliefNext A descriptor.code
            descriptor.moveIdentity
            (profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot A
              strategy hwin basis initialCode codePolicy fixedPolicy point
                initialRoot package current side selected history inputOne
                  inputTwo)) lineage =
        some
          (profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy
            hwin basis initialCode codePolicy fixedPolicy point initialRoot
              package current side selected history inputOne inputTwo) := by
  let raw := profiledOpenProvenancePolicyPhysicalSelectedRawChildCode A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current side selected history inputOne inputTwo
  let root := profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package current side selected history inputOne inputTwo
  have hraw : raw selected.pivot.1 = some (selected.pivot.2, root) :=
    profiledOpenProvenancePolicyPhysicalSelectedRawChildCode_apply A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current side selected history inputOne inputTwo
  have hoccurs : raw.deduplicateRoots.RootOccurs root :=
    raw.rootOccurs_deduplicateRoots root
      ⟨selected.pivot.1, selected.pivot.2, hraw⟩
  rcases hoccurs with ⟨lineage, row, hslot⟩
  refine ⟨lineage, ?_⟩
  have hroot := IndexedLineageChildCode.rootSlots_eq_some_of _ hslot
  cases side with
  | right =>
      simpa only [IndexedLineageSide.other,
        profiledOpenIndexedBiBeliefCurrentSlots_left,
        profiledOpenIndexedBiBeliefNext_leftSlots,
        profiledOpenIndexedRightChildCode,
        profiledOpenProvenancePolicyPhysicalSelectedRawChildCode,
        profiledOpenProvenancePolicyPhysicalSelectedChildAnchor,
        profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot, raw,
        root] using hroot
  | left =>
      simpa only [IndexedLineageSide.other,
        profiledOpenIndexedBiBeliefCurrentSlots_right,
        profiledOpenIndexedBiBeliefNext_rightSlots,
        profiledOpenIndexedLeftChildCode,
        profiledOpenProvenancePolicyPhysicalSelectedRawChildCode,
        profiledOpenProvenancePolicyPhysicalSelectedChildAnchor,
        profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot, raw,
        root] using hroot

/-- Close one literal strict history at the current distinguished state. -/
noncomputable def profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) : ActiveForkQuery A initialCode :=
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  profiledOpenProvenancePolicyClosingQueryOfState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package current
      carriedQuery side selected.pivot selected.pivot
      (profiledOpenPhysicalStrictAccumulatorRun A descriptor.code
        descriptor.moveIdentity history) inputOne inputTwo

/-- The closing tag is definitionally linked to the exact displayed physical
history, row-carrying pivot, and closing inputs. -/
theorem profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_tag
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    (profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current carriedQuery side selected history inputOne inputTwo).1.2 =
      ⟨descriptor.moveIdentity,
        profiledOpenIndexedDirectionSummarize A descriptor.code
          descriptor.moveIdentity
          (profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot A strategy
            hwin basis initialCode codePolicy fixedPolicy point initialRoot
              package current side selected history inputOne inputTwo)⟩ := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  simpa only [
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot,
    profiledOpenProvenancePolicyClosingQueryOfState,
    profiledOpenWitnessedTableQueryWithDirection_tag,
    profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot] using
      (profiledOpenPhysicalStrictAccumulatorRun_finish_eq_summary A
        descriptor.code descriptor.moveIdentity history selected.pivot
          selected.pivot inputOne inputTwo)

omit [Inhabited I] [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- A finite tag displayed as the summary of a literal direction computes
exactly that direction's public successor. -/
theorem profiledOpenIndexedBiBeliefNextFiniteTag_eq_of_eq_summary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (htag : tag = ⟨move,
      profiledOpenIndexedDirectionSummarize A code move direction⟩) :
    profiledOpenIndexedBiBeliefNextFiniteTag A code move tag =
      profiledOpenIndexedBiBeliefNext A code move direction := by
  subst tag
  let hreal :
      ProfiledOpenIndexedFiniteDirectionTag.RealizableAt A
        (⟨move, profiledOpenIndexedDirectionSummarize A code move direction⟩ :
          ProfiledOpenIndexedFiniteDirectionTag A (I := I)) code move :=
    ⟨{ move_eq := rfl, raw := direction, summary_eq := rfl }⟩
  rw [profiledOpenIndexedBiBeliefNextFiniteTag_eq_summary A code move _ hreal]
  have hsummary :=
    profiledOpenIndexedBiBeliefNextSummary_summarize A code move direction
  simpa using hsummary

/-- The distinguished successor code of the literal closing query is the
public successor of the displayed physical direction, not merely an
equivalent finite tag. -/
theorem
    profiledOpenProvenancePolicyPhysicalClosingQuery_step_code
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    let query :=
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current carriedQuery side selected history inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next).code =
      profiledOpenIndexedBiBeliefNext A descriptor.code descriptor.moveIdentity
        (profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot A strategy
          hwin basis initialCode codePolicy fixedPolicy point initialRoot package
            current side selected history inputOne inputTwo) := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let query :=
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current carriedQuery side selected history inputOne inputTwo
  let direction :=
    profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side selected history inputOne inputTwo
  calc
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package
      (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
          query)).code =
        profiledOpenIndexedBiBeliefNextFiniteTag A descriptor.code
          descriptor.moveIdentity query.1.2 :=
      profiledOpenProvenancePolicyDistinguishedStep_code_eq_finiteTagNext A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package current query
    _ = profiledOpenIndexedBiBeliefNext A descriptor.code
          descriptor.moveIdentity direction :=
      profiledOpenIndexedBiBeliefNextFiniteTag_eq_of_eq_summary A
        descriptor.code descriptor.moveIdentity query.1.2 direction
          (profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_tag A
            strategy hwin basis initialCode codePolicy fixedPolicy point
              initialRoot package current carriedQuery side selected history
                inputOne inputTwo)

omit [Inhabited I] [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- Every retained root in an opposite-side successor can be equipped with
any requested physical row.  Successor patterns are the active canonical
row diagonal, so this is stronger than merely selecting an arbitrary member
of the nonempty carrier. -/
theorem profiledOpenIndexedActiveReflexivePivotAt_next_other_of_slot_eq_some
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide) (lineage : I) (row : PairedEntryRow)
    (root : ProfiledOpenClassifiedAnchor A)
    (hslot : profiledOpenIndexedBiBeliefCurrentSlots A side.other
      (profiledOpenIndexedBiBeliefNext A code move direction) lineage =
        some root) :
    ProfiledOpenIndexedActiveReflexivePivotAt A
      (profiledOpenIndexedBiBeliefNext A code move direction) side.other
        (lineage, row) := by
  let next := profiledOpenIndexedBiBeliefNext A code move direction
  cases side with
  | right =>
      change next.leftSlots lineage ≠ none ∧
        next.leftPattern.RowFunctionalAt (lineage, row) ∧
        next.leftPattern (lineage, row) (lineage, row) = true
      have hleft : next.leftSlots lineage = some root := by
        simpa only [IndexedLineageSide.other,
          profiledOpenIndexedBiBeliefCurrentSlots_left] using hslot
      refine ⟨by simp [hleft], ?_, ?_⟩
      · rw [profiledOpenIndexedBiBeliefNext_leftPattern]
        exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A
          next.leftSlots (lineage, row)
      · rw [profiledOpenIndexedBiBeliefNext_leftPattern]
        dsimp only [next] at hleft
        simp [profiledOpenIndexedActiveCanonicalRowPattern, hleft]
  | left =>
      change next.rightSlots lineage ≠ none ∧
        next.rightPattern.RowFunctionalAt (lineage, row) ∧
        next.rightPattern (lineage, row) (lineage, row) = true
      have hright : next.rightSlots lineage = some root := by
        simpa only [IndexedLineageSide.other,
          profiledOpenIndexedBiBeliefCurrentSlots_right] using hslot
      refine ⟨by simp [hright], ?_, ?_⟩
      · rw [profiledOpenIndexedBiBeliefNext_rightPattern]
        exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A
          next.rightSlots (lineage, row)
      · rw [profiledOpenIndexedBiBeliefNext_rightPattern]
        dsimp only [next] at hright
        simp [profiledOpenIndexedActiveCanonicalRowPattern, hright]

/-- Literal strict-history closing is realizable at the current descriptor. -/
theorem
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_realizableAt
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    (profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current carriedQuery side selected history inputOne inputTwo).1.2
        |>.RealizableAt A descriptor.code descriptor.moveIdentity := by
  apply profiledOpenProvenancePolicyClosingQueryOfState_realizableAt A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
  exact ⟨history, rfl⟩

/-- The relevant finite-summary pivot is the selected full lineage/row pair. -/
theorem profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_pivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    let query :=
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current carriedQuery side selected history inputOne inputTwo
    match side with
    | .right => query.1.2.2.rightPivot = selected.pivot
    | .left => query.1.2.2.leftPivot = selected.pivot := by
  cases side <;> rfl

/-- Closing a literal strict history therefore supplies the active pivot for
the exact opposite-side middle state. -/
noncomputable def
    profiledOpenProvenancePolicyPhysicalClosingQuery_nextPivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) :
    let query :=
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current carriedQuery side selected history inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package next side.other := by
  apply profiledOpenProvenancePolicyQuery_nextPivot_of_selectedPivot A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
  · exact
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_realizableAt
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package current carriedQuery side selected history inputOne
            inputTwo
  · exact profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_pivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current carriedQuery side selected history inputOne inputTwo

/-- Root-aligned successor selector for one literal closing query.  The
lineage is chosen only after deduplication, from the occurrence of the exact
pre-dedup selected child root; `row` is then installed on that lineage using
the successor's canonical row diagonal. -/
noncomputable def
    profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    let query :=
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current carriedQuery side selected history inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    ProfiledOpenProvenancePolicyRootAlignedActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next
        side.other
        (profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            current side selected history inputOne inputTwo) := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let direction :=
    profiledOpenProvenancePolicyPhysicalDirectionOfActivePivot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side selected history inputOne inputTwo
  let query :=
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current carriedQuery side selected history inputOne inputTwo
  let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
  let root :=
    profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side
        selected history inputOne inputTwo
  have hex :=
    profiledOpenProvenancePolicyPhysicalSelected_exists_targetSlot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current side selected history inputOne inputTwo
  let lineage := Classical.choose hex
  have hlineage := Classical.choose_spec hex
  have hcode :
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next).code =
        profiledOpenIndexedBiBeliefNext A descriptor.code
          descriptor.moveIdentity direction := by
    exact profiledOpenProvenancePolicyPhysicalClosingQuery_step_code A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current carriedQuery side selected history inputOne inputTwo
  have hroot :
      profiledOpenIndexedBiBeliefCurrentSlots A side.other
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              next).code lineage =
        some root := by
    rw [hcode]
    exact hlineage
  refine {
    activePivot := {
      pivot := (lineage, row)
      active := ?_ }
    root_eq := hroot }
  change ProfiledOpenIndexedActiveReflexivePivotAt A
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next).code
      side.other (lineage, row)
  rw [hcode]
  exact profiledOpenIndexedActiveReflexivePivotAt_next_other_of_slot_eq_some A
    descriptor.code descriptor.moveIdentity direction side lineage row root
      hlineage

/-- The root-aligned selector installs exactly the requested physical row. -/
@[simp] theorem
    profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot_row
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    let aligned :=
      profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          current carriedQuery side selected history inputOne inputTwo row
    aligned.activePivot.pivot.2 = row := by
  rfl

/-- Named exact-root projection of the aligned successor selector. -/
theorem
    profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot_root_eq
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (carriedQuery : ActiveForkQuery A initialCode)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    let query :=
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current carriedQuery side selected history inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    let aligned :=
      profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          current carriedQuery side selected history inputOne inputTwo row
    profiledOpenIndexedBiBeliefCurrentSlots A side.other
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            next).code aligned.activePivot.pivot.1 =
      some
        (profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            current side selected history inputOne inputTwo) := by
  exact
    (profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current carriedQuery side selected history inputOne inputTwo row).root_eq

/-! ## The active delayed fork -/

omit [Fintype I] [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- Appending one retained strict letter is exactly one accumulator step. -/
theorem profiledOpenPhysicalStrictAccumulatorRun_append_singleton
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (history : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (letter : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenPhysicalStrictAccumulatorRun A code move
        (history ++ [letter]) =
      profiledOpenPhysicalStrictAccumulatorStep A code move
        (profiledOpenPhysicalStrictAccumulatorRun A code move history) letter := by
  rw [profiledOpenPhysicalStrictAccumulatorRun,
    profiledOpenPhysicalStrictAccumulatorRunFrom_append]
  rfl

/-- The strict-close middle selector, fixed to the first zero-open physical
row and aligned with the exact selected child root that survives
deduplication. -/
noncomputable def
    profiledOpenProvenancePolicyFiniteDelayedBoundaryMiddleRootPivot
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)) :
    let query :=
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          source prefixQuery oldSide sourcePivot strictPrefix lastStrict.inputOne
            lastStrict.inputTwo
    let middle := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        query
    ProfiledOpenProvenancePolicyRootAlignedActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package middle
        oldSide.other
        (profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            source oldSide sourcePivot strictPrefix lastStrict.inputOne
              lastStrict.inputTwo) :=
  profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package source
      prefixQuery oldSide sourcePivot strictPrefix lastStrict.inputOne
        lastStrict.inputTwo .first

/-- The safe finite delayed fork.  Its middle pivot is derived from the exact
strict-close successor; it is not an additional hypothesis. -/
noncomputable def
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source
  let prefixAccumulator := profiledOpenPhysicalStrictAccumulatorRun A
    descriptor.code descriptor.moveIdentity strictPrefix
  let strictCloseQuery :=
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        source prefixQuery oldSide sourcePivot strictPrefix lastStrict.inputOne
          lastStrict.inputTwo
  let middle := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package source
      strictCloseQuery
  let middleRootPivot :=
    profiledOpenProvenancePolicyFiniteDelayedBoundaryMiddleRootPivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        source prefixQuery oldSide sourcePivot strictPrefix lastStrict
  exact profiledOpenProvenancePolicyFiniteDelayedBoundaryFork A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package source
      prefixQuery fullQuery oldSide sourcePivot.pivot sourcePivot.pivot
        middleRootPivot.activePivot.pivot middleRootPivot.activePivot.pivot
          prefixAccumulator lastStrict bothInputOne bothInputTwo

/-- Both middle coordinates of the fork are the same exact-root aligned
representative selected after strict-close deduplication. -/
@[simp] theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_middlePivots
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    let aligned :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryMiddleRootPivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery oldSide sourcePivot strictPrefix lastStrict
    fork.middleRightPivot = aligned.activePivot.pivot ∧
      fork.middleLeftPivot = aligned.activePivot.pivot := by
  exact ⟨rfl, rfl⟩

/-- The aligned middle representative carries the first zero-open row in
both fork coordinates. -/
@[simp] theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_middleRows
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    fork.middleRightPivot.2 = .first ∧
      fork.middleLeftPivot.2 = .first := by
  exact ⟨rfl, rfl⟩

/-- Exact middle-slot signature: the fork does not merely keep some active
lineage, but the lineage storing the strict-close selected child anchor. -/
theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_middleRoot_eq
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    profiledOpenIndexedBiBeliefCurrentSlots A oldSide.other
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            fork.middle).code fork.middleRightPivot.1 =
      some
        (profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            source oldSide sourcePivot strictPrefix lastStrict.inputOne
              lastStrict.inputTwo) := by
  exact
    (profiledOpenProvenancePolicyFiniteDelayedBoundaryMiddleRootPivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        source prefixQuery oldSide sourcePivot strictPrefix lastStrict).root_eq

/-- Both source and middle pivot guards of the safe fork are proved. -/
theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_active
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    fork.ActiveLineagePivots A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package := by
  dsimp only [
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot,
    profiledOpenProvenancePolicyFiniteDelayedBoundaryFork,
    ProfiledOpenProvenancePolicyFiniteDelayedBoundaryFork.ActiveLineagePivots]
  cases oldSide with
  | right =>
      exact ⟨sourcePivot.active,
        (profiledOpenProvenancePolicyFiniteDelayedBoundaryMiddleRootPivot A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package source prefixQuery .right sourcePivot
              strictPrefix lastStrict).activePivot.active⟩
  | left =>
      exact ⟨sourcePivot.active,
        (profiledOpenProvenancePolicyFiniteDelayedBoundaryMiddleRootPivot A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package source prefixQuery .left sourcePivot
              strictPrefix lastStrict).activePivot.active⟩

@[simp] theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_strictCloseQuery
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    (profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
          lastStrict bothInputOne bothInputTwo).strictCloseQuery =
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          source prefixQuery oldSide sourcePivot strictPrefix lastStrict.inputOne
            lastStrict.inputTwo := rfl

/-- The direct query is the literal full strict history; the held-letter
accumulator implementation is observationally exact. -/
theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_directQuery
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    (profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
          lastStrict bothInputOne bothInputTwo).directQuery =
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          source fullQuery oldSide sourcePivot (strictPrefix ++ [lastStrict])
            bothInputOne bothInputTwo := by
  dsimp only [
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot,
    profiledOpenProvenancePolicyFiniteDelayedBoundaryFork,
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot]
  rw [profiledOpenPhysicalStrictAccumulatorRun_append_singleton]

/-- Empty-history zero-open tags retain both literal pivots and inputs. -/
theorem profiledOpenProvenancePolicyZeroOpenQueryOfState_tag
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (rightPivot leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
    (profiledOpenProvenancePolicyZeroOpenQueryOfState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side
        rightPivot leftPivot inputOne inputTwo).1.2 =
      ⟨descriptor.moveIdentity,
        profiledOpenIndexedDirectionSummarize A descriptor.code
          descriptor.moveIdentity
          (profiledOpenPhysicalStrictHistoryDirection [] rightPivot leftPivot
            inputOne inputTwo)⟩ := by
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  simpa only [profiledOpenProvenancePolicyZeroOpenQueryOfState,
    profiledOpenProvenancePolicyClosingQueryOfState,
    profiledOpenWitnessedTableQueryWithDirection_tag] using
      (profiledOpenPhysicalStrictAccumulatorRun_finish_eq_summary A
        descriptor.code descriptor.moveIdentity [] rightPivot leftPivot inputOne
          inputTwo)

/-! ## Exact-root advancement through a zero-open `.both` boundary -/

/-- A zero-open query using the selected pivot in both finite coordinates is
the empty-history specialization of the literal physical closing query. -/
theorem profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_eq_physical
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenProvenancePolicyZeroOpenQueryOfState A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
          side selected.pivot selected.pivot inputOne inputTwo =
      profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          current
          (profiledOpenWitnessedInitialQueryForMove A initialCode
            (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy
              hwin basis initialCode codePolicy fixedPolicy point initialRoot
                package current).moveIdentity)
          side selected [] inputOne inputTwo := by
  rfl

/-- Exact-root successor selector for a zero-open `.both` boundary.  The
selected classified child survives deduplication, while `row` is the sticky
row to install at the new opposite-side lineage. -/
noncomputable def
    profiledOpenProvenancePolicyZeroOpenQuery_nextRootPivot
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    let query :=
      profiledOpenProvenancePolicyZeroOpenQueryOfState A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
          side selected.pivot selected.pivot inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    ProfiledOpenProvenancePolicyRootAlignedActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package next
        side.other
        (profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            current side selected [] inputOne inputTwo) := by
  exact
    profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current
        (profiledOpenWitnessedInitialQueryForMove A initialCode
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).moveIdentity)
        side selected [] inputOne inputTwo row

/-- The zero-open selector installs the requested sticky row. -/
@[simp] theorem profiledOpenProvenancePolicyZeroOpenQuery_nextRootPivot_row
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    (profiledOpenProvenancePolicyZeroOpenQuery_nextRootPivot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side selected inputOne inputTwo row).activePivot.pivot.2 = row := by
  rfl

/-- The zero-open selector's new lineage stores the exact emitted child root,
not merely an arbitrary member of the new carrier. -/
theorem profiledOpenProvenancePolicyZeroOpenQuery_nextRootPivot_root_eq
    (current : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide)
    (selected : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current side)
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    let query :=
      profiledOpenProvenancePolicyZeroOpenQueryOfState A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
          side selected.pivot selected.pivot inputOne inputTwo
    let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        query
    let aligned :=
      profiledOpenProvenancePolicyZeroOpenQuery_nextRootPivot A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current side selected inputOne inputTwo row
    profiledOpenIndexedBiBeliefCurrentSlots A side.other
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            next).code aligned.activePivot.pivot.1 =
      some
        (profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            current side selected [] inputOne inputTwo) := by
  exact
    (profiledOpenProvenancePolicyZeroOpenQuery_nextRootPivot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side selected inputOne inputTwo row).root_eq

/-- Strict-close tag with its exact prefix and retained-letter inputs. -/
theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_strictCloseTag
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
    fork.strictCloseQuery.1.2 =
      ⟨descriptor.moveIdentity,
        profiledOpenIndexedDirectionSummarize A descriptor.code
          descriptor.moveIdentity
          (profiledOpenPhysicalStrictHistoryDirection strictPrefix
            sourcePivot.pivot sourcePivot.pivot lastStrict.inputOne
              lastStrict.inputTwo)⟩ := by
  dsimp only
  rw [profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_strictCloseQuery]
  exact
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_tag A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        source prefixQuery oldSide sourcePivot strictPrefix lastStrict.inputOne
          lastStrict.inputTwo

/-- Direct tag with the held strict letter included and the simultaneous
closing inputs retained. -/
theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_directTag
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source
    fork.directQuery.1.2 =
      ⟨descriptor.moveIdentity,
        profiledOpenIndexedDirectionSummarize A descriptor.code
          descriptor.moveIdentity
          (profiledOpenPhysicalStrictHistoryDirection
            (strictPrefix ++ [lastStrict]) sourcePivot.pivot sourcePivot.pivot
              bothInputOne bothInputTwo)⟩ := by
  dsimp only
  rw [profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_directQuery]
  exact
    profiledOpenProvenancePolicyPhysicalClosingQueryOfActivePivot_tag A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        source fullQuery oldSide sourcePivot (strictPrefix ++ [lastStrict])
          bothInputOne bothInputTwo

/-- Middle zero-open tag at the exact post-close code. -/
theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot_zeroOpenTag
    (source : ActiveForkState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : ActiveForkQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package fork.middle
    fork.zeroOpenQuery.1.2 =
      ⟨descriptor.moveIdentity,
        profiledOpenIndexedDirectionSummarize A descriptor.code
          descriptor.moveIdentity
          (profiledOpenPhysicalStrictHistoryDirection [] fork.middleRightPivot
            fork.middleLeftPivot bothInputOne bothInputTwo)⟩ := by
  let fork :=
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
          lastStrict bothInputOne bothInputTwo
  exact profiledOpenProvenancePolicyZeroOpenQueryOfState_tag A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package fork.middle
      oldSide.other fork.middleRightPivot fork.middleLeftPivot bothInputOne
        bothInputTwo

end

end DetParityAutomaton

end DistributedSynthesis
