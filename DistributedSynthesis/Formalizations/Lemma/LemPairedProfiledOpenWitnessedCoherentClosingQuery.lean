/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOperationalReachableQuery
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedStreamingOverlayFrontier

/-!
# Coherent closing queries from an executable overlay

The finite direction tag and the bank of executable rational-tree queries are
independent coordinates of `ProfiledOpenWitnessedTableQuery`.  Merely retaining
both coordinates therefore does not say that the query selected at a boundary
is the query reached by the physical overlay that produced that boundary.

This file records the smallest data-level *partial* repair.  A proof-side closing choice
retains a finite overlay together with its lineage.  After executing a physical
input list, the sidewise query bank is rebuilt with the *literal final overlay
query* in the selected value coordinate and canonical empty-word queries in all
other coordinates.  The selected pivot uses the same lineage and the sticky row
stored by that overlay.  No side, lineage, or row is exposed to a local process.

This is deliberately only a finite-state/query-bank alignment result.  It does
**not** identify the finite direction control with the final overlay control.
Those controls belong to two independently rationalized tables: the old
classified table used by the child code and the pinned descriptor-union table
used by the overlay.  Semantic re-anchoring says that each table is a raw
semantic response table at *some* past, but does not identify the two pasts.
Root pinning identifies only the first record.  Consequently the theorems below
do not yet imply that the child anchor is the overlay's closing classified root.

Installing the selected overlay's outputs in a distributed emission also has
to satisfy the existing local-event congruence laws.
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

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

private abbrev ClosingQuery :=
  ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
    max i u v x y s, max i u v x y s} A initialCode

/-! ## The finite state extension -/

/-- One raw proof-side closing choice.  The classified root and sticky row are
already fields of the selected overlay; only the lineage has to be retained in
addition.  This carrier does not assert that the lineage covers the retained
root; an exact-slot installer must establish that fact at the use site. -/
abbrev ProfiledOpenWitnessedStreamingSelectedOverlay :=
  (I × ProfiledOpenWitnessedRightRoundOverlay A initialCode) ⊕
    (I × ProfiledOpenWitnessedLeftRoundOverlay A initialCode)

noncomputable instance
    profiledOpenWitnessedStreamingSelectedOverlay_fintype :
    Fintype (ProfiledOpenWitnessedStreamingSelectedOverlay A initialCode) := by
  classical
  infer_instance

/-- Minimal extension of the orientation-free overlay frontier.  Selection is
optional so the state is total also before a boundary has installed a choice.
The recurrence invariant that a selected overlay belongs to its corresponding
frontier is separate from the finite carrier itself. -/
structure ProfiledOpenWitnessedStreamingCoherentOverlayState where
  frontier : ProfiledOpenWitnessedStreamingOverlayFrontier A initialCode
  selected : Option
    (ProfiledOpenWitnessedStreamingSelectedOverlay A initialCode)

noncomputable instance
    profiledOpenWitnessedStreamingCoherentOverlayState_fintype :
    Fintype
      (ProfiledOpenWitnessedStreamingCoherentOverlayState A initialCode) := by
  classical
  let encode := fun state :
      ProfiledOpenWitnessedStreamingCoherentOverlayState A initialCode ↦
    (state.frontier, state.selected)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

/-! ## Right closing query -/

/-- Rebuild the complete reachable table query after one executable right
overlay run.  The right pivot is the lineage selected with this very overlay
and the row stored in the overlay; the unused left pivot remains an explicit
proof-side argument.  The accumulator supplies an old-classified-table control;
no equality with the overlay's independently rationalized control is claimed. -/
noncomputable def profiledOpenWitnessedRightCoherentClosingQuery
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) : ClosingQuery A initialCode :=
  let finalOverlay :=
    profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs
  let rightPivot : IndexedLineageCandidate I :=
    (lineage, finalOverlay.entryRow)
  profiledOpenFixedSidewiseRightQueryOfSelected A initialCode
    finalOverlay.value finalOverlay.query finalOverlay.reachable
    (candidate.finish A rightPivot leftPivot inputOne inputTwo)

/-- The selected bank coordinate is definitionally the query reached by the
same executable overlay run.  This closes the query-bank half of the product
coordinate only; it does not identify the old classified direction control. -/
@[simp] theorem
    profiledOpenWitnessedRightCoherentClosingQuery_selected
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let finalOverlay :=
      profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs
    (profiledOpenWitnessedRightCoherentClosingQuery A initialCode overlay
        inputs candidate lineage leftPivot inputOne inputTwo).1.1.2.1
          finalOverlay.value =
      finalOverlay.query := by
  dsimp only [profiledOpenWitnessedRightCoherentClosingQuery]
  exact profiledOpenFixedRightQueryBankWithSelected_selected A initialCode _ _

/-- The finite direction tag uses the same overlay's sticky row. -/
@[simp] theorem
    profiledOpenWitnessedRightCoherentClosingQuery_rightPivot
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (leftPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let finalOverlay :=
      profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs
    (profiledOpenWitnessedRightCoherentClosingQuery A initialCode overlay
        inputs candidate lineage leftPivot inputOne inputTwo).1.2.2.rightPivot =
      (lineage, finalOverlay.entryRow) := by
  rfl

/-! ## Left closing query -/

/-- Left mirror of the coherent closing query. -/
noncomputable def profiledOpenWitnessedLeftCoherentClosingQuery
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (rightPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) : ClosingQuery A initialCode :=
  let finalOverlay :=
    profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs
  let leftPivot : IndexedLineageCandidate I :=
    (lineage, finalOverlay.entryRow)
  profiledOpenFixedSidewiseLeftQueryOfSelected A initialCode
    finalOverlay.value finalOverlay.query finalOverlay.reachable
    (candidate.finish A rightPivot leftPivot inputOne inputTwo)

/-- Left selected-coordinate alignment. -/
@[simp] theorem
    profiledOpenWitnessedLeftCoherentClosingQuery_selected
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (rightPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let finalOverlay :=
      profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs
    (profiledOpenWitnessedLeftCoherentClosingQuery A initialCode overlay inputs
        candidate lineage rightPivot inputOne inputTwo).1.1.2.2
          finalOverlay.value =
      finalOverlay.query := by
  dsimp only [profiledOpenWitnessedLeftCoherentClosingQuery]
  exact profiledOpenFixedLeftQueryBankWithSelected_selected A initialCode _ _

/-- The left tag pivot carries the selected overlay's sticky row. -/
@[simp] theorem
    profiledOpenWitnessedLeftCoherentClosingQuery_leftPivot
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂))
    (candidate : ProfiledOpenPhysicalDirectionAccumulatorCandidate A)
    (lineage : I) (rightPivot : IndexedLineageCandidate I)
    (inputOne : In₁) (inputTwo : In₂) :
    let finalOverlay :=
      profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs
    (profiledOpenWitnessedLeftCoherentClosingQuery A initialCode overlay inputs
        candidate lineage rightPivot inputOne inputTwo).1.2.2.leftPivot =
      (lineage, finalOverlay.entryRow) := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
