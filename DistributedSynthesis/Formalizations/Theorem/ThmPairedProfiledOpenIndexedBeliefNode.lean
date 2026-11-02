/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedLineage
import DistributedSynthesis.Formalizations.Lemma.LemIndexedLineageRootDeduplication
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSharedNodeOutput
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefNodeRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenBiBeliefNode

/-!
# Pattern-checked indexed source-free belief nodes

This is the finite public-node consumer of the indexed-lineage construction.
The code stores two ordered root-slot families and the finite equality pattern
of each shadow.  A public move is the already finite pair of classified
family tables.  The hidden environment direction names proof-side pivots and
block data, but no pivot, orientation, or leader bit is exposed to a process.

The total successor does not trust a direction-supplied successor grouping.
It computes both groupings with `indexedLineageChildCodeOfPattern`, cross-swaps
their root slots, and resets the two equality patterns to the canonical
row-diagonal pattern proved for genuine handoffs.  This is the concrete
source-free `next` needed by `LemSourceFreeBeliefNodeRationalization`.

The final section names, but does not assume or prove, the two genuinely
semantic residuals: correlated successor closure (`next_code`) and global
hidden-thread acceptance.  Keeping them separate prevents the local T1 proof
from being mistaken for the unconditional raw-winner construction.
-/

namespace DistributedSynthesis

universe i u v x y s w z a

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Finite code and hidden direction -/

/-- Both ordered shadow families and their complete cross-row equality
patterns.  Slots contain only finite objective anchors. -/
structure ProfiledOpenIndexedBiBeliefCode where
  rightSlots : I → Option (ProfiledOpenClassifiedAnchor A)
  leftSlots : I → Option (ProfiledOpenClassifiedAnchor A)
  rightPattern : IndexedLineageEqualityPattern I
  leftPattern : IndexedLineageEqualityPattern I

noncomputable instance : Fintype (ProfiledOpenIndexedBiBeliefCode A (I := I)) := by
  classical
  let Anchor := ProfiledOpenClassifiedAnchor A
  let Rep :=
    (I → Option Anchor) × (I → Option Anchor) ×
      IndexedLineageEqualityPattern I × IndexedLineageEqualityPattern I
  let e : ProfiledOpenIndexedBiBeliefCode A (I := I) ≃ Rep :=
    { toFun := fun code =>
        (code.rightSlots, code.leftSlots, code.rightPattern, code.leftPattern)
      invFun := fun code =>
        { rightSlots := code.1
          leftSlots := code.2.1
          rightPattern := code.2.2.1
          leftPattern := code.2.2.2 }
      left_inv := by intro code; cases code; rfl
      right_inv := by intro code; rcases code with ⟨right, left, rp, lp⟩; rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- The public move is finite.  It contains both tables, never a selected
orientation. -/
abbrev ProfiledOpenIndexedBiBeliefMove := ProfiledOpenBiBeliefMove A

noncomputable instance : Fintype (ProfiledOpenIndexedBiBeliefMove A) := by
  classical
  infer_instance

/-- Proof-side resolution of both shadows.  The persistent lineage and row
are hidden-thread coordinates.  Lists are environment directions, not finite
automaton state. -/
structure ProfiledOpenIndexedBiBeliefDirection where
  rightPivot : IndexedLineageCandidate I
  rightTaggedPast : List ((I × In₂) × In₁)
  rightInput : In₂ × In₁
  leftPivot : IndexedLineageCandidate I
  leftTaggedPast : List ((I × In₁) × In₂)
  leftInput : In₁ × In₂

/-! ## Active-gated finite child-code computation -/

/-- Canonical post-handoff equality on the lineages which are actually
present.  An absent slot has no row-candidate at all, so it is unrelated to
every pivot.  This active gate is essential: the ungated diagonal pattern
would materialize an absent lineage as a sink root at the following step. -/
def profiledOpenIndexedActiveCanonicalRowPattern
    (slots : I → Option (ProfiledOpenClassifiedAnchor A)) :
    IndexedLineageEqualityPattern I :=
  fun left right =>
    match slots left.1, slots right.1 with
    | some _, some _ => decide (left.2 = right.2)
    | _, _ => false

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
/-- The active-gated diagonal remains row-functional at every pivot. -/
theorem profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (pivot : IndexedLineageCandidate I) :
    (profiledOpenIndexedActiveCanonicalRowPattern A slots).RowFunctionalAt
      pivot := by
  intro member hboth
  cases hpivot : slots pivot.1 with
  | none =>
      simp [profiledOpenIndexedActiveCanonicalRowPattern, hpivot] at hboth
  | some pivotRoot =>
      cases hmember : slots member with
      | none =>
          simp [profiledOpenIndexedActiveCanonicalRowPattern, hpivot,
            hmember] at hboth
      | some memberRoot =>
          rcases pivot with ⟨pivotLineage, pivotRow⟩
          cases pivotRow <;>
            simp [profiledOpenIndexedActiveCanonicalRowPattern, hpivot,
              hmember] at hboth

/-- Materialize a pattern class only inside the currently active carrier.
An absent pivot selects the empty class, and an absent member always stays
absent, independently of arbitrary Boolean entries in the stored pattern. -/
def profiledOpenIndexedGatedChildCode
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → ProfiledOpenClassifiedAnchor A)
    (pivot : IndexedLineageCandidate I) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  match slots pivot.1 with
  | none => fun _ => none
  | some _ => fun member =>
      match slots member with
      | none => none
      | some _ => indexedLineageChildCodeOfPattern pattern root pivot member

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledOpenIndexedGatedChildCode_none_of_pivot_none
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → ProfiledOpenClassifiedAnchor A)
    (pivot : IndexedLineageCandidate I)
    (hpivot : slots pivot.1 = none) (member : I) :
    profiledOpenIndexedGatedChildCode A slots pattern root pivot member =
      none := by
  simp [profiledOpenIndexedGatedChildCode, hpivot]

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledOpenIndexedGatedChildCode_none_of_member_none
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (pattern : IndexedLineageEqualityPattern I)
    (root : IndexedLineageCandidate I → ProfiledOpenClassifiedAnchor A)
    (pivot : IndexedLineageCandidate I) (member : I)
    (hmember : slots member = none) :
    profiledOpenIndexedGatedChildCode A slots pattern root pivot member =
      none := by
  cases hpivot : slots pivot.1 with
  | none =>
      simp [profiledOpenIndexedGatedChildCode, hpivot]
  | some pivotRoot =>
      simp [profiledOpenIndexedGatedChildCode, hpivot, hmember]

/-! ## One shared family-controller prefix per lane -/

/-- Interpret an indexed right-lane tag as a member of the currently selected
classified source.  Ill-typed tags use the source's canonical fallback.  On
valid lanes, every active slot takes the membership branch. -/
noncomputable def profiledOpenIndexedRightSourceMember
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A) (lineage : I) :
    {root // root ∈ source.1} := by
  classical
  let fallback : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  exact match code.rightSlots lineage with
    | some (.right root) =>
        if hmem : root ∈ source.1 then ⟨root, hmem⟩ else fallback
    | _ => fallback

/-- Left source-member decoder. -/
noncomputable def profiledOpenIndexedLeftSourceMember
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenLeftViewClass A) (lineage : I) :
    {root // root ∈ source.1} := by
  classical
  let fallback : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  exact match code.leftSlots lineage with
    | some (.left root) =>
        if hmem : root ∈ source.1 then ⟨root, hmem⟩ else fallback
    | _ => fallback

/-- Decode one finite indexed tagged prefix into one full node of the right
family controller.  This node is shared by every current candidate queried
below. -/
noncomputable def profiledOpenIndexedRightSharedNode
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (past : List ((I × In₂) × In₁)) :
    List ((({root // root ∈ source.1} × In₂) × In₁)) :=
  past.map fun old =>
    (((profiledOpenIndexedRightSourceMember A code source old.1.1), old.1.2),
      old.2)

/-- Left shared-node decoder. -/
noncomputable def profiledOpenIndexedLeftSharedNode
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenLeftViewClass A)
    (past : List ((I × In₁) × In₂)) :
    List ((({root // root ∈ source.1} × In₁) × In₂)) :=
  past.map fun old =>
    (((profiledOpenIndexedLeftSourceMember A code source old.1.1), old.1.2),
      old.2)

/-- Anchor emitted by the right classified table for one persistent
candidate by querying the complete response table at one shared family node.
Ill-shaped slots or moves are sent to the even sink. -/
noncomputable def profiledOpenIndexedRightChildAnchor
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (candidate : IndexedLineageCandidate I) :
    ProfiledOpenClassifiedAnchor A := by
  classical
  exact match move.1 with
  | .right source table =>
      match code.rightSlots candidate.1 with
      | some (.right root) =>
          if hmem : root ∈ source.1 then
            let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let node := profiledOpenIndexedRightSharedNode A code source
              direction.rightTaggedPast
            let output := profiledOpenRightClassifiedSharedNodeOutput A source
              table node member direction.rightInput
            .left ((output.2 candidate.2).1)
          else .sink
      | _ => .sink
  | _ => .sink

/-- Left-to-right mirror. -/
noncomputable def profiledOpenIndexedLeftChildAnchor
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (candidate : IndexedLineageCandidate I) :
    ProfiledOpenClassifiedAnchor A := by
  classical
  exact match move.2 with
  | .left source table =>
      match code.leftSlots candidate.1 with
      | some (.left root) =>
          if hmem : root ∈ source.1 then
            let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let node := profiledOpenIndexedLeftSharedNode A code source
              direction.leftTaggedPast
            let output := profiledOpenLeftClassifiedSharedNodeOutput A source
              table node member direction.leftInput
            .right ((output.2 candidate.2).1)
          else .sink
      | _ => .sink
  | _ => .sink

/-- Raw pattern-derived right-to-left child code, gated by both the selected
pivot and every candidate's current right slot.  Equal finite roots may still
occur at distinct lineages in this intermediate code. -/
noncomputable def profiledOpenIndexedRightRawChildCode
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  profiledOpenIndexedGatedChildCode A code.rightSlots code.rightPattern
    (profiledOpenIndexedRightChildAnchor A code move direction)
    direction.rightPivot

/-- Raw left-to-right child code with the symmetric active gate. -/
noncomputable def profiledOpenIndexedLeftRawChildCode
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  profiledOpenIndexedGatedChildCode A code.leftSlots code.leftPattern
    (profiledOpenIndexedLeftChildAnchor A code move direction)
    direction.leftPivot

/-- Root-normalized right-to-left child code.  One canonical lineage is kept
for every occurring finite root; duplicate histories become inactive instead
of being silently identified by a single source-root representative. -/
noncomputable def profiledOpenIndexedRightChildCode
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  (profiledOpenIndexedRightRawChildCode A code move direction).deduplicateRoots

/-- Root-normalized left-to-right child code. -/
noncomputable def profiledOpenIndexedLeftChildCode
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  (profiledOpenIndexedLeftRawChildCode A code move direction).deduplicateRoots

/-- The all-inactive finite code.  Its patterns are active-gated, hence
identically false without storing a distinguished fake root. -/
def profiledOpenIndexedBiBeliefSinkCode :
    ProfiledOpenIndexedBiBeliefCode A (I := I) :=
  let emptySlots : I → Option (ProfiledOpenClassifiedAnchor A) := fun _ => none
  { rightSlots := emptySlots
    leftSlots := emptySlots
    rightPattern := profiledOpenIndexedActiveCanonicalRowPattern A emptySlots
    leftPattern := profiledOpenIndexedActiveCanonicalRowPattern A emptySlots }

/-- Public move used when both lanes are inactive.  Mixed nodes use this
same sink component only on their inactive lane. -/
def profiledOpenIndexedBiBeliefSinkMove :
    ProfiledOpenIndexedBiBeliefMove A :=
  (.sink, .sink)

/-- Total source-free successor.  Opposite-orientation child slots are
cross-swapped, and each new pattern is the row diagonal restricted to those
new slots.  Missing pivots independently empty their outgoing lane. -/
noncomputable def profiledOpenIndexedBiBeliefNext
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedBiBeliefCode A (I := I) :=
  let rightSlots :=
    (profiledOpenIndexedLeftChildCode A code move direction).rootSlots
  let leftSlots :=
    (profiledOpenIndexedRightChildCode A code move direction).rootSlots
  { rightSlots := rightSlots
    leftSlots := leftSlots
    rightPattern := profiledOpenIndexedActiveCanonicalRowPattern A rightSlots
    leftPattern := profiledOpenIndexedActiveCanonicalRowPattern A leftSlots }

section
omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedBiBeliefNext_rightSlots
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenIndexedBiBeliefNext A code move direction).rightSlots =
      (profiledOpenIndexedLeftChildCode A code move direction).rootSlots :=
  rfl

@[simp] theorem profiledOpenIndexedBiBeliefNext_leftSlots
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenIndexedBiBeliefNext A code move direction).leftSlots =
      (profiledOpenIndexedRightChildCode A code move direction).rootSlots :=
  rfl

@[simp] theorem profiledOpenIndexedBiBeliefNext_rightPattern
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenIndexedBiBeliefNext A code move direction).rightPattern =
      profiledOpenIndexedActiveCanonicalRowPattern A
        (profiledOpenIndexedBiBeliefNext A code move direction).rightSlots :=
  rfl

@[simp] theorem profiledOpenIndexedBiBeliefNext_leftPattern
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenIndexedBiBeliefNext A code move direction).leftPattern =
      profiledOpenIndexedActiveCanonicalRowPattern A
        (profiledOpenIndexedBiBeliefNext A code move direction).leftSlots :=
  rfl

end

section
omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- A missing old left member cannot be resurrected in the next right
shadow. -/
theorem profiledOpenIndexedBiBeliefNext_right_none_of_left_none
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) (lineage : I)
    (hmember : code.leftSlots lineage = none) :
    (profiledOpenIndexedBiBeliefNext A code move direction).rightSlots
        lineage = none := by
  have hchild :
      profiledOpenIndexedLeftChildCode A code move direction lineage = none := by
    apply IndexedLineageChildCode.deduplicateRoots_none_of_none
    simpa only [profiledOpenIndexedLeftRawChildCode] using
      (profiledOpenIndexedGatedChildCode_none_of_member_none A code.leftSlots
        code.leftPattern (profiledOpenIndexedLeftChildAnchor A code move
          direction) direction.leftPivot lineage hmember)
  simp [profiledOpenIndexedBiBeliefNext_rightSlots,
    IndexedLineageChildCode.rootSlots, hchild]

/-- Right-to-left mirror of no resurrection. -/
theorem profiledOpenIndexedBiBeliefNext_left_none_of_right_none
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) (lineage : I)
    (hmember : code.rightSlots lineage = none) :
    (profiledOpenIndexedBiBeliefNext A code move direction).leftSlots
        lineage = none := by
  have hchild :
      profiledOpenIndexedRightChildCode A code move direction lineage = none := by
    apply IndexedLineageChildCode.deduplicateRoots_none_of_none
    simpa only [profiledOpenIndexedRightRawChildCode] using
      (profiledOpenIndexedGatedChildCode_none_of_member_none A code.rightSlots
        code.rightPattern (profiledOpenIndexedRightChildAnchor A code move
          direction) direction.rightPivot lineage hmember)
  simp [profiledOpenIndexedBiBeliefNext_leftSlots,
    IndexedLineageChildCode.rootSlots, hchild]

/-- An absent left pivot empties the whole next right lane. -/
theorem profiledOpenIndexedBiBeliefNext_right_none_of_leftPivot_none
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hpivot : code.leftSlots direction.leftPivot.1 = none)
    (lineage : I) :
    (profiledOpenIndexedBiBeliefNext A code move direction).rightSlots
        lineage = none := by
  have hchild :
      profiledOpenIndexedLeftChildCode A code move direction lineage = none := by
    apply IndexedLineageChildCode.deduplicateRoots_none_of_none
    simpa only [profiledOpenIndexedLeftRawChildCode] using
      (profiledOpenIndexedGatedChildCode_none_of_pivot_none A code.leftSlots
        code.leftPattern (profiledOpenIndexedLeftChildAnchor A code move
          direction) direction.leftPivot hpivot lineage)
  simp [profiledOpenIndexedBiBeliefNext_rightSlots,
    IndexedLineageChildCode.rootSlots, hchild]

/-- An absent right pivot empties the whole next left lane. -/
theorem profiledOpenIndexedBiBeliefNext_left_none_of_rightPivot_none
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hpivot : code.rightSlots direction.rightPivot.1 = none)
    (lineage : I) :
    (profiledOpenIndexedBiBeliefNext A code move direction).leftSlots
        lineage = none := by
  have hchild :
      profiledOpenIndexedRightChildCode A code move direction lineage = none := by
    apply IndexedLineageChildCode.deduplicateRoots_none_of_none
    simpa only [profiledOpenIndexedRightRawChildCode] using
      (profiledOpenIndexedGatedChildCode_none_of_pivot_none A code.rightSlots
        code.rightPattern (profiledOpenIndexedRightChildAnchor A code move
          direction) direction.rightPivot hpivot lineage)
  simp [profiledOpenIndexedBiBeliefNext_leftSlots,
    IndexedLineageChildCode.rootSlots, hchild]

/-- The all-inactive code is absorbing under every public move and hidden
direction. -/
@[simp] theorem profiledOpenIndexedBiBeliefNext_sinkCode
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedBiBeliefNext A
      (profiledOpenIndexedBiBeliefSinkCode A (I := I)) move direction =
        profiledOpenIndexedBiBeliefSinkCode A (I := I) := by
  rfl

end

/-! ## Source-free validity and local T1 -/

/-- Finite set obtained by forgetting the order and absent slots. -/
noncomputable def profiledOpenIndexedSlotRoots
    (slots : I → Option (ProfiledOpenClassifiedAnchor A)) :
    Finset (ProfiledOpenClassifiedAnchor A) := by
  classical
  exact Finset.univ.biUnion fun member =>
    match slots member with
    | none => ∅
    | some root => {root}

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledOpenIndexedSlotRoots_empty :
    profiledOpenIndexedSlotRoots A
        (fun _ : I => (none : Option (ProfiledOpenClassifiedAnchor A))) =
      ∅ := by
  classical
  ext root
  simp [profiledOpenIndexedSlotRoots]

/-- A right lane is either genuinely inactive, represented by the public
sink move, or nonempty and represented by a correctly sourced right table. -/
def ProfiledOpenIndexedRightLaneValid
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (move : ProfiledOpenClassifiedMove A) : Prop :=
  match move with
  | .sink => profiledOpenIndexedSlotRoots A slots = ∅
  | .right source _ =>
      profiledOpenIndexedSlotRoots A slots ≠ ∅ ∧
        profiledOpenRightClassifiedRoots A source =
          profiledOpenIndexedSlotRoots A slots
  | .left _ _ => False

/-- Left-lane mirror, including a legitimate inactive sink component. -/
def ProfiledOpenIndexedLeftLaneValid
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (move : ProfiledOpenClassifiedMove A) : Prop :=
  match move with
  | .sink => profiledOpenIndexedSlotRoots A slots = ∅
  | .left source _ =>
      profiledOpenIndexedSlotRoots A slots ≠ ∅ ∧
        profiledOpenLeftClassifiedRoots A source =
          profiledOpenIndexedSlotRoots A slots
  | .right _ _ => False

/-- Local member-independence of one right-lane component.  The sink case is
vacuous; its carrier is required to be empty by lane validity. -/
def ProfiledOpenIndexedRightLaneLocalT1 :
    ProfiledOpenClassifiedMove A → Prop
  | .sink => True
  | .right source table =>
      ∀ (state : ProfiledOpenRightClassifiedLocalControl A source table)
          (left right : {root // root ∈ source.1}) (input : In₁),
        profiledOpenRightClassifiedLocalMemberStep A source table state left
            input =
          profiledOpenRightClassifiedLocalMemberStep A source table state
            right input
  | .left _ _ => False

/-- Left-lane local T1 mirror. -/
def ProfiledOpenIndexedLeftLaneLocalT1 :
    ProfiledOpenClassifiedMove A → Prop
  | .sink => True
  | .left source table =>
      ∀ (state : ProfiledOpenLeftClassifiedLocalControl A source table)
          (left right : {root // root ∈ source.1}) (input : In₂),
        profiledOpenLeftClassifiedLocalMemberStep A source table state left
            input =
          profiledOpenLeftClassifiedLocalMemberStep A source table state right
            input
  | .right _ _ => False

/-- Independent lane source matching plus the finite row-functionality check
needed by the pattern materializer.  Mixed active/inactive nodes are valid;
in particular, `(sink, sink)` is valid exactly for two empty lanes. -/
def ProfiledOpenIndexedBiBeliefValid
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  ProfiledOpenIndexedRightLaneValid A code.rightSlots move.1 ∧
    ProfiledOpenIndexedLeftLaneValid A code.leftSlots move.2 ∧
    (∀ pivot, code.rightPattern.RowFunctionalAt pivot) ∧
    (∀ pivot, code.leftPattern.RowFunctionalAt pivot)

/-- Local member-independence for both independently active lanes. -/
def ProfiledOpenIndexedBiBeliefT1
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  ProfiledOpenIndexedBiBeliefValid A code move ∧
    ProfiledOpenIndexedRightLaneLocalT1 A move.1 ∧
    ProfiledOpenIndexedLeftLaneLocalT1 A move.2

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedRightLaneLocalT1_of_valid
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (move : ProfiledOpenClassifiedMove A)
    (hvalid : ProfiledOpenIndexedRightLaneValid A slots move) :
    ProfiledOpenIndexedRightLaneLocalT1 A move := by
  cases move with
  | sink => trivial
  | left source table =>
      simp [ProfiledOpenIndexedRightLaneValid] at hvalid
  | right source table =>
      intro state left right input
      exact profiledOpenRightClassifiedLocalMemberStep_eq A source table state
        left right input

theorem profiledOpenIndexedLeftLaneLocalT1_of_valid
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (move : ProfiledOpenClassifiedMove A)
    (hvalid : ProfiledOpenIndexedLeftLaneValid A slots move) :
    ProfiledOpenIndexedLeftLaneLocalT1 A move := by
  cases move with
  | sink => trivial
  | right source table =>
      simp [ProfiledOpenIndexedLeftLaneValid] at hvalid
  | left source table =>
      intro state left right input
      exact profiledOpenLeftClassifiedLocalMemberStep_eq A source table state
        left right input

theorem profiledOpenIndexedBiBeliefT1_of_valid
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (hvalid : ProfiledOpenIndexedBiBeliefValid A code move) :
    ProfiledOpenIndexedBiBeliefT1 A code move :=
  ⟨hvalid,
    profiledOpenIndexedRightLaneLocalT1_of_valid A code.rightSlots move.1
      hvalid.1,
    profiledOpenIndexedLeftLaneLocalT1_of_valid A code.leftSlots move.2
      hvalid.2.1⟩

/-- The all-empty code and all-sink public move form a legitimate node. -/
theorem profiledOpenIndexedBiBeliefSink_valid :
    ProfiledOpenIndexedBiBeliefValid A
      (profiledOpenIndexedBiBeliefSinkCode A (I := I))
      (profiledOpenIndexedBiBeliefSinkMove A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ProfiledOpenIndexedRightLaneValid,
      profiledOpenIndexedBiBeliefSinkCode,
      profiledOpenIndexedBiBeliefSinkMove]
  · simp [ProfiledOpenIndexedLeftLaneValid,
      profiledOpenIndexedBiBeliefSinkCode,
      profiledOpenIndexedBiBeliefSinkMove]
  · intro pivot
    change
      (profiledOpenIndexedActiveCanonicalRowPattern A
        (fun _ : I =>
          (none : Option (ProfiledOpenClassifiedAnchor A)))).RowFunctionalAt
        pivot
    exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A _ _
  · intro pivot
    change
      (profiledOpenIndexedActiveCanonicalRowPattern A
        (fun _ : I =>
          (none : Option (ProfiledOpenClassifiedAnchor A)))).RowFunctionalAt
        pivot
    exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A _ _

end

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every successor installs row-functional active-gated patterns, including
mixed inactive lanes. -/
theorem profiledOpenIndexedBiBeliefNext_patterns_rowFunctional
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (∀ pivot,
      (profiledOpenIndexedBiBeliefNext A code move direction).rightPattern
        |>.RowFunctionalAt pivot) ∧
    (∀ pivot,
      (profiledOpenIndexedBiBeliefNext A code move direction).leftPattern
        |>.RowFunctionalAt pivot) := by
  constructor <;> intro pivot
  · rw [profiledOpenIndexedBiBeliefNext_rightPattern]
    exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A _ _
  · rw [profiledOpenIndexedBiBeliefNext_leftPattern]
    exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A _ _

/-- Finite priority exposed for the indexed hidden-thread system. -/
def profiledOpenIndexedRootPriority
    (root : ProfiledOpenClassifiedAnchor A) : Nat :=
  profiledOpenClassifiedAnchorPriority A root

/-! ## Precisely named semantic residuals -/

/-- The genuine remaining T1/source-free closure equation.  `raw.Semantic`
may contain exact correlated histories, but the right-hand side is the finite
pattern-derived `next` above. -/
def ProfiledOpenIndexedCorrelatedSuccessorClosure
    (raw : SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedBiBeliefDirection
        (I := I) (In₁ := In₁) (In₂ := In₂))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I))) : Prop :=
  ∀ node direction,
    raw.code (raw.step (raw.stateAt node) direction) =
      profiledOpenIndexedBiBeliefNext A
        (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) direction

/-- The separate global `hthread`: every correlated branch is accepted by
the finite indexed-lineage thread system supplied by the caller. -/
def ProfiledOpenIndexedCorrelatedThreadAcceptance
    (U : FiniteThreadSystem
      (ProfiledOpenIndexedBiBeliefMove A ×
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)))
    (raw : SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedBiBeliefDirection
        (I := I) (In₁ := In₁) (In₂ := In₂))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I))) : Prop :=
  ∀ branch,
    U.universalRunDPA.Accepts (observableThreadWord raw.moveTree branch)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Once the two named semantic facts are proved from a raw winner, the
generic source-free certificate is assembled without further mathematics. -/
theorem sourceFreeBeliefSemanticCertificate_of_indexed
    (U : FiniteThreadSystem
      (ProfiledOpenIndexedBiBeliefMove A ×
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)))
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (raw : SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedBiBeliefDirection
        (I := I) (In₁ := In₁) (In₂ := In₂))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I)))
    (hinitial : raw.code raw.initial = initialCode)
    (hvalid : ∀ node,
      ProfiledOpenIndexedBiBeliefValid A (raw.code (raw.stateAt node))
        (raw.move (raw.stateAt node)))
    (hnext : ProfiledOpenIndexedCorrelatedSuccessorClosure A raw)
    (hthread : ProfiledOpenIndexedCorrelatedThreadAcceptance A U raw) :
    SourceFreeBeliefSemanticCertificate U initialCode
      (ProfiledOpenIndexedBiBeliefValid A)
      (profiledOpenIndexedBiBeliefNext A) raw :=
  { initial_code := hinitial
    valid := hvalid
    next_code := hnext
    accepts := hthread }

end


end DetParityAutomaton

end DistributedSynthesis
