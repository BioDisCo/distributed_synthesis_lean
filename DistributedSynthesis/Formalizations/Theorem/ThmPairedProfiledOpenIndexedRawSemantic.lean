/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCommonProvenance
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefNode
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSharedNodeMapping
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSuccessorAPI
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenInjectiveSemanticRealization
import DistributedSynthesis.Formalizations.Lemma.LemIndexedLineageSurvivorFamily

/-!
# Raw semantic lanes for the indexed belief node

An active semantic lane stores one realization of one exact-view source and a
partial, surjective map from persistent lineage indices to its finite roots.
The map may repeat a root, but every root of the public family has a lineage.
Inactive lanes are explicit.  This is proof-side state only: the public code
contains just optional finite anchors and a Boolean equality pattern, while
the public move contains just the classified finite table.

This file first proves that every such semantic pair produces a valid
source-free indexed node.  Its second layer constructs the one-step
correlated semantic handoff from the shared-node provenance theorem.  No
orientation, lineage, or strict-leader bit is delivered to a process.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Active semantic lanes -/

/-- One active right-oriented semantic family.  `memberAt` is proof-side and
surjects onto the finite source roots. -/
structure ProfiledOpenIndexedRightSemanticLane where
  source : ProfiledOpenRightViewClass A
  realization : ProfiledOpenRightRealization A strategy hwin basis source
  memberAt : I → Option {root // root ∈ source.1}
  covers : ∀ member : {root // root ∈ source.1},
    ∃ lineage : I, memberAt lineage = some member

/-- Left-oriented semantic lane. -/
structure ProfiledOpenIndexedLeftSemanticLane where
  source : ProfiledOpenLeftViewClass A
  realization : ProfiledOpenLeftRealization A strategy hwin basis source
  memberAt : I → Option {root // root ∈ source.1}
  covers : ∀ member : {root // root ∈ source.1},
    ∃ lineage : I, memberAt lineage = some member

/-- A lane may be semantically inactive. -/
abbrev ProfiledOpenIndexedRightSemanticShadow :=
  Option (ProfiledOpenIndexedRightSemanticLane A strategy hwin basis (I := I))

/-- Left inactive/active shadow. -/
abbrev ProfiledOpenIndexedLeftSemanticShadow :=
  Option (ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis (I := I))

/-- Optional public right anchors represented by a semantic shadow. -/
def ProfiledOpenIndexedRightSemanticShadow.slots :
    ProfiledOpenIndexedRightSemanticShadow A strategy hwin basis (I := I) →
      I → Option (ProfiledOpenClassifiedAnchor A)
  | none => fun _ => none
  | some lane => fun lineage =>
      (lane.memberAt lineage).map fun member => .right member.1

/-- Optional left anchors. -/
def ProfiledOpenIndexedLeftSemanticShadow.slots :
    ProfiledOpenIndexedLeftSemanticShadow A strategy hwin basis (I := I) →
      I → Option (ProfiledOpenClassifiedAnchor A)
  | none => fun _ => none
  | some lane => fun lineage =>
      (lane.memberAt lineage).map fun member => .left member.1

/-- Exact old-opposite-view equality on active right lineages, false outside
the active carrier. -/
noncomputable def ProfiledOpenIndexedRightSemanticShadow.pattern :
    ProfiledOpenIndexedRightSemanticShadow A strategy hwin basis (I := I) →
      IndexedLineageEqualityPattern I
  | none => fun _ _ => false
  | some lane => fun left right =>
      match lane.memberAt left.1, lane.memberAt right.1 with
      | some leftMember, some rightMember =>
          procOneEntryOppositeViewPattern strategy lane.realization.entry
            (leftMember, left.2) (rightMember, right.2)
      | _, _ => false

/-- Left equality-pattern mirror. -/
noncomputable def ProfiledOpenIndexedLeftSemanticShadow.pattern :
    ProfiledOpenIndexedLeftSemanticShadow A strategy hwin basis (I := I) →
      IndexedLineageEqualityPattern I
  | none => fun _ _ => false
  | some lane => fun left right =>
      match lane.memberAt left.1, lane.memberAt right.1 with
      | some leftMember, some rightMember =>
          procTwoEntryOppositeViewPattern strategy lane.realization.entry
            (leftMember, left.2) (rightMember, right.2)
      | _, _ => false

/-- Finite public right move of a semantic shadow. -/
noncomputable def ProfiledOpenIndexedRightSemanticShadow.move :
    ProfiledOpenIndexedRightSemanticShadow A strategy hwin basis (I := I) →
      ProfiledOpenClassifiedMove A
  | none => .sink
  | some lane =>
      .right lane.source
        ((lane.realization.coherentTable A).table.toClassified A lane.source)

/-- Finite public left move. -/
noncomputable def ProfiledOpenIndexedLeftSemanticShadow.move :
    ProfiledOpenIndexedLeftSemanticShadow A strategy hwin basis (I := I) →
      ProfiledOpenClassifiedMove A
  | none => .sink
  | some lane =>
      .left lane.source
        ((lane.realization.coherentTable A).table.toClassified A lane.source)

/-! ## The semantic public node -/

/-- Both correlated shadows of one raw semantic node. -/
structure ProfiledOpenIndexedCorrelatedSemanticState where
  right : ProfiledOpenIndexedRightSemanticShadow A strategy hwin basis
    (I := I)
  left : ProfiledOpenIndexedLeftSemanticShadow A strategy hwin basis
    (I := I)

/-- Forget exact histories and expose only the finite indexed code. -/
noncomputable def ProfiledOpenIndexedCorrelatedSemanticState.code
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedBiBeliefCode A (I := I) :=
  { rightSlots := state.right.slots A strategy hwin basis
    leftSlots := state.left.slots A strategy hwin basis
    rightPattern := state.right.pattern A strategy hwin basis
    leftPattern := state.left.pattern A strategy hwin basis }

/-- The public move contains both finite tables but no selected orientation. -/
noncomputable def ProfiledOpenIndexedCorrelatedSemanticState.move
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedBiBeliefMove A :=
  (state.right.move A strategy hwin basis,
    state.left.move A strategy hwin basis)

/-! ## Structural validity -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Membership in an optional-slot root set is exactly occurrence in one
slot. -/
theorem mem_profiledOpenIndexedSlotRoots_iff
    (slots : I → Option (ProfiledOpenClassifiedAnchor A))
    (root : ProfiledOpenClassifiedAnchor A) :
    root ∈ profiledOpenIndexedSlotRoots A slots ↔
      ∃ lineage : I, slots lineage = some root := by
  classical
  constructor
  · intro hroot
    simp only [profiledOpenIndexedSlotRoots, Finset.mem_biUnion] at hroot
    rcases hroot with ⟨lineage, _, hmember⟩
    cases hslot : slots lineage with
    | none => simp [hslot] at hmember
    | some slotRoot =>
        have heq : root = slotRoot := by simpa [hslot] using hmember
        subst slotRoot
        exact ⟨lineage, hslot⟩
  · rintro ⟨lineage, hlineage⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨lineage, Finset.mem_univ lineage, ?_⟩
    simp [hlineage]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- An active right semantic lane has exactly its source roots. -/
theorem ProfiledOpenIndexedRightSemanticLane.slotRoots_eq
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I)) :
    profiledOpenIndexedSlotRoots A
        (ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin basis
          (some lane)) =
      profiledOpenRightClassifiedRoots A lane.source := by
  classical
  ext anchor
  constructor
  · intro hanchor
    rw [mem_profiledOpenIndexedSlotRoots_iff] at hanchor
    rcases hanchor with ⟨lineage, hlineage⟩
    cases hmember : lane.memberAt lineage with
    | none => simp [ProfiledOpenIndexedRightSemanticShadow.slots, hmember] at hlineage
    | some member =>
        have : anchor = .right member.1 := by
          simpa [ProfiledOpenIndexedRightSemanticShadow.slots, hmember] using
            hlineage.symm
        subst anchor
        simp [profiledOpenRightClassifiedRoots, member.2]
  · intro hanchor
    rw [mem_profiledOpenIndexedSlotRoots_iff]
    rcases Finset.mem_image.mp hanchor with ⟨root, hroot, rfl⟩
    let member : {root // root ∈ lane.source.1} := ⟨root, hroot⟩
    rcases lane.covers member with ⟨lineage, hlineage⟩
    refine ⟨lineage, ?_⟩
    simp [ProfiledOpenIndexedRightSemanticShadow.slots, member, hlineage]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left slot-root equality. -/
theorem ProfiledOpenIndexedLeftSemanticLane.slotRoots_eq
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I)) :
    profiledOpenIndexedSlotRoots A
        (ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin basis
          (some lane)) =
      profiledOpenLeftClassifiedRoots A lane.source := by
  classical
  ext anchor
  constructor
  · intro hanchor
    rw [mem_profiledOpenIndexedSlotRoots_iff] at hanchor
    rcases hanchor with ⟨lineage, hlineage⟩
    cases hmember : lane.memberAt lineage with
    | none => simp [ProfiledOpenIndexedLeftSemanticShadow.slots, hmember] at hlineage
    | some member =>
        have : anchor = .left member.1 := by
          simpa [ProfiledOpenIndexedLeftSemanticShadow.slots, hmember] using
            hlineage.symm
        subst anchor
        simp [profiledOpenLeftClassifiedRoots, member.2]
  · intro hanchor
    rw [mem_profiledOpenIndexedSlotRoots_iff]
    rcases Finset.mem_image.mp hanchor with ⟨root, hroot, rfl⟩
    let member : {root // root ∈ lane.source.1} := ⟨root, hroot⟩
    rcases lane.covers member with ⟨lineage, hlineage⟩
    refine ⟨lineage, ?_⟩
    simp [ProfiledOpenIndexedLeftSemanticShadow.slots, member, hlineage]

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The semantic right pattern is row-functional at every pivot. -/
theorem ProfiledOpenIndexedRightSemanticShadow.pattern_rowFunctionalAt
    (shadow : ProfiledOpenIndexedRightSemanticShadow A strategy hwin basis
      (I := I)) (pivot : IndexedLineageCandidate I) :
    (shadow.pattern A strategy hwin basis).RowFunctionalAt pivot := by
  classical
  cases shadow with
  | none => simp [ProfiledOpenIndexedRightSemanticShadow.pattern,
      IndexedLineageEqualityPattern.RowFunctionalAt]
  | some lane =>
      intro lineage hboth
      cases hpivot : lane.memberAt pivot.1 with
      | none =>
          simp [ProfiledOpenIndexedRightSemanticShadow.pattern, hpivot] at hboth
      | some pivotMember =>
          cases hmember : lane.memberAt lineage with
          | none =>
              simp [ProfiledOpenIndexedRightSemanticShadow.pattern, hpivot,
                hmember] at hboth
          | some member =>
              have hfirst :
                  currentView Proc.two
                      (procOneViewClassRowHistory lane.realization.entry
                        (member, .first)) =
                    currentView Proc.two
                      (procOneViewClassRowHistory lane.realization.entry
                        (pivotMember, pivot.2)) := by
                simpa [ProfiledOpenIndexedRightSemanticShadow.pattern,
                  hpivot, hmember, procOneEntryOppositeViewPattern] using hboth.1
              have hsecond :
                  currentView Proc.two
                      (procOneViewClassRowHistory lane.realization.entry
                        (member, .both)) =
                    currentView Proc.two
                      (procOneViewClassRowHistory lane.realization.entry
                        (pivotMember, pivot.2)) := by
                simpa [ProfiledOpenIndexedRightSemanticShadow.pattern,
                  hpivot, hmember, procOneEntryOppositeViewPattern] using hboth.2
              exact (lane.realization.entry member).other_view_ne
                (by simpa [procOneViewClassRowHistory] using
                  hfirst.trans hsecond.symm)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left pattern row-functionality. -/
theorem ProfiledOpenIndexedLeftSemanticShadow.pattern_rowFunctionalAt
    (shadow : ProfiledOpenIndexedLeftSemanticShadow A strategy hwin basis
      (I := I)) (pivot : IndexedLineageCandidate I) :
    (shadow.pattern A strategy hwin basis).RowFunctionalAt pivot := by
  classical
  cases shadow with
  | none => simp [ProfiledOpenIndexedLeftSemanticShadow.pattern,
      IndexedLineageEqualityPattern.RowFunctionalAt]
  | some lane =>
      intro lineage hboth
      cases hpivot : lane.memberAt pivot.1 with
      | none =>
          simp [ProfiledOpenIndexedLeftSemanticShadow.pattern, hpivot] at hboth
      | some pivotMember =>
          cases hmember : lane.memberAt lineage with
          | none =>
              simp [ProfiledOpenIndexedLeftSemanticShadow.pattern, hpivot,
                hmember] at hboth
          | some member =>
              have hfirst :
                  currentView Proc.one
                      (procTwoViewClassRowHistory lane.realization.entry
                        (member, .first)) =
                    currentView Proc.one
                      (procTwoViewClassRowHistory lane.realization.entry
                        (pivotMember, pivot.2)) := by
                simpa [ProfiledOpenIndexedLeftSemanticShadow.pattern,
                  hpivot, hmember, procTwoEntryOppositeViewPattern] using hboth.1
              have hsecond :
                  currentView Proc.one
                      (procTwoViewClassRowHistory lane.realization.entry
                        (member, .both)) =
                    currentView Proc.one
                      (procTwoViewClassRowHistory lane.realization.entry
                        (pivotMember, pivot.2)) := by
                simpa [ProfiledOpenIndexedLeftSemanticShadow.pattern,
                  hpivot, hmember, procTwoEntryOppositeViewPattern] using hboth.2
              exact (lane.realization.entry member).other_view_ne
                (by simpa [procTwoViewClassRowHistory] using
                  hfirst.trans hsecond.symm)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every raw semantic state exposes a valid finite source-free node. -/
theorem ProfiledOpenIndexedCorrelatedSemanticState.valid
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedBiBeliefValid A
      (state.code A strategy hwin basis) (state.move A strategy hwin basis) := by
  rcases state with ⟨right, left⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases right with
    | none =>
        simp [ProfiledOpenIndexedCorrelatedSemanticState.code,
          ProfiledOpenIndexedCorrelatedSemanticState.move,
          ProfiledOpenIndexedRightSemanticShadow.slots,
          ProfiledOpenIndexedRightSemanticShadow.move,
          ProfiledOpenIndexedRightLaneValid, profiledOpenIndexedSlotRoots_empty]
    | some lane =>
        change ProfiledOpenIndexedRightLaneValid A
          (ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin basis
            (some lane))
          (ProfiledOpenIndexedRightSemanticShadow.move A strategy hwin basis
            (some lane))
        rw [show ProfiledOpenIndexedRightSemanticShadow.move A strategy hwin
          basis (some lane) =
          ProfiledOpenClassifiedMove.right lane.source
            ((lane.realization.coherentTable A).table.toClassified A
              lane.source) by rfl]
        change profiledOpenIndexedSlotRoots A
            (ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin
              basis (some lane)) ≠ ∅ ∧ _
        rw [lane.slotRoots_eq A strategy hwin basis]
        exact ⟨(Finset.image_nonempty.mpr lane.source.2.1).ne_empty, rfl⟩
  · cases left with
    | none =>
        simp [ProfiledOpenIndexedCorrelatedSemanticState.code,
          ProfiledOpenIndexedCorrelatedSemanticState.move,
          ProfiledOpenIndexedLeftSemanticShadow.slots,
          ProfiledOpenIndexedLeftSemanticShadow.move,
          ProfiledOpenIndexedLeftLaneValid, profiledOpenIndexedSlotRoots_empty]
    | some lane =>
        change ProfiledOpenIndexedLeftLaneValid A
          (ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin basis
            (some lane))
          (ProfiledOpenIndexedLeftSemanticShadow.move A strategy hwin basis
            (some lane))
        rw [show ProfiledOpenIndexedLeftSemanticShadow.move A strategy hwin
          basis (some lane) =
          ProfiledOpenClassifiedMove.left lane.source
            ((lane.realization.coherentTable A).table.toClassified A
              lane.source) by rfl]
        change profiledOpenIndexedSlotRoots A
            (ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin
              basis (some lane)) ≠ ∅ ∧ _
        rw [lane.slotRoots_eq A strategy hwin basis]
        exact ⟨(Finset.image_nonempty.mpr lane.source.2.1).ne_empty, rfl⟩
  · exact fun pivot =>
      ProfiledOpenIndexedRightSemanticShadow.pattern_rowFunctionalAt
        A strategy hwin basis right pivot
  · exact fun pivot =>
      ProfiledOpenIndexedLeftSemanticShadow.pattern_rowFunctionalAt
        A strategy hwin basis left pivot

/-! ## Literal normalized survivors -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- A normalized right-to-left survivor comes from one genuinely active
source member and row.  Its stored finite root is exactly the raw shared-node
anchor at that candidate.  This is the first half of the no-splicing bridge:
deduplication never fabricates a semantic candidate. -/
theorem ProfiledOpenIndexedCorrelatedSemanticState.rightSurvivor_literal
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : state.right = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedRightRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ∃ member : {root // root ∈ lane.source.1},
      lane.memberAt survivor.lineage = some member ∧
      (state.code A strategy hwin basis).rightPattern
          (survivor.lineage, survivor.row) direction.rightPivot = true ∧
      survivor.root =
        profiledOpenIndexedRightChildAnchor A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction
          (survivor.lineage, survivor.row) := by
  classical
  let code := state.code A strategy hwin basis
  let move := state.move A strategy hwin basis
  let raw := profiledOpenIndexedRightRawChildCode A code move direction
  have hraw : raw survivor.lineage =
      some (survivor.row, survivor.root) :=
    raw.eq_of_deduplicateRoots_eq_some survivor.lineage survivor.row
      survivor.root survivor.slot
  have hpivot : code.rightSlots direction.rightPivot.1 ≠ none := by
    intro hnone
    have hempty := profiledOpenIndexedGatedChildCode_none_of_pivot_none A
      code.rightSlots code.rightPattern
      (profiledOpenIndexedRightChildAnchor A code move direction)
      direction.rightPivot hnone survivor.lineage
    cases hempty.symm.trans hraw
  have hmemberActive : code.rightSlots survivor.lineage ≠ none := by
    intro hnone
    have hempty := profiledOpenIndexedGatedChildCode_none_of_member_none A
      code.rightSlots code.rightPattern
      (profiledOpenIndexedRightChildAnchor A code move direction)
      direction.rightPivot survivor.lineage hnone
    cases hempty.symm.trans hraw
  have hmaterialized :
      indexedLineageChildCodeOfPattern code.rightPattern
          (profiledOpenIndexedRightChildAnchor A code move direction)
          direction.rightPivot survivor.lineage =
        some (survivor.row, survivor.root) := by
    rw [← profiledOpenIndexedGatedChildCode_eq_of_active A
      code.rightSlots code.rightPattern
      (profiledOpenIndexedRightChildAnchor A code move direction)
      direction.rightPivot survivor.lineage hpivot hmemberActive]
    exact hraw
  have hinverted := indexedLineageChildCodeOfPattern_eq_some_elim
    code.rightPattern
    (profiledOpenIndexedRightChildAnchor A code move direction)
    direction.rightPivot survivor.lineage survivor.row survivor.root
    hmaterialized
  have hlaneActive : lane.memberAt survivor.lineage ≠ none := by
    intro hnone
    apply hmemberActive
    have hslots : code.rightSlots survivor.lineage =
        (lane.memberAt survivor.lineage).map
          (fun member => ProfiledOpenClassifiedAnchor.right member.1) := by
      simp [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hright,
        ProfiledOpenIndexedRightSemanticShadow.slots]
    rw [hslots, hnone]
    rfl
  obtain ⟨member, hslot⟩ := Option.ne_none_iff_exists'.mp hlaneActive
  exact ⟨member, hslot, hinverted⟩

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right normalized-survivor mirror. -/
theorem ProfiledOpenIndexedCorrelatedSemanticState.leftSurvivor_literal
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hleft : state.left = some lane)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (survivor :
      (profiledOpenIndexedLeftRawChildCode A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) direction).RootSurvivor) :
    ∃ member : {root // root ∈ lane.source.1},
      lane.memberAt survivor.lineage = some member ∧
      (state.code A strategy hwin basis).leftPattern
          (survivor.lineage, survivor.row) direction.leftPivot = true ∧
      survivor.root =
        profiledOpenIndexedLeftChildAnchor A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) direction
          (survivor.lineage, survivor.row) := by
  classical
  let code := state.code A strategy hwin basis
  let move := state.move A strategy hwin basis
  let raw := profiledOpenIndexedLeftRawChildCode A code move direction
  have hraw : raw survivor.lineage =
      some (survivor.row, survivor.root) :=
    raw.eq_of_deduplicateRoots_eq_some survivor.lineage survivor.row
      survivor.root survivor.slot
  have hpivot : code.leftSlots direction.leftPivot.1 ≠ none := by
    intro hnone
    have hempty := profiledOpenIndexedGatedChildCode_none_of_pivot_none A
      code.leftSlots code.leftPattern
      (profiledOpenIndexedLeftChildAnchor A code move direction)
      direction.leftPivot hnone survivor.lineage
    cases hempty.symm.trans hraw
  have hmemberActive : code.leftSlots survivor.lineage ≠ none := by
    intro hnone
    have hempty := profiledOpenIndexedGatedChildCode_none_of_member_none A
      code.leftSlots code.leftPattern
      (profiledOpenIndexedLeftChildAnchor A code move direction)
      direction.leftPivot survivor.lineage hnone
    cases hempty.symm.trans hraw
  have hmaterialized :
      indexedLineageChildCodeOfPattern code.leftPattern
          (profiledOpenIndexedLeftChildAnchor A code move direction)
          direction.leftPivot survivor.lineage =
        some (survivor.row, survivor.root) := by
    rw [← profiledOpenIndexedGatedChildCode_eq_of_active A
      code.leftSlots code.leftPattern
      (profiledOpenIndexedLeftChildAnchor A code move direction)
      direction.leftPivot survivor.lineage hpivot hmemberActive]
    exact hraw
  have hinverted := indexedLineageChildCodeOfPattern_eq_some_elim
    code.leftPattern
    (profiledOpenIndexedLeftChildAnchor A code move direction)
    direction.leftPivot survivor.lineage survivor.row survivor.root
    hmaterialized
  have hlaneActive : lane.memberAt survivor.lineage ≠ none := by
    intro hnone
    apply hmemberActive
    have hslots : code.leftSlots survivor.lineage =
        (lane.memberAt survivor.lineage).map
          (fun member => ProfiledOpenClassifiedAnchor.left member.1) := by
      simp [code, ProfiledOpenIndexedCorrelatedSemanticState.code, hleft,
        ProfiledOpenIndexedLeftSemanticShadow.slots]
    rw [hslots, hnone]
    rfl
  obtain ⟨member, hslot⟩ := Option.ne_none_iff_exists'.mp hlaneActive
  exact ⟨member, hslot, hinverted⟩

end


end DetParityAutomaton

end DistributedSynthesis
