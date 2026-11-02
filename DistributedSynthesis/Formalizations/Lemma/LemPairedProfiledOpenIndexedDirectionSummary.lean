/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSuccessorAPI

/-!
# Finite direction summaries for the indexed source-free node

The raw hidden direction stores two arbitrarily long tagged prefixes.  At a
fixed finite code and move, each prefix is consumed only by one classified
transition-rational family table.  Its effect is therefore completely
captured by two finite controls: the rational table control after the sender
word, and the finite family monitor control after the full decoded word.

This file packages those controls together with the finite pivots and current
inputs.  It then computes the indexed child code directly from the package
and proves that this finite computation agrees with the original raw-list
successor.  No strict-leader, orientation, or history bit becomes visible to
either process; this is a proof-side quotient of Nature's direction.
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

noncomputable local instance : DecidableEq (ProfiledOpenRightRoot A) :=
  Classical.decEq _

noncomputable local instance : DecidableEq (ProfiledOpenLeftRoot A) :=
  Classical.decEq _

/-! ## Finite induced-table controls -/

/-- The complete finite effect of a right classified shared-node prefix.
The first component controls the transition-rational table label at the
sender word; the second is the narrowed family-monitor control at the full
decoded word. -/
abbrev ProfiledOpenRightClassifiedInducedControl
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source) :=
  table.toTransitionRationalTree.Control ×
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1)).State

/-- Left classified induced-table control. -/
abbrev ProfiledOpenLeftClassifiedInducedControl
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source) :=
  table.toTransitionRationalTree.Control ×
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1)).State

/-- Read the finite right induced control at one full decoded node. -/
noncomputable def profiledOpenRightClassifiedInducedControlAt
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁))) :
    ProfiledOpenRightClassifiedInducedControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenRightClassifiedRootMonitor A member.1
  let family := table.toTransitionRationalTree
  (family.controlAt (senderWord node),
    narrowedControl (finiteRootFamilyMonitor monitors) family.labeledTree node)

/-- Read the finite left induced control. -/
noncomputable def profiledOpenLeftClassifiedInducedControlAt
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂))) :
    ProfiledOpenLeftClassifiedInducedControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenLeftClassifiedRootMonitor A member.1
  let family := table.toTransitionRationalTree
  (family.controlAt (senderWord node),
    narrowedControl (finiteRootFamilyMonitor monitors) family.labeledTree node)

/-- Query a right classified table from its finite induced control. -/
noncomputable def profiledOpenRightClassifiedOutputAtInducedControl
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (control : ProfiledOpenRightClassifiedInducedControl A source table)
    (member : {root // root ∈ source.1}) (input : In₂ × In₁) :
    ProfiledOpenRightClassifiedOutput A :=
  (table.toTransitionRationalTree.labelOf control.1).2 control.2
    ((member, input.1), input.2)

/-- Query a left table from its finite induced control. -/
noncomputable def profiledOpenLeftClassifiedOutputAtInducedControl
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (control : ProfiledOpenLeftClassifiedInducedControl A source table)
    (member : {root // root ∈ source.1}) (input : In₁ × In₂) :
    ProfiledOpenLeftClassifiedOutput A :=
  (table.toTransitionRationalTree.labelOf control.1).2 control.2
    ((member, input.1), input.2)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The raw right shared-node output depends on its whole node only through
the finite induced control. -/
theorem profiledOpenRightClassifiedSharedNodeOutput_eq_inducedControl
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (member : {root // root ∈ source.1}) (input : In₂ × In₁) :
    profiledOpenRightClassifiedSharedNodeOutput A source table node member
        input =
      profiledOpenRightClassifiedOutputAtInducedControl A source table
        (profiledOpenRightClassifiedInducedControlAt A source table node)
        member input := by
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left shared-node factorization mirror. -/
theorem profiledOpenLeftClassifiedSharedNodeOutput_eq_inducedControl
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (member : {root // root ∈ source.1}) (input : In₁ × In₂) :
    profiledOpenLeftClassifiedSharedNodeOutput A source table node member
        input =
      profiledOpenLeftClassifiedOutputAtInducedControl A source table
        (profiledOpenLeftClassifiedInducedControlAt A source table node)
        member input := by
  rfl

/-! ## A finite quotient of the raw indexed direction -/

/-- Only a genuine right classified move needs a right induced-table
control.  Ill-oriented and sink move components carry no prefix information. -/
def ProfiledOpenIndexedRightDirectionControl
    (move : ProfiledOpenClassifiedMove A) : Type :=
  match move with
  | .right source table =>
      Fin (Fintype.card
        (ProfiledOpenRightClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table))
  | _ => PUnit

/-- Left move-component control family. -/
def ProfiledOpenIndexedLeftDirectionControl
    (move : ProfiledOpenClassifiedMove A) : Type :=
  match move with
  | .left source table =>
      Fin (Fintype.card
        (ProfiledOpenLeftClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table))
  | _ => PUnit

noncomputable instance profiledOpenIndexedRightDirectionControl_fintype
    (move : ProfiledOpenClassifiedMove A) :
    Fintype (ProfiledOpenIndexedRightDirectionControl A move) := by
  classical
  cases move <;>
    simp only [ProfiledOpenIndexedRightDirectionControl] <;>
    infer_instance

noncomputable instance profiledOpenIndexedLeftDirectionControl_fintype
    (move : ProfiledOpenClassifiedMove A) :
    Fintype (ProfiledOpenIndexedLeftDirectionControl A move) := by
  classical
  cases move <;>
    simp only [ProfiledOpenIndexedLeftDirectionControl] <;>
    infer_instance

/-- Collapse one raw right tagged prefix to the finite induced-table control
selected by the current public move. -/
noncomputable def profiledOpenIndexedRightDirectionControlOfPast
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenClassifiedMove A)
    (past : List ((I × In₂) × In₁)) :
    ProfiledOpenIndexedRightDirectionControl A move :=
  match move with
  | .right source table =>
      Fintype.equivFin
        (ProfiledOpenRightClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table)
        (profiledOpenRightClassifiedInducedControlAt A source table
          (profiledOpenIndexedRightSharedNode A code source past))
  | .sink => PUnit.unit
  | .left _ _ => PUnit.unit

/-- Left tagged-prefix collapse. -/
noncomputable def profiledOpenIndexedLeftDirectionControlOfPast
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenClassifiedMove A)
    (past : List ((I × In₁) × In₂)) :
    ProfiledOpenIndexedLeftDirectionControl A move :=
  match move with
  | .left source table =>
      Fintype.equivFin
        (ProfiledOpenLeftClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table)
        (profiledOpenLeftClassifiedInducedControlAt A source table
          (profiledOpenIndexedLeftSharedNode A code source past))
  | .sink => PUnit.unit
  | .right _ _ => PUnit.unit

/-- Finite environment-direction quotient at one fixed public move.  The
arbitrarily long lists have been replaced by the two finite induced-table
controls. -/
structure ProfiledOpenIndexedDirectionSummary
    (move : ProfiledOpenIndexedBiBeliefMove A) where
  rightPivot : IndexedLineageCandidate I
  rightControl : ProfiledOpenIndexedRightDirectionControl A move.1
  rightInput : In₂ × In₁
  leftPivot : IndexedLineageCandidate I
  leftControl : ProfiledOpenIndexedLeftDirectionControl A move.2
  leftInput : In₁ × In₂

noncomputable instance profiledOpenIndexedDirectionSummary_fintype
    (move : ProfiledOpenIndexedBiBeliefMove A) :
    Fintype (ProfiledOpenIndexedDirectionSummary A (I := I) move) := by
  classical
  let encode := fun summary :
      ProfiledOpenIndexedDirectionSummary A (I := I) move =>
    (summary.rightPivot, summary.rightControl, summary.rightInput,
      summary.leftPivot, summary.leftControl, summary.leftInput)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftRP, leftRC, leftRI, leftLP, leftLC, leftLI⟩
    rcases right with ⟨rightRP, rightRC, rightRI, rightLP, rightLC, rightLI⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl)

/-- Summarize a raw hidden direction at the current finite code and move. -/
noncomputable def profiledOpenIndexedDirectionSummarize
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenIndexedDirectionSummary A (I := I) move :=
  { rightPivot := direction.rightPivot
    rightControl := profiledOpenIndexedRightDirectionControlOfPast A code
      move.1 direction.rightTaggedPast
    rightInput := direction.rightInput
    leftPivot := direction.leftPivot
    leftControl := profiledOpenIndexedLeftDirectionControlOfPast A code
      move.2 direction.leftTaggedPast
    leftInput := direction.leftInput }

/-! ## Direct successor computation on summaries -/

/-- Right child-anchor evaluator whose dependent finite control is eliminated
by structural recursion on the public move component. -/
noncomputable def profiledOpenIndexedRightChildAnchorAtDirectionControl
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenIndexedRightDirectionControl A move →
        (In₂ × In₁) → IndexedLineageCandidate I →
          ProfiledOpenClassifiedAnchor A
  | .sink, _, _, _ => .sink
  | .left _ _, _, _, _ => .sink
  | .right source table, packed, input, candidate =>
      match code.rightSlots candidate.1 with
      | some (.right root) =>
          if hmem : root ∈ source.1 then
            let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let control :=
              (Fintype.equivFin
                (ProfiledOpenRightClassifiedInducedControl.{u, v, x, y, s,
                  0, 0} A source table)).symm packed
            let output := profiledOpenRightClassifiedOutputAtInducedControl A
              source table control member input
            .left ((output.2 candidate.2).1)
          else .sink
      | _ => .sink

/-- Left child-anchor evaluator on its packed finite control. -/
noncomputable def profiledOpenIndexedLeftChildAnchorAtDirectionControl
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenIndexedLeftDirectionControl A move →
        (In₁ × In₂) → IndexedLineageCandidate I →
          ProfiledOpenClassifiedAnchor A
  | .sink, _, _, _ => .sink
  | .right _ _, _, _, _ => .sink
  | .left source table, packed, input, candidate =>
      match code.leftSlots candidate.1 with
      | some (.left root) =>
          if hmem : root ∈ source.1 then
            let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let control :=
              (Fintype.equivFin
                (ProfiledOpenLeftClassifiedInducedControl.{u, v, x, y, s,
                  0, 0} A source table)).symm packed
            let output := profiledOpenLeftClassifiedOutputAtInducedControl A
              source table control member input
            .right ((output.2 candidate.2).1)
          else .sink
      | _ => .sink

/-- Right-to-left child anchor read only from the finite direction summary. -/
noncomputable def profiledOpenIndexedRightChildAnchorSummary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (summary : ProfiledOpenIndexedDirectionSummary A (I := I) move)
    (candidate : IndexedLineageCandidate I) :
    ProfiledOpenClassifiedAnchor A :=
  profiledOpenIndexedRightChildAnchorAtDirectionControl A code move.1
    summary.rightControl summary.rightInput candidate

/-- Left-to-right child anchor from the finite summary. -/
noncomputable def profiledOpenIndexedLeftChildAnchorSummary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (summary : ProfiledOpenIndexedDirectionSummary A (I := I) move)
    (candidate : IndexedLineageCandidate I) :
    ProfiledOpenClassifiedAnchor A :=
  profiledOpenIndexedLeftChildAnchorAtDirectionControl A code move.2
    summary.leftControl summary.leftInput candidate

/-- Raw right child code computed without a history list. -/
noncomputable def profiledOpenIndexedRightRawChildCodeSummary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (summary : ProfiledOpenIndexedDirectionSummary A (I := I) move) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  profiledOpenIndexedGatedChildCode A code.rightSlots code.rightPattern
    (profiledOpenIndexedRightChildAnchorSummary A code move summary)
    summary.rightPivot

/-- Raw left child code from the finite summary. -/
noncomputable def profiledOpenIndexedLeftRawChildCodeSummary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (summary : ProfiledOpenIndexedDirectionSummary A (I := I) move) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  profiledOpenIndexedGatedChildCode A code.leftSlots code.leftPattern
    (profiledOpenIndexedLeftChildAnchorSummary A code move summary)
    summary.leftPivot

/-- Normalized right child code from the finite summary. -/
noncomputable def profiledOpenIndexedRightChildCodeSummary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (summary : ProfiledOpenIndexedDirectionSummary A (I := I) move) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  (profiledOpenIndexedRightRawChildCodeSummary A code move summary)
    |>.deduplicateRoots

/-- Normalized left child code from the finite summary. -/
noncomputable def profiledOpenIndexedLeftChildCodeSummary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (summary : ProfiledOpenIndexedDirectionSummary A (I := I) move) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  (profiledOpenIndexedLeftRawChildCodeSummary A code move summary)
    |>.deduplicateRoots

/-- The complete finite-code successor on a finite direction summary. -/
noncomputable def profiledOpenIndexedBiBeliefNextSummary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (summary : ProfiledOpenIndexedDirectionSummary A (I := I) move) :
    ProfiledOpenIndexedBiBeliefCode A (I := I) :=
  let rightSlots :=
    (profiledOpenIndexedLeftChildCodeSummary A code move summary).rootSlots
  let leftSlots :=
    (profiledOpenIndexedRightChildCodeSummary A code move summary).rootSlots
  { rightSlots := rightSlots
    leftSlots := leftSlots
    rightPattern := profiledOpenIndexedActiveCanonicalRowPattern A rightSlots
    leftPattern := profiledOpenIndexedActiveCanonicalRowPattern A leftSlots }

/-! ## Exact factorization theorem -/

section
omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedRightChildAnchorSummary_summarize
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (candidate : IndexedLineageCandidate I) :
    profiledOpenIndexedRightChildAnchorSummary A code move
        (profiledOpenIndexedDirectionSummarize A code move direction)
        candidate =
      profiledOpenIndexedRightChildAnchor A code move direction candidate := by
  classical
  rcases move with ⟨rightMove, leftMove⟩
  cases rightMove with
  | sink =>
      simp [profiledOpenIndexedRightChildAnchorSummary,
        profiledOpenIndexedRightChildAnchorAtDirectionControl,
        profiledOpenIndexedRightChildAnchor]
  | left source table =>
      simp [profiledOpenIndexedRightChildAnchorSummary,
        profiledOpenIndexedRightChildAnchorAtDirectionControl,
        profiledOpenIndexedRightChildAnchor]
  | right source table =>
      cases hslot : code.rightSlots candidate.1 with
      | none =>
          simp [profiledOpenIndexedRightChildAnchorSummary,
            profiledOpenIndexedRightChildAnchorAtDirectionControl,
            profiledOpenIndexedRightChildAnchor, hslot]
      | some anchor =>
          cases anchor <;>
            simp [profiledOpenIndexedRightChildAnchorSummary,
              profiledOpenIndexedRightChildAnchorAtDirectionControl,
              profiledOpenIndexedRightChildAnchor,
              profiledOpenIndexedDirectionSummarize,
              profiledOpenIndexedRightDirectionControlOfPast,
              ProfiledOpenIndexedRightDirectionControl,
              profiledOpenRightClassifiedSharedNodeOutput_eq_inducedControl,
              hslot]

@[simp] theorem profiledOpenIndexedLeftChildAnchorSummary_summarize
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (candidate : IndexedLineageCandidate I) :
    profiledOpenIndexedLeftChildAnchorSummary A code move
        (profiledOpenIndexedDirectionSummarize A code move direction)
        candidate =
      profiledOpenIndexedLeftChildAnchor A code move direction candidate := by
  classical
  rcases move with ⟨rightMove, leftMove⟩
  cases leftMove with
  | sink =>
      simp [profiledOpenIndexedLeftChildAnchorSummary,
        profiledOpenIndexedLeftChildAnchorAtDirectionControl,
        profiledOpenIndexedLeftChildAnchor]
  | right source table =>
      simp [profiledOpenIndexedLeftChildAnchorSummary,
        profiledOpenIndexedLeftChildAnchorAtDirectionControl,
        profiledOpenIndexedLeftChildAnchor]
  | left source table =>
      cases hslot : code.leftSlots candidate.1 with
      | none =>
          simp [profiledOpenIndexedLeftChildAnchorSummary,
            profiledOpenIndexedLeftChildAnchorAtDirectionControl,
            profiledOpenIndexedLeftChildAnchor, hslot]
      | some anchor =>
          cases anchor <;>
            simp [profiledOpenIndexedLeftChildAnchorSummary,
              profiledOpenIndexedLeftChildAnchorAtDirectionControl,
              profiledOpenIndexedLeftChildAnchor,
              profiledOpenIndexedDirectionSummarize,
              profiledOpenIndexedLeftDirectionControlOfPast,
              ProfiledOpenIndexedLeftDirectionControl,
              profiledOpenLeftClassifiedSharedNodeOutput_eq_inducedControl,
              hslot]

theorem profiledOpenIndexedRightRawChildCodeSummary_summarize
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedRightRawChildCodeSummary A code move
        (profiledOpenIndexedDirectionSummarize A code move direction) =
      profiledOpenIndexedRightRawChildCode A code move direction := by
  unfold profiledOpenIndexedRightRawChildCodeSummary
    profiledOpenIndexedRightRawChildCode
  congr 1
  funext candidate
  exact profiledOpenIndexedRightChildAnchorSummary_summarize A code move
    direction candidate

theorem profiledOpenIndexedLeftRawChildCodeSummary_summarize
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedLeftRawChildCodeSummary A code move
        (profiledOpenIndexedDirectionSummarize A code move direction) =
      profiledOpenIndexedLeftRawChildCode A code move direction := by
  unfold profiledOpenIndexedLeftRawChildCodeSummary
    profiledOpenIndexedLeftRawChildCode
  congr 1
  funext candidate
  exact profiledOpenIndexedLeftChildAnchorSummary_summarize A code move
    direction candidate

/-- The original unbounded-direction successor factors exactly through the
finite summary. -/
theorem profiledOpenIndexedBiBeliefNextSummary_summarize
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedBiBeliefNextSummary A code move
        (profiledOpenIndexedDirectionSummarize A code move direction) =
      profiledOpenIndexedBiBeliefNext A code move direction := by
  have hright :
      profiledOpenIndexedRightChildCodeSummary A code move
          (profiledOpenIndexedDirectionSummarize A code move direction) =
        profiledOpenIndexedRightChildCode A code move direction := by
    exact congrArg IndexedLineageChildCode.deduplicateRoots
      (profiledOpenIndexedRightRawChildCodeSummary_summarize A code move
        direction)
  have hleft :
      profiledOpenIndexedLeftChildCodeSummary A code move
          (profiledOpenIndexedDirectionSummarize A code move direction) =
        profiledOpenIndexedLeftChildCode A code move direction := by
    exact congrArg IndexedLineageChildCode.deduplicateRoots
      (profiledOpenIndexedLeftRawChildCodeSummary_summarize A code move
        direction)
  unfold profiledOpenIndexedBiBeliefNextSummary
    profiledOpenIndexedBiBeliefNext
  rw [hright, hleft]

/-- Equal finite direction summaries force equal public successors.  This is
the quotient/congruence form consumed by finite-controller constructions. -/
theorem profiledOpenIndexedBiBeliefNext_eq_of_summarize_eq
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (left right : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsummary :
      profiledOpenIndexedDirectionSummarize A code move left =
        profiledOpenIndexedDirectionSummarize A code move right) :
    profiledOpenIndexedBiBeliefNext A code move left =
      profiledOpenIndexedBiBeliefNext A code move right := by
  calc
    profiledOpenIndexedBiBeliefNext A code move left =
        profiledOpenIndexedBiBeliefNextSummary A code move
          (profiledOpenIndexedDirectionSummarize A code move left) :=
      (profiledOpenIndexedBiBeliefNextSummary_summarize A code move left).symm
    _ = profiledOpenIndexedBiBeliefNextSummary A code move
          (profiledOpenIndexedDirectionSummarize A code move right) := by
      rw [hsummary]
    _ = profiledOpenIndexedBiBeliefNext A code move right :=
      profiledOpenIndexedBiBeliefNextSummary_summarize A code move right

/-- Equal summaries give equal normalized right-to-left child root slots. -/
theorem profiledOpenIndexedRightChildCode_rootSlots_eq_of_summarize_eq
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (left right : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsummary :
      profiledOpenIndexedDirectionSummarize A code move left =
        profiledOpenIndexedDirectionSummarize A code move right) :
    (profiledOpenIndexedRightChildCode A code move left).rootSlots =
      (profiledOpenIndexedRightChildCode A code move right).rootSlots := by
  have hnext := profiledOpenIndexedBiBeliefNext_eq_of_summarize_eq A code move
    left right hsummary
  exact congrArg ProfiledOpenIndexedBiBeliefCode.leftSlots hnext

/-- Equal summaries give equal normalized left-to-right child root slots. -/
theorem profiledOpenIndexedLeftChildCode_rootSlots_eq_of_summarize_eq
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (left right : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hsummary :
      profiledOpenIndexedDirectionSummarize A code move left =
        profiledOpenIndexedDirectionSummarize A code move right) :
    (profiledOpenIndexedLeftChildCode A code move left).rootSlots =
      (profiledOpenIndexedLeftChildCode A code move right).rootSlots := by
  have hnext := profiledOpenIndexedBiBeliefNext_eq_of_summarize_eq A code move
    left right hsummary
  exact congrArg ProfiledOpenIndexedBiBeliefCode.rightSlots hnext

end

end


end DetParityAutomaton

end DistributedSynthesis
