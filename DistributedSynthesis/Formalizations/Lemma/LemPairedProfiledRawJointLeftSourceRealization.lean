/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLambdaFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenChildViewEquality

/-!
# Literal left-to-right source realization for the raw joint family

This is the exact process-two/left mirror of the basis-free right source
realization.  Every live left member produces the finite right slot of its
literal `PairedStrategyMemory` child.  The pivot-selected children moreover
form one genuine process-one local-view family.

No rational run or leader-observation signal occurs here.  The theorem is a
one-reversal statement; recursively assembling the two orientations still
requires a joint successor exact-fibre witness.
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
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-! ## One live member: finite child equals the literal memory child -/

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- The source code and raw move expose exactly the strategy lambda and the
finite profiled source stored by a live semantic left member. -/
theorem ProfiledRawJointSemanticFamily.leftCandidateChild_eq_some
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (member : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : family.left index = some member) (row : PairedEntryRow) :
    profiledRawLeftCandidateChild A (family.code A) (family.move A)
        direction (index, row) =
      some (profiledRawLeftChildSlot A
        ((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.leftPhysicalPast
          direction.leftInput) := by
  simp [profiledRawLeftCandidateChild,
    ProfiledRawJointSemanticFamily.code,
    ProfiledRawJointSemanticFamily.move, hmember]

/-- The finite slot computed above is definitionally the profiled state of
the literal operational process-one child. -/
theorem profiledRawLeftChildSlot_eq_literalProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) :
    PairedStrategyMemory.toProfiledTreeState (A := A)
        (profiledRawLeftSemanticChildMemory A member row
          direction.leftPhysicalPast direction.leftInput) =
      .inr (.inl (profiledRawLeftChildSlot A
        ((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.leftPhysicalPast
          direction.leftInput)) := by
  rw [show profiledRawLeftSemanticChildMemory A member row
      direction.leftPhysicalPast direction.leftInput =
      (PairedStrategyMemory.processTwo member.1 member.2).step (A := A)
        (.fromTwo row direction.leftPhysicalPast direction.leftInput) by rfl]
  rw [PairedStrategyMemory.toProfiledTreeState_step]
  exact pairedProfiledTwoChild_eq_profiledRawLeftChildSlot A
    (((member.1.code, member.2),
      leftInitialFirstProfile member.1.lambdaOfStrategy))
    member.1.lambdaOfStrategy row direction.leftPhysicalPast
      direction.leftInput

/-- Combined live-member realization: the optional finite computation is
present and its value names the literal strategy-memory child. -/
theorem ProfiledRawJointSemanticFamily.exists_leftLiteralChildSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (member : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : family.left index = some member) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      profiledRawLeftCandidateChild A (family.code A) (family.move A)
          direction (index, row) = some slot ∧
        PairedStrategyMemory.toProfiledTreeState (A := A)
            (profiledRawLeftSemanticChildMemory A member row
              direction.leftPhysicalPast direction.leftInput) =
          .inr (.inl slot) := by
  let slot := profiledRawLeftChildSlot A
    ((member.1.code, member.2),
      leftInitialFirstProfile member.1.lambdaOfStrategy)
    member.1.lambdaOfStrategy row direction.leftPhysicalPast
      direction.leftInput
  exact ⟨slot,
    family.leftCandidateChild_eq_some A direction index member hmember row,
    profiledRawLeftChildSlot_eq_literalProfiledState A direction member row⟩

end

/-! ## The semantic process-one child named by a finite slot -/

/-- Literal process-one entry/minimum pair produced by one active left
member. -/
def profiledRawLeftSemanticChildPair
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) : ProcOnePairedEntryRep strategy × A.State :=
  let entry : Unit → ProcTwoPairedEntryRep strategy := fun _ => member.1
  (procOneViewClassChild strategy entry past input ((), row),
    procOneViewClassChildMinimum A entry past ((), row))

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The pair above is exactly the constructor exposed by the literal memory
step. -/
theorem profiledRawLeftSemanticChildMemory_eq_processOne
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    profiledRawLeftSemanticChildMemory A member row past input =
      .processOne (profiledRawLeftSemanticChildPair A member row past input).1
        (profiledRawLeftSemanticChildPair A member row past input).2 := by
  classical
  let entry : Unit → ProcTwoPairedEntryRep strategy := fun _ => member.1
  let minimum : Unit → A.State := fun _ => member.2
  simpa [profiledRawLeftSemanticChildMemory,
    profiledRawLeftSemanticChildPair, entry, minimum] using
    (pairedStrategyMemory_step_eq_procOneViewClassChild A entry minimum
      () past input row)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The finite right slot is the exact finite erasure of the literal
semantic process-one pair. -/
theorem profiledRawLeftChildSlot_eq_semanticChildPairCode
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) :
    let child := profiledRawLeftSemanticChildPair A member row
      direction.leftPhysicalPast direction.leftInput
    profiledRawLeftChildSlot A
        ((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.leftPhysicalPast
          direction.leftInput =
      ((child.1.code, child.2),
        rightInitialFirstProfile child.1.lambdaOfStrategy) := by
  dsimp only
  have hliteral := profiledRawLeftChildSlot_eq_literalProfiledState A
    direction member row
  have hmemory := profiledRawLeftSemanticChildMemory_eq_processOne A member
    row direction.leftPhysicalPast direction.leftInput
  rw [hmemory] at hliteral
  change
    Sum.inr (Sum.inl
      (((profiledRawLeftSemanticChildPair A member row
            direction.leftPhysicalPast direction.leftInput).1.code,
          (profiledRawLeftSemanticChildPair A member row
            direction.leftPhysicalPast direction.leftInput).2),
        rightInitialFirstProfile
          (profiledRawLeftSemanticChildPair A member row
            direction.leftPhysicalPast direction.leftInput).1.lambdaOfStrategy)) =
      Sum.inr (Sum.inl (profiledRawLeftChildSlot A
        ((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.leftPhysicalPast
          direction.leftInput)) at hliteral
  exact (Sum.inl.inj (Sum.inr.inj hliteral)).symm

/-! ## The pivot-selected semantic child family -/

/-- Finite erasure of a literal process-one semantic child. -/
def profiledRawRightSlotOfSemanticPair
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (child : ProcOnePairedEntryRep strategy × A.State) :
    ProfiledRawRightSlot A :=
  ((child.1.code, child.2),
    rightInitialFirstProfile child.1.lambdaOfStrategy)

/-- The semantic process-one child selected for one lineage by the left
pivot. -/
def ProfiledRawJointSemanticFamily.leftSelectedChild
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) : Option (ProcOnePairedEntryRep strategy × A.State) :=
  match family.left index with
  | none => none
  | some member =>
      if family.leftPattern A (index, .first) direction.leftPivot = true then
        some (profiledRawLeftSemanticChildPair A member .first
          direction.leftPhysicalPast direction.leftInput)
      else if family.leftPattern A (index, .both) direction.leftPivot = true then
        some (profiledRawLeftSemanticChildPair A member .both
          direction.leftPhysicalPast direction.leftInput)
      else none

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype I] [Inhabited In₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- A live candidate in the pivot equality class is represented by the
materialized semantic child. -/
theorem ProfiledRawJointSemanticFamily.leftSelectedChild_eq_some_of_pattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (member : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : family.left index = some member) (row : PairedEntryRow)
    (hpattern :
      family.leftPattern A (index, row) direction.leftPivot = true) :
    family.leftSelectedChild A direction index =
      some (profiledRawLeftSemanticChildPair A member row
        direction.leftPhysicalPast direction.leftInput) := by
  cases row with
  | first =>
      simp [ProfiledRawJointSemanticFamily.leftSelectedChild, hmember,
        hpattern]
  | both =>
      have hfirst :
          family.leftPattern A (index, .first) direction.leftPivot ≠ true := by
        intro hfirst
        exact family.leftPattern_rowFunctionalAt A direction.leftPivot index
          ⟨hfirst, hpattern⟩
      simp [ProfiledRawJointSemanticFamily.leftSelectedChild, hmember,
        hfirst, hpattern]

omit [Fintype I] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Every selected child exposes its source member and selected row. -/
theorem ProfiledRawJointSemanticFamily.leftSelectedChild_eq_some_source
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (child : ProcOnePairedEntryRep strategy × A.State)
    (hchild : family.leftSelectedChild A direction index = some child) :
    ∃ member row,
      family.left index = some member ∧
        family.leftPattern A (index, row) direction.leftPivot = true ∧
        child = profiledRawLeftSemanticChildPair A member row
          direction.leftPhysicalPast direction.leftInput := by
  cases hmember : family.left index with
  | none =>
      simp [ProfiledRawJointSemanticFamily.leftSelectedChild, hmember] at hchild
  | some member =>
      by_cases hfirst :
          family.leftPattern A (index, .first) direction.leftPivot = true
      · refine ⟨member, .first, by simpa using hmember, hfirst, ?_⟩
        simpa [ProfiledRawJointSemanticFamily.leftSelectedChild, hmember,
          hfirst] using hchild.symm
      · by_cases hboth :
            family.leftPattern A (index, .both) direction.leftPivot = true
        · refine ⟨member, .both, by simpa using hmember, hboth, ?_⟩
          simpa [ProfiledRawJointSemanticFamily.leftSelectedChild, hmember,
            hfirst, hboth] using hchild.symm
        · simp [ProfiledRawJointSemanticFamily.leftSelectedChild, hmember,
            hfirst, hboth] at hchild

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Pointwise semantic/finite agreement for the pivot-selected left child
family. -/
theorem ProfiledRawJointSemanticFamily.leftSelectedChild_finiteSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) :
    (family.leftSelectedChild A direction index).map
        (profiledRawRightSlotOfSemanticPair A) =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).right index := by
  cases hmember : family.left index with
  | none =>
      simp [ProfiledRawJointSemanticFamily.leftSelectedChild,
        profiledRawJointFamilyNext, profiledRawLeftIndexedChildCode,
        profiledRawJointChildCodeOfPattern, profiledRawLeftCandidateChild,
        profiledRawOptionalChildSlots, ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.move,
        ProfiledRawJointSemanticFamily.leftPattern, hmember]
  | some member =>
      by_cases hfirst :
          family.leftPattern A (index, .first) direction.leftPivot = true
      · simp [ProfiledRawJointSemanticFamily.leftSelectedChild,
          profiledRawJointFamilyNext, profiledRawLeftIndexedChildCode,
          profiledRawJointChildCodeOfPattern, profiledRawLeftCandidateChild,
          profiledRawOptionalChildSlots, ProfiledRawJointSemanticFamily.code,
          ProfiledRawJointSemanticFamily.move, hmember, hfirst,
          profiledRawRightSlotOfSemanticPair,
          profiledRawLeftChildSlot_eq_semanticChildPairCode A direction
            member .first]
      · by_cases hboth :
            family.leftPattern A (index, .both) direction.leftPivot = true
        · simp [ProfiledRawJointSemanticFamily.leftSelectedChild,
            profiledRawJointFamilyNext, profiledRawLeftIndexedChildCode,
            profiledRawJointChildCodeOfPattern, profiledRawLeftCandidateChild,
            profiledRawOptionalChildSlots,
            ProfiledRawJointSemanticFamily.code,
            ProfiledRawJointSemanticFamily.move, hmember, hfirst, hboth,
            profiledRawRightSlotOfSemanticPair,
            profiledRawLeftChildSlot_eq_semanticChildPairCode A direction
              member .both]
        · simp [ProfiledRawJointSemanticFamily.leftSelectedChild,
            profiledRawJointFamilyNext, profiledRawLeftIndexedChildCode,
            profiledRawJointChildCodeOfPattern, profiledRawLeftCandidateChild,
            profiledRawOptionalChildSlots,
            ProfiledRawJointSemanticFamily.code,
            ProfiledRawJointSemanticFamily.move, hmember, hfirst, hboth]

/-! ## Shared process-one view of selected children -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [Inhabited In₂] in
/-- Two pattern-selected left members yield process-one children with the
same process-one view. -/
theorem ProfiledRawJointSemanticFamily.leftPattern_children_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftMember rightMember : ProcTwoPairedEntryRep strategy × A.State)
    (hleftMember : family.left leftIndex = some leftMember)
    (hrightMember : family.left rightIndex = some rightMember)
    (leftRow rightRow : PairedEntryRow)
    (hleftPattern :
      family.leftPattern A (leftIndex, leftRow) direction.leftPivot = true)
    (hrightPattern :
      family.leftPattern A (rightIndex, rightRow) direction.leftPivot = true) :
    currentView Proc.one
        (profiledRawLeftSemanticChildPair A leftMember leftRow
          direction.leftPhysicalPast direction.leftInput).1.leftHistory =
      currentView Proc.one
        (profiledRawLeftSemanticChildPair A rightMember rightRow
          direction.leftPhysicalPast direction.leftInput).1.leftHistory := by
  classical
  cases hpivot : family.left direction.leftPivot.1 with
  | none =>
      simp [ProfiledRawJointSemanticFamily.leftPattern, hleftMember,
        hpivot] at hleftPattern
  | some pivotMember =>
      have hleftOld :
          currentView Proc.one
              (profiledRawProcTwoRowHistory leftMember.1 leftRow) =
            currentView Proc.one
              (profiledRawProcTwoRowHistory pivotMember.1
                direction.leftPivot.2) := by
        simpa [ProfiledRawJointSemanticFamily.leftPattern, hleftMember,
          hpivot] using hleftPattern
      have hrightOld :
          currentView Proc.one
              (profiledRawProcTwoRowHistory rightMember.1 rightRow) =
            currentView Proc.one
              (profiledRawProcTwoRowHistory pivotMember.1
                direction.leftPivot.2) := by
        simpa [ProfiledRawJointSemanticFamily.leftPattern, hrightMember,
          hpivot] using hrightPattern
      let entry : Bool → ProcTwoPairedEntryRep strategy := fun side =>
        if side then rightMember.1 else leftMember.1
      have hblind : ∀ left right,
          currentView Proc.two (entry left).rightHistory =
            currentView Proc.two (entry right).rightHistory := by
        intro left right
        cases left <;> cases right
        · rfl
        · simpa [entry] using family.left_view_shared leftIndex rightIndex
            leftMember rightMember hleftMember hrightMember
        · simpa [entry] using (family.left_view_shared leftIndex rightIndex
            leftMember rightMember hleftMember hrightMember).symm
        · rfl
      have hrow :
          currentView Proc.one
              (procTwoViewClassRowHistory entry (false, leftRow)) =
            currentView Proc.one
              (procTwoViewClassRowHistory entry (true, rightRow)) := by
        simpa [entry, procTwoViewClassRowHistory,
          profiledRawProcTwoRowHistory] using hleftOld.trans hrightOld.symm
      have hchild :=
        (procOneViewClassChild_view_eq_iff strategy entry hblind
          direction.leftPhysicalPast direction.leftInput
          (false, leftRow) (true, rightRow)).2 hrow
      simpa [profiledRawLeftSemanticChildPair, entry] using hchild

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [Inhabited In₂] in
/-- The materialized left-selected children form one genuine process-one
local-view family. -/
theorem ProfiledRawJointSemanticFamily.leftSelectedChild_view_shared
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ∀ leftIndex rightIndex leftChild rightChild,
      family.leftSelectedChild A direction leftIndex = some leftChild →
      family.leftSelectedChild A direction rightIndex = some rightChild →
      currentView Proc.one leftChild.1.leftHistory =
        currentView Proc.one rightChild.1.leftHistory := by
  intro leftIndex rightIndex leftChild rightChild hleft hright
  rcases family.leftSelectedChild_eq_some_source A direction leftIndex
      leftChild hleft with
    ⟨leftMember, leftRow, hleftMember, hleftPattern, rfl⟩
  rcases family.leftSelectedChild_eq_some_source A direction rightIndex
      rightChild hright with
    ⟨rightMember, rightRow, hrightMember, hrightPattern, rfl⟩
  exact family.leftPattern_children_view_eq A direction leftIndex rightIndex
    leftMember rightMember hleftMember hrightMember leftRow rightRow
      hleftPattern hrightPattern

/-! ## Exact-fibre wrapper -/

/-- Complete left half of one raw source realization. -/
structure ProfiledRawJointLeftSourceRealization
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) : Prop where
  exactFibre : family.ExactFibreAt A direction
  childViewShared : ∀ leftIndex rightIndex leftChild rightChild,
    family.leftSelectedChild A direction leftIndex = some leftChild →
    family.leftSelectedChild A direction rightIndex = some rightChild →
    currentView Proc.one leftChild.1.leftHistory =
      currentView Proc.one rightChild.1.leftHistory
  finiteSlots : ∀ index,
    (family.leftSelectedChild A direction index).map
        (profiledRawRightSlotOfSemanticPair A) =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).right index

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The left half passes the one-reversal source-realization test
unconditionally once the joint source is an exact fibre. -/
theorem ProfiledRawJointSemanticFamily.leftSourceRealization
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hexact : family.ExactFibreAt A direction) :
    ProfiledRawJointLeftSourceRealization A family direction where
  exactFibre := hexact
  childViewShared := family.leftSelectedChild_view_shared A direction
  finiteSlots := family.leftSelectedChild_finiteSlot A direction

end

end DetParityAutomaton

end DistributedSynthesis
