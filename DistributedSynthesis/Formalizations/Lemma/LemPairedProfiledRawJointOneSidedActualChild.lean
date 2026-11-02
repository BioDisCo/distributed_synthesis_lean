/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointIncidence

/-!
# One-sided actual children of a raw joint move

The raw move must contain both orientation responses before Nature resolves the
exact compressed direction.  Its *actual semantic target*, however, is
one-sided: a right block produces a process-two family and a left block
produces a process-one family.  Advancing both projections simultaneously is a
useful finite product calculation, but it is not one recursively exact world.

This file packages the one-sided targets.  Their finite codes are projections
of `profiledRawJointFamilyNext`, their cross incidence is empty, and their
`ExactFibreAt` law holds for every next direction because one opposite lane is
inactive.  The proof-side selected side is an exact-observation coordinate; it
is not a process observation or a strict-leader bit.
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

/-! ## Finite one-sided projections -/

/-- Finite target of an actually selected right block.  Only the new left
(process-two) lane is live. -/
noncomputable def profiledRawJointRightActualFamilyNext
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointFamilyCode A (I := I) :=
  let next := profiledRawJointFamilyNext A code move direction
  { right := fun _ => none
    left := next.left
    rightPattern := fun _ _ => false
    leftPattern := next.leftPattern }

/-- Finite target of an actually selected left block. -/
noncomputable def profiledRawJointLeftActualFamilyNext
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointFamilyCode A (I := I) :=
  let next := profiledRawJointFamilyNext A code move direction
  { right := next.right
    left := fun _ => none
    rightPattern := next.rightPattern
    leftPattern := fun _ _ => false }

/-- Incidence-enriched right actual target.  No two live opposite lanes exist,
so its cross matrix is definitionally empty. -/
noncomputable def profiledRawJointRightActualIncidenceNext
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointIncidenceCode A (I := I) :=
  { family := profiledRawJointRightActualFamilyNext A code move direction
    cross := fun _ _ => false }

/-- Left actual target mirror. -/
noncomputable def profiledRawJointLeftActualIncidenceNext
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointIncidenceCode A (I := I) :=
  { family := profiledRawJointLeftActualFamilyNext A code move direction
    cross := fun _ _ => false }

/-! ## Literal one-sided semantic targets -/

/-- Literal target selected when the right lane is the actual compressed
block. -/
def ProfiledRawJointSemanticFamily.rightActualChild
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointSemanticFamily A strategy (I := I) where
  right := fun _ => none
  left := family.rightSelectedChild A direction
  right_view_shared := by simp
  left_view_shared := family.rightSelectedChild_view_shared A direction

/-- Literal left-block target. -/
def ProfiledRawJointSemanticFamily.leftActualChild
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointSemanticFamily A strategy (I := I) where
  right := family.leftSelectedChild A direction
  left := fun _ => none
  right_view_shared := family.leftSelectedChild_view_shared A direction
  left_view_shared := by simp

omit [Fintype I] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem ProfiledRawJointSemanticFamily.rightActualChild_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.rightActualChild A direction).right = fun _ => none := rfl

omit [Fintype I] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem ProfiledRawJointSemanticFamily.rightActualChild_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.rightActualChild A direction).left =
      family.rightSelectedChild A direction := rfl

omit [Fintype I] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem ProfiledRawJointSemanticFamily.leftActualChild_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.leftActualChild A direction).right =
      family.leftSelectedChild A direction := rfl

omit [Fintype I] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem ProfiledRawJointSemanticFamily.leftActualChild_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.leftActualChild A direction).left = fun _ => none := rfl

/-! ## Strict/simultaneous local projection agreement -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Process one's newly selected family is definitionally the same whether
the global proof keeps both children (a simultaneous receive) or selects the
left actual child (the indistinguishable strict-left alternative). -/
@[simp] theorem ProfiledRawJointSemanticFamily.semanticChild_right_eq_leftActual
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.semanticChild A direction).right =
      (family.leftActualChild A direction).right :=
  rfl

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Process-two mirror: its selected family agrees between the simultaneous
successor and the indistinguishable strict-right alternative. -/
@[simp] theorem ProfiledRawJointSemanticFamily.semanticChild_left_eq_rightActual
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.semanticChild A direction).left =
      (family.rightActualChild A direction).left :=
  rfl

/-! ## Recursive exact-fibre closure -/

omit [Fintype I] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- A right actual child is an exact fibre at every subsequent direction: the
right lane is empty, making both cross-lane implications vacuous. -/
theorem ProfiledRawJointSemanticFamily.rightActualChild_exactFibreAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction nextDirection : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.rightActualChild A direction).ExactFibreAt A nextDirection := by
  constructor
  · intro rightIndex rightMember leftPivotMember hright hleft
    simp [ProfiledRawJointSemanticFamily.rightActualChild] at hright
  · intro leftIndex leftMember rightPivotMember hleft hright
    simp [ProfiledRawJointSemanticFamily.rightActualChild] at hright

omit [Fintype I] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Left actual child mirror. -/
theorem ProfiledRawJointSemanticFamily.leftActualChild_exactFibreAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction nextDirection : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.leftActualChild A direction).ExactFibreAt A nextDirection := by
  constructor
  · intro rightIndex rightMember leftPivotMember hright hleft
    simp [ProfiledRawJointSemanticFamily.leftActualChild] at hleft
  · intro leftIndex leftMember rightPivotMember hleft hright
    simp [ProfiledRawJointSemanticFamily.leftActualChild] at hleft

/-! ## Sidewise source equality without a cross-fibre hypothesis -/

omit [Fintype I] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Two process-two children selected from the same right family and the
same physical direction have the same fresh entry.  The right equality
pattern identifies their process-one views with the pivot row, while
`right_view_shared` identifies their process-two views.  Thus no fact about
the unused left pivot is needed. -/
theorem ProfiledRawJointSemanticFamily.rightSelectedChild_entry_eq_sidewise
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftChild rightChild : ProcTwoPairedEntryRep strategy × A.State)
    (hleft : family.rightSelectedChild A direction leftIndex = some leftChild)
    (hright : family.rightSelectedChild A direction rightIndex = some rightChild) :
    leftChild.1 = rightChild.1 := by
  rcases family.rightSelectedChild_eq_some_source A direction leftIndex
      leftChild hleft with
    ⟨leftMember, leftRow, hleftMember, hleftPattern, rfl⟩
  rcases family.rightSelectedChild_eq_some_source A direction rightIndex
      rightChild hright with
    ⟨rightMember, rightRow, hrightMember, hrightPattern, rfl⟩
  cases hpivot : family.right direction.rightPivot.1 with
  | none =>
      simp [ProfiledRawJointSemanticFamily.rightPattern, hleftMember,
        hpivot] at hleftPattern
  | some pivotMember =>
      have hleftSource := family.rightPattern_history_eq_pivot A direction
        leftIndex leftMember pivotMember hleftMember hpivot leftRow
          hleftPattern
      have hrightSource := family.rightPattern_history_eq_pivot A direction
        rightIndex rightMember pivotMember hrightMember hpivot rightRow
          hrightPattern
      cases leftRow <;> cases rightRow <;>
        simp [profiledRawRightSemanticChildPair, procTwoViewClassChild,
          profiledRawProcOneRowHistory] at hleftSource hrightSource ⊢ <;>
        apply procTwoFreshPair_eq_of_base_eq <;>
        exact congrArg (fun base => extendPrefix strategy base
          (direction.rightPhysicalPast.map rightEnvironment))
            (hleftSource.trans hrightSource.symm)

omit [Fintype I] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Process-one mirror: the unused right pivot is irrelevant to a literal
left-block child. -/
theorem ProfiledRawJointSemanticFamily.leftSelectedChild_entry_eq_sidewise
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftChild rightChild : ProcOnePairedEntryRep strategy × A.State)
    (hleft : family.leftSelectedChild A direction leftIndex = some leftChild)
    (hright : family.leftSelectedChild A direction rightIndex = some rightChild) :
    leftChild.1 = rightChild.1 := by
  rcases family.leftSelectedChild_eq_some_source A direction leftIndex
      leftChild hleft with
    ⟨leftMember, leftRow, hleftMember, hleftPattern, rfl⟩
  rcases family.leftSelectedChild_eq_some_source A direction rightIndex
      rightChild hright with
    ⟨rightMember, rightRow, hrightMember, hrightPattern, rfl⟩
  cases hpivot : family.left direction.leftPivot.1 with
  | none =>
      simp [ProfiledRawJointSemanticFamily.leftPattern, hleftMember,
        hpivot] at hleftPattern
  | some pivotMember =>
      have hleftSource := family.leftPattern_history_eq_pivot A direction
        leftIndex leftMember pivotMember hleftMember hpivot leftRow
          hleftPattern
      have hrightSource := family.leftPattern_history_eq_pivot A direction
        rightIndex rightMember pivotMember hrightMember hpivot rightRow
          hrightPattern
      cases leftRow <;> cases rightRow <;>
        simp [profiledRawLeftSemanticChildPair, procOneViewClassChild,
          profiledRawProcTwoRowHistory] at hleftSource hrightSource ⊢ <;>
        apply procOneFreshPair_eq_of_base_eq <;>
        exact congrArg (fun base => extendPrefix strategy base
          (direction.leftPhysicalPast.map leftEnvironment))
            (hleftSource.trans hrightSource.symm)

/-! ## Sidewise exact erasure -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The surviving process-two equality matrix after an actual right block
is computable from the old right family alone. -/
theorem ProfiledRawJointSemanticFamily.rightActualChild_code_leftPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ((family.rightActualChild A direction).code A).leftPattern =
      (profiledRawJointRightActualFamilyNext A (family.code A)
        (family.move A) direction).leftPattern := by
  classical
  funext left right
  rcases left with ⟨leftIndex, leftRow⟩
  rcases right with ⟨rightIndex, rightRow⟩
  change
    (family.rightActualChild A direction).leftPattern A
        (leftIndex, leftRow) (rightIndex, rightRow) =
      profiledRawActiveCanonicalRowPattern
        (profiledRawJointFamilyNext A (family.code A)
          (family.move A) direction).left
          (leftIndex, leftRow) (rightIndex, rightRow)
  cases hleft : family.rightSelectedChild A direction leftIndex with
  | none =>
      have hleftSlot := family.rightSelectedChild_finiteSlot A direction
        leftIndex
      rw [hleft] at hleftSlot
      simp only [Option.map_none] at hleftSlot
      simp only [profiledRawActiveCanonicalRowPattern]
      rw [← hleftSlot]
      simp [ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.rightActualChild,
        ProfiledRawJointSemanticFamily.leftPattern,
        profiledRawJointRightActualFamilyNext,
        profiledRawActiveCanonicalRowPattern, hleft]
  | some leftChild =>
      cases hright : family.rightSelectedChild A direction rightIndex with
      | none =>
          have hrightSlot := family.rightSelectedChild_finiteSlot A direction
            rightIndex
          rw [hright] at hrightSlot
          simp only [Option.map_none] at hrightSlot
          simp only [profiledRawActiveCanonicalRowPattern]
          rw [← hrightSlot]
          simp [ProfiledRawJointSemanticFamily.code,
            ProfiledRawJointSemanticFamily.rightActualChild,
            ProfiledRawJointSemanticFamily.leftPattern,
            profiledRawJointRightActualFamilyNext,
            profiledRawActiveCanonicalRowPattern, hleft, hright]
      | some rightChild =>
          have hleftSlot := family.rightSelectedChild_finiteSlot A direction
            leftIndex
          have hrightSlot := family.rightSelectedChild_finiteSlot A direction
            rightIndex
          rw [hleft] at hleftSlot
          rw [hright] at hrightSlot
          simp only [Option.map_some] at hleftSlot hrightSlot
          simp only [profiledRawActiveCanonicalRowPattern]
          rw [← hleftSlot, ← hrightSlot]
          have hentry := family.rightSelectedChild_entry_eq_sidewise A
            direction leftIndex rightIndex leftChild rightChild hleft hright
          cases leftRow <;> cases rightRow <;>
            simp [ProfiledRawJointSemanticFamily.code,
              ProfiledRawJointSemanticFamily.rightActualChild,
              ProfiledRawJointSemanticFamily.leftPattern,
              profiledRawJointRightActualFamilyNext,
              profiledRawActiveCanonicalRowPattern,
              profiledRawProcTwoRowHistory, hleft, hright, hentry,
              rightChild.1.other_view_ne,
              rightChild.1.other_view_ne.symm]

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The surviving process-one equality matrix after an actual left block is
the symmetric sidewise update. -/
theorem ProfiledRawJointSemanticFamily.leftActualChild_code_rightPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ((family.leftActualChild A direction).code A).rightPattern =
      (profiledRawJointLeftActualFamilyNext A (family.code A)
        (family.move A) direction).rightPattern := by
  classical
  funext left right
  rcases left with ⟨leftIndex, leftRow⟩
  rcases right with ⟨rightIndex, rightRow⟩
  change
    (family.leftActualChild A direction).rightPattern A
        (leftIndex, leftRow) (rightIndex, rightRow) =
      profiledRawActiveCanonicalRowPattern
        (profiledRawJointFamilyNext A (family.code A)
          (family.move A) direction).right
          (leftIndex, leftRow) (rightIndex, rightRow)
  cases hleft : family.leftSelectedChild A direction leftIndex with
  | none =>
      have hleftSlot := family.leftSelectedChild_finiteSlot A direction
        leftIndex
      rw [hleft] at hleftSlot
      simp only [Option.map_none] at hleftSlot
      simp only [profiledRawActiveCanonicalRowPattern]
      rw [← hleftSlot]
      simp [ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.leftActualChild,
        ProfiledRawJointSemanticFamily.rightPattern,
        profiledRawJointLeftActualFamilyNext,
        profiledRawActiveCanonicalRowPattern, hleft]
  | some leftChild =>
      cases hright : family.leftSelectedChild A direction rightIndex with
      | none =>
          have hrightSlot := family.leftSelectedChild_finiteSlot A direction
            rightIndex
          rw [hright] at hrightSlot
          simp only [Option.map_none] at hrightSlot
          simp only [profiledRawActiveCanonicalRowPattern]
          rw [← hrightSlot]
          simp [ProfiledRawJointSemanticFamily.code,
            ProfiledRawJointSemanticFamily.leftActualChild,
            ProfiledRawJointSemanticFamily.rightPattern,
            profiledRawJointLeftActualFamilyNext,
            profiledRawActiveCanonicalRowPattern, hleft, hright]
      | some rightChild =>
          have hleftSlot := family.leftSelectedChild_finiteSlot A direction
            leftIndex
          have hrightSlot := family.leftSelectedChild_finiteSlot A direction
            rightIndex
          rw [hleft] at hleftSlot
          rw [hright] at hrightSlot
          simp only [Option.map_some] at hleftSlot hrightSlot
          simp only [profiledRawActiveCanonicalRowPattern]
          rw [← hleftSlot, ← hrightSlot]
          have hentry := family.leftSelectedChild_entry_eq_sidewise A
            direction leftIndex rightIndex leftChild rightChild hleft hright
          cases leftRow <;> cases rightRow <;>
            simp [ProfiledRawJointSemanticFamily.code,
              ProfiledRawJointSemanticFamily.leftActualChild,
              ProfiledRawJointSemanticFamily.rightPattern,
              profiledRawJointLeftActualFamilyNext,
              profiledRawActiveCanonicalRowPattern,
              profiledRawProcOneRowHistory, hleft, hright, hentry,
              rightChild.1.other_view_ne,
              rightChild.1.other_view_ne.symm]

/-! ## Exact finite erasure -/

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- An actual right child has the announced finite family code without any
condition on the unused left pivot. -/
theorem ProfiledRawJointSemanticFamily.rightActualChild_code_eq_sidewise
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.rightActualChild A direction).code A =
      profiledRawJointRightActualFamilyNext A (family.code A) (family.move A)
        direction := by
  apply ProfiledRawJointFamilyCode.eq_of_fields A
  · funext index
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.rightActualChild,
      profiledRawJointRightActualFamilyNext]
  · exact family.semanticChild_code_left A direction
  · funext left right
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.rightActualChild,
      ProfiledRawJointSemanticFamily.rightPattern,
      profiledRawJointRightActualFamilyNext]
  · exact family.rightActualChild_code_leftPattern A direction

/-- Left-orientation mirror. -/
theorem ProfiledRawJointSemanticFamily.leftActualChild_code_eq_sidewise
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.leftActualChild A direction).code A =
      profiledRawJointLeftActualFamilyNext A (family.code A) (family.move A)
        direction := by
  apply ProfiledRawJointFamilyCode.eq_of_fields A
  · exact family.semanticChild_code_right A direction
  · funext index
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.leftActualChild,
      profiledRawJointLeftActualFamilyNext]
  · exact family.leftActualChild_code_rightPattern A direction
  · funext left right
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.leftActualChild,
      ProfiledRawJointSemanticFamily.leftPattern,
      profiledRawJointLeftActualFamilyNext]

/-- Incidence-enriched sidewise erasure for an actual right block. -/
theorem
    ProfiledRawJointSemanticFamily.rightActualChild_incidenceCode_eq_sidewise
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.rightActualChild A direction).incidenceCode A =
      profiledRawJointRightActualIncidenceNext A (family.code A)
        (family.move A) direction := by
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · exact family.rightActualChild_code_eq_sidewise A direction
  · funext right left
    simp [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.crossIncidence,
      ProfiledRawJointSemanticFamily.rightActualChild,
      profiledRawJointRightActualIncidenceNext]

/-- Incidence-enriched sidewise erasure for an actual left block. -/
theorem
    ProfiledRawJointSemanticFamily.leftActualChild_incidenceCode_eq_sidewise
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.leftActualChild A direction).incidenceCode A =
      profiledRawJointLeftActualIncidenceNext A (family.code A)
        (family.move A) direction := by
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · exact family.leftActualChild_code_eq_sidewise A direction
  · funext right left
    simp [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.crossIncidence,
      ProfiledRawJointSemanticFamily.leftActualChild,
      profiledRawJointLeftActualIncidenceNext]

/-- The literal right actual child erases to the one-sided projection of the
source-free joint successor. -/
theorem ProfiledRawJointSemanticFamily.rightActualChild_code_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (common : ProfiledRawJointCommonSourceAt A family direction) :
    (family.rightActualChild A direction).code A =
      profiledRawJointRightActualFamilyNext A (family.code A) (family.move A)
        direction := by
  apply ProfiledRawJointFamilyCode.eq_of_fields A
  · funext index
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.rightActualChild,
      profiledRawJointRightActualFamilyNext]
  · exact family.semanticChild_code_left A direction
  · funext left right
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.rightActualChild,
      ProfiledRawJointSemanticFamily.rightPattern,
      profiledRawJointRightActualFamilyNext]
  · change ((family.semanticChild A direction).code A).leftPattern = _
    exact family.semanticChild_code_leftPattern A direction common

/-- Left finite-erasure mirror. -/
theorem ProfiledRawJointSemanticFamily.leftActualChild_code_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (common : ProfiledRawJointCommonSourceAt A family direction) :
    (family.leftActualChild A direction).code A =
      profiledRawJointLeftActualFamilyNext A (family.code A) (family.move A)
        direction := by
  apply ProfiledRawJointFamilyCode.eq_of_fields A
  · exact family.semanticChild_code_right A direction
  · funext index
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.leftActualChild,
      profiledRawJointLeftActualFamilyNext]
  · change ((family.semanticChild A direction).code A).rightPattern = _
    exact family.semanticChild_code_rightPattern A direction common
  · funext left right
    simp [ProfiledRawJointSemanticFamily.code,
      ProfiledRawJointSemanticFamily.leftActualChild,
      ProfiledRawJointSemanticFamily.leftPattern,
      profiledRawJointLeftActualFamilyNext]

/-- Full incidence-code equality for a right actual target. -/
theorem ProfiledRawJointSemanticFamily.rightActualChild_incidenceCode_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (common : ProfiledRawJointCommonSourceAt A family direction) :
    (family.rightActualChild A direction).incidenceCode A =
      profiledRawJointRightActualIncidenceNext A (family.code A)
        (family.move A) direction := by
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · exact family.rightActualChild_code_eq A direction common
  · funext right left
    simp [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.crossIncidence,
      ProfiledRawJointSemanticFamily.rightActualChild,
      profiledRawJointRightActualIncidenceNext]

/-- Full incidence-code equality for a left actual target. -/
theorem ProfiledRawJointSemanticFamily.leftActualChild_incidenceCode_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (common : ProfiledRawJointCommonSourceAt A family direction) :
    (family.leftActualChild A direction).incidenceCode A =
      profiledRawJointLeftActualIncidenceNext A (family.code A)
        (family.move A) direction := by
  apply ProfiledRawJointIncidenceCode.eq_of_fields A
  · exact family.leftActualChild_code_eq A direction common
  · funext right left
    simp [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.crossIncidence,
      ProfiledRawJointSemanticFamily.leftActualChild,
      profiledRawJointLeftActualIncidenceNext]

end

end


end DetParityAutomaton

end DistributedSynthesis
