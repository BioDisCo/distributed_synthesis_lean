/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLeftSourceRealization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonSource

/-!
# One semantic child of a raw joint family

The two one-sided literal child constructions assemble into one semantic
family before rationalization.  Under the source `ExactFibreAt` hypothesis,
the common-source theorem also identifies its exact finite code with
`profiledRawJointFamilyNext`.

This is a one-reversal theorem.  It deliberately does not assert that the
child admits a new `ExactFibreAt` direction; that is the recursive closure
question left for the next lemma.
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

/-! ## Assembly of the two literal child families -/

/-- Cross-swap the two pivot-selected literal child families.  The shared
view laws were proved independently of a rational basis in the one-sided
source-realization lemmas. -/
def ProfiledRawJointSemanticFamily.semanticChild
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointSemanticFamily A strategy (I := I) where
  right := family.leftSelectedChild A direction
  left := family.rightSelectedChild A direction
  right_view_shared := family.leftSelectedChild_view_shared A direction
  left_view_shared := family.rightSelectedChild_view_shared A direction

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

@[simp] theorem ProfiledRawJointSemanticFamily.semanticChild_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.semanticChild A direction).right =
      family.leftSelectedChild A direction := rfl

@[simp] theorem ProfiledRawJointSemanticFamily.semanticChild_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (family.semanticChild A direction).left =
      family.rightSelectedChild A direction := rfl

/-- The semantic child's right finite slots are already the computed right
slots of the raw transition. -/
theorem ProfiledRawJointSemanticFamily.semanticChild_code_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ((family.semanticChild A direction).code A).right =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).right := by
  funext index
  exact family.leftSelectedChild_finiteSlot A direction index

/-- Left finite-slot mirror. -/
theorem ProfiledRawJointSemanticFamily.semanticChild_code_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ((family.semanticChild A direction).code A).left =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).left := by
  funext index
  exact family.rightSelectedChild_finiteSlot A direction index

end

/-! ## Common-source collapse of the selected entries -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Proof arguments in a fresh-pair constructor carry no additional data:
equal generated bases give equal fresh process-one entries. -/
theorem procOneFreshPair_eq_of_base_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hleft : StrategyGeneratedPrefix strategy left)
    (hright : StrategyGeneratedPrefix strategy right)
    (inputOne : In₁) (inputTwo : In₂) (heq : left = right) :
    procOneFreshPair strategy left hleft inputOne inputTwo =
      procOneFreshPair strategy right hright inputOne inputTwo := by
  subst right
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Process-two fresh-pair mirror. -/
theorem procTwoFreshPair_eq_of_base_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hleft : StrategyGeneratedPrefix strategy left)
    (hright : StrategyGeneratedPrefix strategy right)
    (inputOne : In₁) (inputTwo : In₂) (heq : left = right) :
    procTwoFreshPair strategy left hleft inputOne inputTwo =
      procTwoFreshPair strategy right hright inputOne inputTwo := by
  subst right
  rfl

omit [Fintype I] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- All selected left-to-right children have the same literal process-one
entry once their retained source rows are identified with the common source.
The carried automaton minima may still differ, so the conclusion is only on
the entry component. -/
theorem ProfiledRawJointCommonSourceAt.leftSelectedChild_entry_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {family : ProfiledRawJointSemanticFamily A strategy (I := I)}
    {direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)}
    (common : ProfiledRawJointCommonSourceAt A family direction)
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
  have hleftSource := common.left_source leftIndex leftMember leftRow
    hleftMember hleftPattern
  have hrightSource := common.left_source rightIndex rightMember rightRow
    hrightMember hrightPattern
  cases leftRow <;> cases rightRow <;>
    simp [profiledRawLeftSemanticChildPair, procOneViewClassChild,
      profiledRawProcTwoRowHistory] at hleftSource hrightSource ⊢ <;>
    apply procOneFreshPair_eq_of_base_eq <;>
    exact congrArg (fun base => extendPrefix strategy base
      (direction.leftPhysicalPast.map leftEnvironment))
        (hleftSource.trans hrightSource.symm)

omit [Fintype I] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Right-to-left mirror: all selected children have the same literal
process-two entry. -/
theorem ProfiledRawJointCommonSourceAt.rightSelectedChild_entry_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {family : ProfiledRawJointSemanticFamily A strategy (I := I)}
    {direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)}
    (common : ProfiledRawJointCommonSourceAt A family direction)
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
  have hleftSource := common.right_source leftIndex leftMember leftRow
    hleftMember hleftPattern
  have hrightSource := common.right_source rightIndex rightMember rightRow
    hrightMember hrightPattern
  cases leftRow <;> cases rightRow <;>
    simp [profiledRawRightSemanticChildPair, procTwoViewClassChild,
      profiledRawProcOneRowHistory] at hleftSource hrightSource ⊢ <;>
    apply procTwoFreshPair_eq_of_base_eq <;>
    exact congrArg (fun base => extendPrefix strategy base
      (direction.rightPhysicalPast.map rightEnvironment))
        (hleftSource.trans hrightSource.symm)

/-! ## Exact reset of the two finite row patterns -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The semantic child's right equality matrix is exactly the active
canonical row matrix installed by the finite transition. -/
theorem ProfiledRawJointSemanticFamily.semanticChild_code_rightPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (common : ProfiledRawJointCommonSourceAt A family direction) :
    ((family.semanticChild A direction).code A).rightPattern =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).rightPattern := by
  classical
  funext left right
  rcases left with ⟨leftIndex, leftRow⟩
  rcases right with ⟨rightIndex, rightRow⟩
  change
    (family.semanticChild A direction).rightPattern A
        (leftIndex, leftRow) (rightIndex, rightRow) =
      profiledRawActiveCanonicalRowPattern
        (profiledRawJointFamilyNext A (family.code A) (family.move A)
          direction).right (leftIndex, leftRow) (rightIndex, rightRow)
  cases hleft : family.leftSelectedChild A direction leftIndex with
  | none =>
      have hleftSlot := family.leftSelectedChild_finiteSlot A direction leftIndex
      rw [hleft] at hleftSlot
      simp only [Option.map_none] at hleftSlot
      simp only [profiledRawActiveCanonicalRowPattern]
      rw [← hleftSlot]
      simp [ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.semanticChild,
        ProfiledRawJointSemanticFamily.rightPattern,
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
            ProfiledRawJointSemanticFamily.semanticChild,
            ProfiledRawJointSemanticFamily.rightPattern,
            profiledRawActiveCanonicalRowPattern,
            hleft, hright]
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
          have hentry := common.leftSelectedChild_entry_eq A leftIndex
            rightIndex leftChild rightChild hleft hright
          cases leftRow <;> cases rightRow <;>
            simp [ProfiledRawJointSemanticFamily.code,
              ProfiledRawJointSemanticFamily.semanticChild,
              ProfiledRawJointSemanticFamily.rightPattern,
              profiledRawActiveCanonicalRowPattern,
              profiledRawProcOneRowHistory, hleft, hright, hentry,
              rightChild.1.other_view_ne,
              rightChild.1.other_view_ne.symm]

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Left equality-matrix mirror. -/
theorem ProfiledRawJointSemanticFamily.semanticChild_code_leftPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (common : ProfiledRawJointCommonSourceAt A family direction) :
    ((family.semanticChild A direction).code A).leftPattern =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).leftPattern := by
  classical
  funext left right
  rcases left with ⟨leftIndex, leftRow⟩
  rcases right with ⟨rightIndex, rightRow⟩
  change
    (family.semanticChild A direction).leftPattern A
        (leftIndex, leftRow) (rightIndex, rightRow) =
      profiledRawActiveCanonicalRowPattern
        (profiledRawJointFamilyNext A (family.code A) (family.move A)
          direction).left (leftIndex, leftRow) (rightIndex, rightRow)
  cases hleft : family.rightSelectedChild A direction leftIndex with
  | none =>
      have hleftSlot := family.rightSelectedChild_finiteSlot A direction leftIndex
      rw [hleft] at hleftSlot
      simp only [Option.map_none] at hleftSlot
      simp only [profiledRawActiveCanonicalRowPattern]
      rw [← hleftSlot]
      simp [ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.semanticChild,
        ProfiledRawJointSemanticFamily.leftPattern,
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
            ProfiledRawJointSemanticFamily.semanticChild,
            ProfiledRawJointSemanticFamily.leftPattern,
            profiledRawActiveCanonicalRowPattern,
            hleft, hright]
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
          have hentry := common.rightSelectedChild_entry_eq A leftIndex
            rightIndex leftChild rightChild hleft hright
          cases leftRow <;> cases rightRow <;>
            simp [ProfiledRawJointSemanticFamily.code,
              ProfiledRawJointSemanticFamily.semanticChild,
              ProfiledRawJointSemanticFamily.leftPattern,
              profiledRawActiveCanonicalRowPattern,
              profiledRawProcTwoRowHistory, hleft, hright, hentry,
              rightChild.1.other_view_ne,
              rightChild.1.other_view_ne.symm]

/-! ## The full one-step semantic/code package -/

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Fieldwise extensionality for the raw family code. -/
theorem ProfiledRawJointFamilyCode.eq_of_fields
    (left right : ProfiledRawJointFamilyCode A (I := I))
    (hright : left.right = right.right)
    (hleft : left.left = right.left)
    (hrightPattern : left.rightPattern = right.rightPattern)
    (hleftPattern : left.leftPattern = right.leftPattern) :
    left = right := by
  cases left
  cases right
  simp_all

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- With a literal common source, all four fields of the semantic child code
are exactly the source-free finite update. -/
theorem ProfiledRawJointSemanticFamily.semanticChild_code_eq_of_commonSource
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (common : ProfiledRawJointCommonSourceAt A family direction) :
    (family.semanticChild A direction).code A =
      profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction := by
  exact ProfiledRawJointFamilyCode.eq_of_fields A _ _
    (family.semanticChild_code_right A direction)
    (family.semanticChild_code_left A direction)
    (family.semanticChild_code_rightPattern A direction common)
    (family.semanticChild_code_leftPattern A direction common)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The requested unconditional one-reversal package: an exact source fibre
has one literal semantic child whose complete finite code is the computed raw
successor.  No rational basis and no same-code representative choice occurs. -/
theorem ProfiledRawJointSemanticFamily.exists_semanticChild_code_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hexact : family.ExactFibreAt A direction) :
    ∃ child : ProfiledRawJointSemanticFamily A strategy (I := I),
      child.code A =
        profiledRawJointFamilyNext A (family.code A) (family.move A)
          direction := by
  classical
  let common := Classical.choice (family.exists_commonSourceAt A direction
    hexact)
  exact ⟨family.semanticChild A direction,
    family.semanticChild_code_eq_of_commonSource A direction common⟩

/-- Data form of the preceding theorem, useful as the transition witness for
the future input-free automaton.  It intentionally has no recursive
`ExactFibreAt` field. -/
structure ProfiledRawJointSemanticChildPackage
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) where
  child : ProfiledRawJointSemanticFamily A strategy (I := I)
  code_eq : child.code A =
    profiledRawJointFamilyNext A (family.code A) (family.move A) direction

/-- Canonical package constructed from the raw strategy and exact source
fibre. -/
noncomputable def ProfiledRawJointSemanticFamily.semanticChildPackage
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hexact : family.ExactFibreAt A direction) :
    ProfiledRawJointSemanticChildPackage A family direction := by
  classical
  let common := Classical.choice (family.exists_commonSourceAt A direction
    hexact)
  exact {
    child := family.semanticChild A direction
    code_eq := family.semanticChild_code_eq_of_commonSource A direction common }

end

end DetParityAutomaton

end DistributedSynthesis
