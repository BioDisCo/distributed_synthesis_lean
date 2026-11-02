/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLambdaFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenChildViewEquality

/-!
# Literal right-to-left source realization for the raw joint family

This file isolates the process-one/right half of the one-reversal test.  It
contains no rational basis.  For every live right member, the slot computed by
the finite raw move is exactly the profiled state of the literal
`PairedStrategyMemory` child.

The last section also materializes the semantic family of process-two
children selected by the right pivot.  This is only one half of a successor
`ProfiledRawJointSemanticFamily`: the left-to-right mirror and the joint
cross-fibre invariant must still be assembled before this can be iterated.
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
finite profiled source stored by a live semantic right member. -/
theorem ProfiledRawJointSemanticFamily.rightCandidateChild_eq_some
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (member : ProcOnePairedEntryRep strategy × A.State)
    (hmember : family.right index = some member) (row : PairedEntryRow) :
    profiledRawRightCandidateChild A (family.code A) (family.move A)
        direction (index, row) =
      some (profiledRawRightChildSlot A
        ((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.rightPhysicalPast
          direction.rightInput) := by
  simp [profiledRawRightCandidateChild,
    ProfiledRawJointSemanticFamily.code,
    ProfiledRawJointSemanticFamily.move, hmember]

/-- The finite slot computed above is definitionally the profiled state of
the literal operational child.  This is the local T1 equation needed before
any input-free rationalization. -/
theorem profiledRawRightChildSlot_eq_literalProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) :
    PairedStrategyMemory.toProfiledTreeState (A := A)
        (profiledRawRightSemanticChildMemory A member row
          direction.rightPhysicalPast direction.rightInput) =
      .inr (.inr (profiledRawRightChildSlot A
        ((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.rightPhysicalPast
          direction.rightInput)) := by
  rw [show profiledRawRightSemanticChildMemory A member row
      direction.rightPhysicalPast direction.rightInput =
      (PairedStrategyMemory.processOne member.1 member.2).step (A := A)
        (.fromOne row direction.rightPhysicalPast direction.rightInput) by rfl]
  rw [PairedStrategyMemory.toProfiledTreeState_step]
  exact pairedProfiledOneChild_eq_profiledRawRightChildSlot A
    (((member.1.code, member.2),
      rightInitialFirstProfile member.1.lambdaOfStrategy))
    member.1.lambdaOfStrategy row direction.rightPhysicalPast
      direction.rightInput

/-- Combined live-member realization: the optional finite computation is
present and its value names the literal strategy-memory child. -/
theorem ProfiledRawJointSemanticFamily.exists_rightLiteralChildSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (member : ProcOnePairedEntryRep strategy × A.State)
    (hmember : family.right index = some member) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      profiledRawRightCandidateChild A (family.code A) (family.move A)
          direction (index, row) = some slot ∧
        PairedStrategyMemory.toProfiledTreeState (A := A)
            (profiledRawRightSemanticChildMemory A member row
              direction.rightPhysicalPast direction.rightInput) =
          .inr (.inr slot) := by
  let slot := profiledRawRightChildSlot A
    ((member.1.code, member.2),
      rightInitialFirstProfile member.1.lambdaOfStrategy)
    member.1.lambdaOfStrategy row direction.rightPhysicalPast
      direction.rightInput
  exact ⟨slot,
    family.rightCandidateChild_eq_some A direction index member hmember row,
    profiledRawRightChildSlot_eq_literalProfiledState A direction member row⟩

end

/-! ## The semantic process-two child named by a finite slot -/

/-- Literal process-two entry/minimum pair produced by one active right
member.  The singleton index is deliberate: the definition depends on the
actual member, not on a representative chosen from another code fibre. -/
def profiledRawRightSemanticChildPair
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) : ProcTwoPairedEntryRep strategy × A.State :=
  let entry : Unit → ProcOnePairedEntryRep strategy := fun _ => member.1
  (procTwoViewClassChild strategy entry past input ((), row),
    procTwoViewClassChildMinimum A entry past ((), row))

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The pair above is exactly the constructor exposed by the literal memory
step. -/
theorem profiledRawRightSemanticChildMemory_eq_processTwo
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    profiledRawRightSemanticChildMemory A member row past input =
      .processTwo (profiledRawRightSemanticChildPair A member row past input).1
        (profiledRawRightSemanticChildPair A member row past input).2 := by
  classical
  let entry : Unit → ProcOnePairedEntryRep strategy := fun _ => member.1
  let minimum : Unit → A.State := fun _ => member.2
  simpa [profiledRawRightSemanticChildMemory,
    profiledRawRightSemanticChildPair, entry, minimum] using
    (pairedStrategyMemory_step_eq_procTwoViewClassChild A entry minimum
      () past input row)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Hence the finite child slot is not merely compatible with some child: it
is the exact finite erasure of the literal semantic process-two pair. -/
theorem profiledRawRightChildSlot_eq_semanticChildPairCode
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) :
    let child := profiledRawRightSemanticChildPair A member row
      direction.rightPhysicalPast direction.rightInput
    profiledRawRightChildSlot A
        ((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.rightPhysicalPast
          direction.rightInput =
      ((child.1.code, child.2),
        leftInitialFirstProfile child.1.lambdaOfStrategy) := by
  dsimp only
  have hliteral := profiledRawRightChildSlot_eq_literalProfiledState A
    direction member row
  have hmemory := profiledRawRightSemanticChildMemory_eq_processTwo A member
    row direction.rightPhysicalPast direction.rightInput
  rw [hmemory] at hliteral
  change
    Sum.inr (Sum.inr
      (((profiledRawRightSemanticChildPair A member row
            direction.rightPhysicalPast direction.rightInput).1.code,
          (profiledRawRightSemanticChildPair A member row
            direction.rightPhysicalPast direction.rightInput).2),
        leftInitialFirstProfile
          (profiledRawRightSemanticChildPair A member row
            direction.rightPhysicalPast direction.rightInput).1.lambdaOfStrategy)) =
      Sum.inr (Sum.inr (profiledRawRightChildSlot A
        ((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.rightPhysicalPast
          direction.rightInput)) at hliteral
  exact (Sum.inr.inj (Sum.inr.inj hliteral)).symm

/-! ## The pivot-selected semantic child family -/

/-- Finite erasure of a literal process-two semantic child. -/
def profiledRawLeftSlotOfSemanticPair
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (child : ProcTwoPairedEntryRep strategy × A.State) :
    ProfiledRawLeftSlot A :=
  ((child.1.code, child.2),
    leftInitialFirstProfile child.1.lambdaOfStrategy)

/-- The semantic process-two child selected for one lineage by the right
pivot.  Its two tests deliberately mirror
`profiledRawJointChildCodeOfPattern`; row-functionality ensures that the
`.first` tie-break never hides a simultaneously live `.both` corner. -/
def ProfiledRawJointSemanticFamily.rightSelectedChild
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) : Option (ProcTwoPairedEntryRep strategy × A.State) :=
  match family.right index with
  | none => none
  | some member =>
      if family.rightPattern A (index, .first) direction.rightPivot = true then
        some (profiledRawRightSemanticChildPair A member .first
          direction.rightPhysicalPast direction.rightInput)
      else if family.rightPattern A (index, .both) direction.rightPivot = true then
        some (profiledRawRightSemanticChildPair A member .both
          direction.rightPhysicalPast direction.rightInput)
      else none

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype I] [Inhabited In₁] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- A live candidate in the pivot equality class is represented by the
materialized semantic child.  Row-functionality discharges the only subtle
case: a `.both` candidate cannot be shadowed by the deterministic `.first`
tie-break. -/
theorem ProfiledRawJointSemanticFamily.rightSelectedChild_eq_some_of_pattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (member : ProcOnePairedEntryRep strategy × A.State)
    (hmember : family.right index = some member) (row : PairedEntryRow)
    (hpattern :
      family.rightPattern A (index, row) direction.rightPivot = true) :
    family.rightSelectedChild A direction index =
      some (profiledRawRightSemanticChildPair A member row
        direction.rightPhysicalPast direction.rightInput) := by
  cases row with
  | first =>
      simp [ProfiledRawJointSemanticFamily.rightSelectedChild, hmember,
        hpattern]
  | both =>
      have hfirst :
          family.rightPattern A (index, .first) direction.rightPivot ≠ true := by
        intro hfirst
        exact family.rightPattern_rowFunctionalAt A direction.rightPivot index
          ⟨hfirst, hpattern⟩
      simp [ProfiledRawJointSemanticFamily.rightSelectedChild, hmember,
        hfirst, hpattern]

omit [Fintype I] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Every selected semantic child comes with its live source member, selected
row, and the exact equality-pattern membership used by the finite child. -/
theorem ProfiledRawJointSemanticFamily.rightSelectedChild_eq_some_source
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) (child : ProcTwoPairedEntryRep strategy × A.State)
    (hchild : family.rightSelectedChild A direction index = some child) :
    ∃ member row,
      family.right index = some member ∧
        family.rightPattern A (index, row) direction.rightPivot = true ∧
        child = profiledRawRightSemanticChildPair A member row
          direction.rightPhysicalPast direction.rightInput := by
  cases hmember : family.right index with
  | none =>
      simp [ProfiledRawJointSemanticFamily.rightSelectedChild, hmember] at hchild
  | some member =>
      by_cases hfirst :
          family.rightPattern A (index, .first) direction.rightPivot = true
      · refine ⟨member, .first, by simpa using hmember, hfirst, ?_⟩
        simpa [ProfiledRawJointSemanticFamily.rightSelectedChild, hmember,
          hfirst] using hchild.symm
      · by_cases hboth :
            family.rightPattern A (index, .both) direction.rightPivot = true
        · refine ⟨member, .both, by simpa using hmember, hboth, ?_⟩
          simpa [ProfiledRawJointSemanticFamily.rightSelectedChild, hmember,
            hfirst, hboth] using hchild.symm
        · simp [ProfiledRawJointSemanticFamily.rightSelectedChild, hmember,
            hfirst, hboth] at hchild

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Pointwise semantic/finite agreement for the pivot-selected right child
family.  Thus the finite successor's left slots already have literal semantic
representatives; no choice or rational basis is used. -/
theorem ProfiledRawJointSemanticFamily.rightSelectedChild_finiteSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (index : I) :
    (family.rightSelectedChild A direction index).map
        (profiledRawLeftSlotOfSemanticPair A) =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).left index := by
  cases hmember : family.right index with
  | none =>
      simp [ProfiledRawJointSemanticFamily.rightSelectedChild,
        profiledRawJointFamilyNext, profiledRawRightIndexedChildCode,
        profiledRawJointChildCodeOfPattern, profiledRawRightCandidateChild,
        profiledRawOptionalChildSlots, ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.move,
        ProfiledRawJointSemanticFamily.rightPattern, hmember]
  | some member =>
      by_cases hfirst :
          family.rightPattern A (index, .first) direction.rightPivot = true
      · simp [ProfiledRawJointSemanticFamily.rightSelectedChild,
          profiledRawJointFamilyNext, profiledRawRightIndexedChildCode,
          profiledRawJointChildCodeOfPattern, profiledRawRightCandidateChild,
          profiledRawOptionalChildSlots, ProfiledRawJointSemanticFamily.code,
          ProfiledRawJointSemanticFamily.move, hmember, hfirst,
          profiledRawLeftSlotOfSemanticPair,
          profiledRawRightChildSlot_eq_semanticChildPairCode A direction
            member .first]
      · by_cases hboth :
            family.rightPattern A (index, .both) direction.rightPivot = true
        · simp [ProfiledRawJointSemanticFamily.rightSelectedChild,
            profiledRawJointFamilyNext, profiledRawRightIndexedChildCode,
            profiledRawJointChildCodeOfPattern, profiledRawRightCandidateChild,
            profiledRawOptionalChildSlots,
            ProfiledRawJointSemanticFamily.code,
            ProfiledRawJointSemanticFamily.move, hmember, hfirst, hboth,
            profiledRawLeftSlotOfSemanticPair,
            profiledRawRightChildSlot_eq_semanticChildPairCode A direction
              member .both]
        · simp [ProfiledRawJointSemanticFamily.rightSelectedChild,
            profiledRawJointFamilyNext, profiledRawRightIndexedChildCode,
            profiledRawJointChildCodeOfPattern, profiledRawRightCandidateChild,
            profiledRawOptionalChildSlots,
            ProfiledRawJointSemanticFamily.code,
            ProfiledRawJointSemanticFamily.move, hmember, hfirst, hboth]

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [Inhabited In₁] in
/-- Two pattern-selected right members yield process-two children with the
same process-two view.  This is the semantic content of the right equality
matrix; the proof uses the already established exact child-view equivalence,
not a reconstructed leader bit. -/
theorem ProfiledRawJointSemanticFamily.rightPattern_children_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftMember rightMember : ProcOnePairedEntryRep strategy × A.State)
    (hleftMember : family.right leftIndex = some leftMember)
    (hrightMember : family.right rightIndex = some rightMember)
    (leftRow rightRow : PairedEntryRow)
    (hleftPattern :
      family.rightPattern A (leftIndex, leftRow) direction.rightPivot = true)
    (hrightPattern :
      family.rightPattern A (rightIndex, rightRow) direction.rightPivot = true) :
    currentView Proc.two
        (profiledRawRightSemanticChildPair A leftMember leftRow
          direction.rightPhysicalPast direction.rightInput).1.rightHistory =
      currentView Proc.two
        (profiledRawRightSemanticChildPair A rightMember rightRow
          direction.rightPhysicalPast direction.rightInput).1.rightHistory := by
  classical
  cases hpivot : family.right direction.rightPivot.1 with
  | none =>
      simp [ProfiledRawJointSemanticFamily.rightPattern, hleftMember,
        hpivot] at hleftPattern
  | some pivotMember =>
      have hleftOld :
          currentView Proc.two
              (profiledRawProcOneRowHistory leftMember.1 leftRow) =
            currentView Proc.two
              (profiledRawProcOneRowHistory pivotMember.1
                direction.rightPivot.2) := by
        simpa [ProfiledRawJointSemanticFamily.rightPattern, hleftMember,
          hpivot] using hleftPattern
      have hrightOld :
          currentView Proc.two
              (profiledRawProcOneRowHistory rightMember.1 rightRow) =
            currentView Proc.two
              (profiledRawProcOneRowHistory pivotMember.1
                direction.rightPivot.2) := by
        simpa [ProfiledRawJointSemanticFamily.rightPattern, hrightMember,
          hpivot] using hrightPattern
      let entry : Bool → ProcOnePairedEntryRep strategy := fun side =>
        if side then rightMember.1 else leftMember.1
      have hblind : ∀ left right,
          currentView Proc.one (entry left).leftHistory =
            currentView Proc.one (entry right).leftHistory := by
        intro left right
        cases left <;> cases right
        · rfl
        · simpa [entry] using family.right_view_shared leftIndex rightIndex
            leftMember rightMember hleftMember hrightMember
        · simpa [entry] using (family.right_view_shared leftIndex rightIndex
            leftMember rightMember hleftMember hrightMember).symm
        · rfl
      have hrow :
          currentView Proc.two
              (procOneViewClassRowHistory entry (false, leftRow)) =
            currentView Proc.two
              (procOneViewClassRowHistory entry (true, rightRow)) := by
        simpa [entry, procOneViewClassRowHistory,
          profiledRawProcOneRowHistory] using hleftOld.trans hrightOld.symm
      have hchild :=
        (procTwoViewClassChild_view_eq_iff strategy entry hblind
          direction.rightPhysicalPast direction.rightInput
          (false, leftRow) (true, rightRow)).2 hrow
      simpa [profiledRawRightSemanticChildPair, entry] using hchild

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [Inhabited In₁] in
/-- The materialized right-selected semantic children form one genuine
process-two local-view family. -/
theorem ProfiledRawJointSemanticFamily.rightSelectedChild_view_shared
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ∀ leftIndex rightIndex leftChild rightChild,
      family.rightSelectedChild A direction leftIndex = some leftChild →
      family.rightSelectedChild A direction rightIndex = some rightChild →
      currentView Proc.two leftChild.1.rightHistory =
        currentView Proc.two rightChild.1.rightHistory := by
  intro leftIndex rightIndex leftChild rightChild hleft hright
  rcases family.rightSelectedChild_eq_some_source A direction leftIndex
      leftChild hleft with
    ⟨leftMember, leftRow, hleftMember, hleftPattern, rfl⟩
  rcases family.rightSelectedChild_eq_some_source A direction rightIndex
      rightChild hright with
    ⟨rightMember, rightRow, hrightMember, hrightPattern, rfl⟩
  exact family.rightPattern_children_view_eq A direction leftIndex rightIndex
    leftMember rightMember hleftMember hrightMember leftRow rightRow
      hleftPattern hrightPattern

/-! ## Exact-fibre wrapper and the remaining joint seam -/

/-- The complete right half of one raw source realization.  `exactFibre` is
retained because the eventual bidirectional assembly needs it, although the
right-local T1 and representation equations above are stronger: they do not
consume the opposite lane. -/
structure ProfiledRawJointRightSourceRealization
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) : Prop where
  exactFibre : family.ExactFibreAt A direction
  childViewShared : ∀ leftIndex rightIndex leftChild rightChild,
    family.rightSelectedChild A direction leftIndex = some leftChild →
    family.rightSelectedChild A direction rightIndex = some rightChild →
    currentView Proc.two leftChild.1.rightHistory =
      currentView Proc.two rightChild.1.rightHistory
  finiteSlots : ∀ index,
    (family.rightSelectedChild A direction index).map
        (profiledRawLeftSlotOfSemanticPair A) =
      (profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction).left index

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The right half passes the one-reversal source-realization test
unconditionally once the joint source is an exact fibre. -/
theorem ProfiledRawJointSemanticFamily.rightSourceRealization
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hexact : family.ExactFibreAt A direction) :
    ProfiledRawJointRightSourceRealization A family direction where
  exactFibre := hexact
  childViewShared := family.rightSelectedChild_view_shared A direction
  finiteSlots := family.rightSelectedChild_finiteSlot A direction

/-- What this one-sided theorem deliberately does not assert.  A recursive
successor needs the mirror child family and a *new* direction whose two pivots
make the cross-lane exact-fibre equations true.  Naming that datum prevents
the already disproved move of treating two marginal child families as if
they automatically had a shared origin. -/
def ProfiledRawJointSuccessorExactFibreWitness
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (next : ProfiledRawJointSemanticFamily A strategy (I := I)) : Prop :=
  ∃ nextDirection : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂),
    next.ExactFibreAt A nextDirection

end

end DetParityAutomaton

end DistributedSynthesis
