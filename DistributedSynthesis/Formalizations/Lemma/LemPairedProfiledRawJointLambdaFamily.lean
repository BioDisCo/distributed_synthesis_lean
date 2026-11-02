/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryWinningRun
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalTree

/-!
# Raw bidirectional lambda families

A move contains right and left block lambdas simultaneously. Its finite
source code consists of profiled paired-entry states. The source-free child
functions apply `pairedProfiledOneChild` and `pairedProfiledTwoChild`
pointwise and cross the two orientations.

The final predicate requires a common raw move compatible with every exact
family in the same code fibre. This is an explicit uniformity condition:
pointwise rational runs, individual observation successors, and separately
rationalized trees do not themselves establish it. Each lane has one common
physical past/input and one pivot equality class.
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
variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-! ## Minimal basis-free lineage interface -/

/-- One persistent lineage and one of its two physical entry rows. -/
abbrev ProfiledRawJointCandidate (I : Type i) := I × PairedEntryRow

/-- Complete finite equality matrix on the row candidates. -/
abbrev ProfiledRawJointEqualityPattern (I : Type i) :=
  ProfiledRawJointCandidate I → ProfiledRawJointCandidate I → Bool

/-- At one pivot, a semantic equality class contains at most one row of each
persistent lineage. -/
def ProfiledRawJointEqualityPattern.RowFunctionalAt
    (pattern : ProfiledRawJointEqualityPattern I)
    (pivot : ProfiledRawJointCandidate I) : Prop :=
  ∀ member,
    ¬ (pattern (member, .first) pivot = true ∧
      pattern (member, .both) pivot = true)

/-- Ordered partial child family. -/
abbrev ProfiledRawJointChildCode (I : Type i) (Root : Type*) :=
  I → Option (PairedEntryRow × Root)

/-- Materialize exactly the pivot equality class, using `.first` only as a
deterministic tie-break outside the semantic row-functional invariant. -/
def profiledRawJointChildCodeOfPattern
    {Root : Type*} (pattern : ProfiledRawJointEqualityPattern I)
    (root : ProfiledRawJointCandidate I → Root)
    (pivot : ProfiledRawJointCandidate I) :
    ProfiledRawJointChildCode I Root :=
  fun member =>
    if pattern (member, .first) pivot = true then
      some (.first, root (member, .first))
    else if pattern (member, .both) pivot = true then
      some (.both, root (member, .both))
    else none

/-! ## Raw move and finite source code -/

/-- Finite payload of one live right-oriented profiled entry. -/
abbrev ProfiledRawRightSlot :=
  (((A.State × A.State) × A.State) ×
    RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))

/-- Finite payload of one live left-oriented profiled entry. -/
abbrev ProfiledRawLeftSlot :=
  (((A.State × A.State) × A.State) ×
    LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))

/-- Two optional finite families.  No exact history or selected real member is
stored in this code. -/
structure ProfiledRawJointFamilyCode where
  right : I → Option (ProfiledRawRightSlot A)
  left : I → Option (ProfiledRawLeftSlot A)
  rightPattern : ProfiledRawJointEqualityPattern I
  leftPattern : ProfiledRawJointEqualityPattern I

noncomputable instance : Fintype (ProfiledRawJointFamilyCode A (I := I)) := by
  classical
  letI : Fintype A.State := A.stateFinite
  letI : Fintype (ProfiledRawRightSlot A) := Fintype.ofFinite _
  letI : Fintype (ProfiledRawLeftSlot A) := Fintype.ofFinite _
  letI : Fintype (I → Option (ProfiledRawRightSlot A)) := Fintype.ofFinite _
  letI : Fintype (I → Option (ProfiledRawLeftSlot A)) := Fintype.ofFinite _
  letI : Fintype (ProfiledRawJointEqualityPattern I) := Fintype.ofFinite _
  let Rep :=
    (I → Option (ProfiledRawRightSlot A)) ×
      (I → Option (ProfiledRawLeftSlot A)) ×
      ProfiledRawJointEqualityPattern I ×
      ProfiledRawJointEqualityPattern I
  let e : ProfiledRawJointFamilyCode A (I := I) ≃ Rep :=
    { toFun := fun code =>
        (code.right, code.left, code.rightPattern, code.leftPattern)
      invFun := fun code => ⟨code.1, code.2.1, code.2.2.1, code.2.2.2⟩
      left_inv := by intro code; cases code; rfl
      right_inv := by intro code; rcases code with ⟨right, left, rp, lp⟩; rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- One pre-rationalization label.  The lambda types may be infinite; this is
harmless because they occur only under the transition existential. -/
structure ProfiledRawJointLambdaFamilyMove where
  source : ProfiledRawJointFamilyCode A (I := I)
  rightLambda : I → Option
    (ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
  leftLambda : I → Option
    (ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

/-- Exact block data for both proof-side families.  Each lane has one common
physical block history/input and a proof-side pivot.  This common-history
shape is essential: an `I → past` array is too permissive and does not
preserve an exact-view class.  Lineage tags are retained only for the later
receiver-table lookup; they are erased by `rightPhysicalPast`/`leftPhysicalPast`.

The whole value is an input-free tree direction, not a process observation or
a strict-leader signal. -/
structure ProfiledRawJointFamilyDirection where
  rightPivot : ProfiledRawJointCandidate I
  rightTaggedPast : List ((I × In₂) × In₁)
  rightInput : In₂ × In₁
  leftPivot : ProfiledRawJointCandidate I
  leftTaggedPast : List ((I × In₁) × In₂)
  leftInput : In₁ × In₂

/-- Physical right-block past shared by every candidate. -/
def ProfiledRawJointFamilyDirection.rightPhysicalPast
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) : List (In₂ × In₁) :=
  direction.rightTaggedPast.map fun old => (old.1.2, old.2)

/-- Physical left-block mirror. -/
def ProfiledRawJointFamilyDirection.leftPhysicalPast
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) : List (In₁ × In₂) :=
  direction.leftTaggedPast.map fun old => (old.1.2, old.2)

/-! ## History-free pointwise children -/

/-- Finite left payload produced by one right lambda. -/
def profiledRawRightChildSlot
    (source : ProfiledRawRightSlot A)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) : ProfiledRawLeftSlot A :=
  let code := source.1.1
  let start := match row with | .first => code.1 | .both => code.2
  let word := match row with
    | .first => lambda.leftWord past
    | .both => lambda.bothWord past
  let childCode := match row with
    | .first => pairedRightFreshChildCodeLeft A code lambda past input
    | .both => pairedRightFreshChildCodeBoth A code lambda past input
  ((childCode, blockMinState A start word),
    rightClosingProfile lambda row past input)

/-- Finite right payload produced by one left lambda. -/
def profiledRawLeftChildSlot
    (source : ProfiledRawLeftSlot A)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) : ProfiledRawRightSlot A :=
  let code := source.1.1
  let start := match row with | .first => code.1 | .both => code.2
  let word := match row with
    | .first => lambda.rightWord past
    | .both => lambda.bothWord past
  let childCode := match row with
    | .first => pairedLeftFreshChildCodeRight A code lambda past input
    | .both => pairedLeftFreshChildCodeBoth A code lambda past input
  ((childCode, blockMinState A start word),
    leftClosingProfile lambda row past input)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- The payload helper is literally the existing profiled right child. -/
theorem pairedProfiledOneChild_eq_profiledRawRightChildSlot
    (source : ProfiledRawRightSlot A)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    pairedProfiledOneChild A source.1.1 lambda row past input =
      .inr (.inr (profiledRawRightChildSlot A source lambda row past input)) := by
  cases row <;> rfl

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Left mirror of the definitional child equation. -/
theorem pairedProfiledTwoChild_eq_profiledRawLeftChildSlot
    (source : ProfiledRawLeftSlot A)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    pairedProfiledTwoChild A source.1.1 lambda row past input =
      .inr (.inl (profiledRawLeftChildSlot A source lambda row past input)) := by
  cases row <;> rfl

/-- Optional finite child attached to one right-row candidate. -/
def profiledRawRightCandidateChild
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (candidate : ProfiledRawJointCandidate I) :
    Option (ProfiledRawLeftSlot A) :=
  match code.right candidate.1, move.rightLambda candidate.1 with
  | some source, some lambda =>
      some (profiledRawRightChildSlot A source lambda candidate.2
        direction.rightPhysicalPast direction.rightInput)
  | _, _ => none

/-- Optional finite child attached to one left-row candidate. -/
def profiledRawLeftCandidateChild
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (candidate : ProfiledRawJointCandidate I) :
    Option (ProfiledRawRightSlot A) :=
  match code.left candidate.1, move.leftLambda candidate.1 with
  | some source, some lambda =>
      some (profiledRawLeftChildSlot A source lambda candidate.2
        direction.leftPhysicalPast direction.leftInput)
  | _, _ => none

/-- Materialize only the old-right equality class selected by Nature's
pivot.  Other old members become absent; they are not incorrectly required to
join one successor family. -/
def profiledRawRightIndexedChildCode
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointChildCode I (Option (ProfiledRawLeftSlot A)) :=
  profiledRawJointChildCodeOfPattern code.rightPattern
    (profiledRawRightCandidateChild A code move direction)
    direction.rightPivot

/-- Old-left equality-class mirror. -/
def profiledRawLeftIndexedChildCode
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointChildCode I (Option (ProfiledRawRightSlot A)) :=
  profiledRawJointChildCodeOfPattern code.leftPattern
    (profiledRawLeftCandidateChild A code move direction)
    direction.leftPivot

/-- Forget the selected row and flatten the optional root. -/
def profiledRawOptionalChildSlots
    {Root : Type*} (children : ProfiledRawJointChildCode I (Option Root)) :
    I → Option Root :=
  fun index => (children index).bind fun child => child.2

/-- Canonical post-handoff row pattern, gated by the active slots. -/
def profiledRawActiveCanonicalRowPattern
    {Root : Type*} (slots : I → Option Root) :
    ProfiledRawJointEqualityPattern I :=
  fun left right =>
    match slots left.1, slots right.1 with
    | some _, some _ => decide (left.2 = right.2)
    | _, _ => false

/-- Total one-step finite code update.  Each lane keeps precisely the pivot
equality class, cross-swaps orientation, and installs the canonical active
row pattern.  This computation does not prove that one next raw move is
uniform over all exact families erased to the resulting code. -/
def profiledRawJointFamilyNext
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointFamilyCode A (I := I) :=
  let right := profiledRawOptionalChildSlots
    (profiledRawLeftIndexedChildCode A code move direction)
  let left := profiledRawOptionalChildSlots
    (profiledRawRightIndexedChildCode A code move direction)
  { right := right
    left := left
    rightPattern := profiledRawActiveCanonicalRowPattern right
    leftPattern := profiledRawActiveCanonicalRowPattern left }

/-- Harmless finite destination for an incompatible exact observation. -/
def profiledRawJointFamilySinkCode :
    ProfiledRawJointFamilyCode A (I := I) :=
  { right := fun _ => none
    left := fun _ => none
    rightPattern := fun _ _ => false
    leftPattern := fun _ _ => false }

/-! ## Source-free legality -/

/-- Node-local law for the raw joint label.  Every active source has one raw
T2-winning lambda with the stored initial profile, inactive slots carry no
lambda, and all active blind lambdas in one orientation are equal. -/
def ProfiledRawJointLambdaFamilyMove.Valid
    (code : ProfiledRawJointFamilyCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I)) : Prop :=
  move.source = code ∧
    (∀ pivot, code.rightPattern.RowFunctionalAt pivot) ∧
    (∀ pivot, code.leftPattern.RowFunctionalAt pivot) ∧
    (∀ index source, code.right index = some source →
      ∃ lambda, move.rightLambda index = some lambda ∧
        rightInitialFirstProfile lambda = source.2 ∧
        PairedRightForeverAccepts A source.1.1 lambda) ∧
    (∀ index, code.right index = none → move.rightLambda index = none) ∧
    (∀ index source, code.left index = some source →
      ∃ lambda, move.leftLambda index = some lambda ∧
        leftInitialFirstProfile lambda = source.2 ∧
        PairedLeftForeverAccepts A source.1.1 lambda) ∧
    (∀ index, code.left index = none → move.leftLambda index = none) ∧
    (∀ left right leftLambda rightLambda,
      move.rightLambda left = some leftLambda →
      move.rightLambda right = some rightLambda →
      leftLambda.blind = rightLambda.blind) ∧
    (∀ left right leftLambda rightLambda,
      move.leftLambda left = some leftLambda →
      move.leftLambda right = some rightLambda →
      leftLambda.blind = rightLambda.blind)

/-! ## Construction from one raw distributed strategy -/

/-- Proof-side simultaneous family before any rational run is selected. -/
structure ProfiledRawJointSemanticFamily
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  right : I → Option (ProcOnePairedEntryRep strategy × A.State)
  left : I → Option (ProcTwoPairedEntryRep strategy × A.State)
  right_view_shared : ∀ leftIndex rightIndex leftMember rightMember,
    right leftIndex = some leftMember →
      right rightIndex = some rightMember →
      currentView Proc.one leftMember.1.leftHistory =
        currentView Proc.one rightMember.1.leftHistory
  left_view_shared : ∀ leftIndex rightIndex leftMember rightMember,
    left leftIndex = some leftMember →
      left rightIndex = some rightMember →
      currentView Proc.two leftMember.1.rightHistory =
        currentView Proc.two rightMember.1.rightHistory

/-! ## Proof-side equality patterns and the joint-fibre seam -/

/-- Literal history selected by a row of one process-one entry. -/
def profiledRawProcOneRowHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcOnePairedEntryRep strategy) (row : PairedEntryRow) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match row with
  | .first => entry.leftHistory
  | .both => entry.bothHistory

/-- Process-two mirror. -/
def profiledRawProcTwoRowHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : ProcTwoPairedEntryRep strategy) (row : PairedEntryRow) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match row with
  | .first => entry.rightHistory
  | .both => entry.bothHistory

/-- Exact old-opposite-view matrix of the optional right family.  Inactive
slots are unrelated to every candidate. -/
noncomputable def ProfiledRawJointSemanticFamily.rightPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I)) :
    ProfiledRawJointEqualityPattern I := by
  classical
  exact fun left right =>
    match family.right left.1, family.right right.1 with
    | some leftMember, some rightMember =>
        decide
          (currentView Proc.two
              (profiledRawProcOneRowHistory leftMember.1 left.2) =
            currentView Proc.two
              (profiledRawProcOneRowHistory rightMember.1 right.2))
    | _, _ => false

/-- Exact old-opposite-view matrix of the optional left family. -/
noncomputable def ProfiledRawJointSemanticFamily.leftPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I)) :
    ProfiledRawJointEqualityPattern I := by
  classical
  exact fun left right =>
    match family.left left.1, family.left right.1 with
    | some leftMember, some rightMember =>
        decide
          (currentView Proc.one
              (profiledRawProcTwoRowHistory leftMember.1 left.2) =
            currentView Proc.one
              (profiledRawProcTwoRowHistory rightMember.1 right.2))
    | _, _ => false

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The semantic right matrix cannot select both rows of one lineage. -/
theorem ProfiledRawJointSemanticFamily.rightPattern_rowFunctionalAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (pivot : ProfiledRawJointCandidate I) :
    (family.rightPattern A).RowFunctionalAt pivot := by
  classical
  intro lineage hboth
  cases hpivot : family.right pivot.1 with
  | none =>
      simp [ProfiledRawJointSemanticFamily.rightPattern, hpivot] at hboth
  | some pivotMember =>
      cases hmember : family.right lineage with
      | none =>
          simp [ProfiledRawJointSemanticFamily.rightPattern, hpivot,
            hmember] at hboth
      | some member =>
          have hfirst :
              currentView Proc.two
                  (profiledRawProcOneRowHistory member.1 .first) =
                currentView Proc.two
                  (profiledRawProcOneRowHistory pivotMember.1 pivot.2) := by
            simpa [ProfiledRawJointSemanticFamily.rightPattern, hpivot,
              hmember] using hboth.1
          have hboth' :
              currentView Proc.two
                  (profiledRawProcOneRowHistory member.1 .both) =
                currentView Proc.two
                  (profiledRawProcOneRowHistory pivotMember.1 pivot.2) := by
            simpa [ProfiledRawJointSemanticFamily.rightPattern, hpivot,
              hmember] using hboth.2
          exact member.1.other_view_ne
            (by simpa [profiledRawProcOneRowHistory] using
              hfirst.trans hboth'.symm)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Left row-functionality mirror. -/
theorem ProfiledRawJointSemanticFamily.leftPattern_rowFunctionalAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (pivot : ProfiledRawJointCandidate I) :
    (family.leftPattern A).RowFunctionalAt pivot := by
  classical
  intro lineage hboth
  cases hpivot : family.left pivot.1 with
  | none =>
      simp [ProfiledRawJointSemanticFamily.leftPattern, hpivot] at hboth
  | some pivotMember =>
      cases hmember : family.left lineage with
      | none =>
          simp [ProfiledRawJointSemanticFamily.leftPattern, hpivot,
            hmember] at hboth
      | some member =>
          have hfirst :
              currentView Proc.one
                  (profiledRawProcTwoRowHistory member.1 .first) =
                currentView Proc.one
                  (profiledRawProcTwoRowHistory pivotMember.1 pivot.2) := by
            simpa [ProfiledRawJointSemanticFamily.leftPattern, hpivot,
              hmember] using hboth.1
          have hboth' :
              currentView Proc.one
                  (profiledRawProcTwoRowHistory member.1 .both) =
                currentView Proc.one
                  (profiledRawProcTwoRowHistory pivotMember.1 pivot.2) := by
            simpa [ProfiledRawJointSemanticFamily.leftPattern, hpivot,
              hmember] using hboth.2
          exact member.1.other_view_ne
            (by simpa [profiledRawProcTwoRowHistory] using
              hfirst.trans hboth'.symm)

/-- The two pivots must belong to the same two process-local fibres as the
opposite blind families.  This is a genuinely joint proof-side law: two
independently correct marginal equality matrices do not imply it. -/
def ProfiledRawJointSemanticFamily.ExactFibreAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) : Prop :=
  (∀ rightIndex rightMember leftPivotMember,
      family.right rightIndex = some rightMember →
      family.left direction.leftPivot.1 = some leftPivotMember →
      currentView Proc.one rightMember.1.leftHistory =
        currentView Proc.one
          (profiledRawProcTwoRowHistory leftPivotMember.1
            direction.leftPivot.2)) ∧
    (∀ leftIndex leftMember rightPivotMember,
      family.left leftIndex = some leftMember →
      family.right direction.rightPivot.1 = some rightPivotMember →
      currentView Proc.two leftMember.1.rightHistory =
        currentView Proc.two
          (profiledRawProcOneRowHistory rightPivotMember.1
            direction.rightPivot.2))

/-! ## Literal semantic children -/

/-- Literal child memory of one old right-oriented semantic member. -/
def profiledRawRightSemanticChildMemory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) : PairedStrategyMemory A strategy :=
  (PairedStrategyMemory.processOne member.1 member.2).step (A := A)
    (.fromOne row past input)

/-- Literal child memory of one old left-oriented semantic member. -/
def profiledRawLeftSemanticChildMemory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) : PairedStrategyMemory A strategy :=
  (PairedStrategyMemory.processTwo member.1 member.2).step (A := A)
    (.fromTwo row past input)

/-- Erase semantic histories to the finite profiled source code. -/
def ProfiledRawJointSemanticFamily.code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I)) :
    ProfiledRawJointFamilyCode A (I := I) where
  right := fun index => (family.right index).map fun member =>
    ((member.1.code, member.2),
      rightInitialFirstProfile member.1.lambdaOfStrategy)
  left := fun index => (family.left index).map fun member =>
    ((member.1.code, member.2),
      leftInitialFirstProfile member.1.lambdaOfStrategy)
  rightPattern := family.rightPattern A
  leftPattern := family.leftPattern A

/-- Read every raw lambda at once.  No inner `HasRationalRun` is constructed. -/
def ProfiledRawJointSemanticFamily.move
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I)) :
    ProfiledRawJointLambdaFamilyMove A (I := I) where
  source := family.code A
  rightLambda := fun index => (family.right index).map fun member =>
    member.1.lambdaOfStrategy
  leftLambda := fun index => (family.left index).map fun member =>
    member.1.lambdaOfStrategy

omit [Fintype I] [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- A global winner makes the one raw joint family locally legal.  This is
the exact pre-basis analogue of the old per-entry legality proof. -/
theorem ProfiledRawJointSemanticFamily.move_valid_of_winning
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := I)) :
    (family.move A).Valid A (family.code A) := by
  classical
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact family.rightPattern_rowFunctionalAt A
  · exact family.leftPattern_rowFunctionalAt A
  · intro index source hsource
    cases hmember : family.right index with
    | none => simp [ProfiledRawJointSemanticFamily.code, hmember] at hsource
    | some member =>
        have hsource' :
            source = ((member.1.code, member.2),
              rightInitialFirstProfile member.1.lambdaOfStrategy) := by
          simpa [ProfiledRawJointSemanticFamily.code, hmember] using hsource.symm
        subst source
        refine ⟨member.1.lambdaOfStrategy, ?_, rfl, ?_⟩
        · simp [ProfiledRawJointSemanticFamily.move, hmember]
        · exact pairedRightForeverAccepts_of_winning A strategy hwin member.1
  · intro index hsource
    cases hmember : family.right index with
    | none => simp [ProfiledRawJointSemanticFamily.move, hmember]
    | some member =>
        simp [ProfiledRawJointSemanticFamily.code, hmember] at hsource
  · intro index source hsource
    cases hmember : family.left index with
    | none => simp [ProfiledRawJointSemanticFamily.code, hmember] at hsource
    | some member =>
        have hsource' :
            source = ((member.1.code, member.2),
              leftInitialFirstProfile member.1.lambdaOfStrategy) := by
          simpa [ProfiledRawJointSemanticFamily.code, hmember] using hsource.symm
        subst source
        refine ⟨member.1.lambdaOfStrategy, ?_, rfl, ?_⟩
        · simp [ProfiledRawJointSemanticFamily.move, hmember]
        · exact pairedLeftForeverAccepts_of_winning A strategy hwin member.1
  · intro index hsource
    cases hmember : family.left index with
    | none => simp [ProfiledRawJointSemanticFamily.move, hmember]
    | some member =>
        simp [ProfiledRawJointSemanticFamily.code, hmember] at hsource
  · intro left right leftLambda rightLambda hleft hright
    cases hleftMember : family.right left with
    | none => simp [ProfiledRawJointSemanticFamily.move, hleftMember] at hleft
    | some leftMember =>
        cases hrightMember : family.right right with
        | none => simp [ProfiledRawJointSemanticFamily.move, hrightMember] at hright
        | some rightMember =>
            have hleftLambda : leftLambda = leftMember.1.lambdaOfStrategy := by
              simpa [ProfiledRawJointSemanticFamily.move, hleftMember] using
                hleft.symm
            have hrightLambda : rightLambda = rightMember.1.lambdaOfStrategy := by
              simpa [ProfiledRawJointSemanticFamily.move, hrightMember] using
                hright.symm
            subst leftLambda
            subst rightLambda
            exact blockSenderOne_eq_of_view_eq strategy
              (family.right_view_shared left right leftMember rightMember
                hleftMember hrightMember)
  · intro left right leftLambda rightLambda hleft hright
    cases hleftMember : family.left left with
    | none => simp [ProfiledRawJointSemanticFamily.move, hleftMember] at hleft
    | some leftMember =>
        cases hrightMember : family.left right with
        | none => simp [ProfiledRawJointSemanticFamily.move, hrightMember] at hright
        | some rightMember =>
            have hleftLambda : leftLambda = leftMember.1.lambdaOfStrategy := by
              simpa [ProfiledRawJointSemanticFamily.move, hleftMember] using
                hleft.symm
            have hrightLambda : rightLambda = rightMember.1.lambdaOfStrategy := by
              simpa [ProfiledRawJointSemanticFamily.move, hrightMember] using
                hright.symm
            subst leftLambda
            subst rightLambda
            exact blockSenderTwo_eq_of_view_eq strategy
              (family.left_view_shared left right leftMember rightMember
                hleftMember hrightMember)

/-! ## The deliberately unresolved recursive seam -/

/-- Abstract compatibility of a semantic exact-view family with one raw
joint move.  Concrete consumers may take this to mean literal strategy
readback, a physical local-controller law, or an allowed-edge law after the
single outer rationalization. -/
abbrev ProfiledRawJointMoveCompatibility
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  ProfiledRawJointSemanticFamily A strategy (I := I) →
    ProfiledRawJointLambdaFamilyMove A (I := I) → Prop

/-- The same finite code must admit one move compatible with every exact
family hidden in that code fibre.  The present finite slots and the two
within-lane equality matrices do **not** prove this proposition.

This is the fail-fast boundary exposed by the former exact-view pair-tree and
policy-uniformity attempts.  Rationalizing the right and left projections
separately has the wrong quantifier order; merely carrying an exact child as
an observation also does not make the next move uniform on a finite code. -/
def ProfiledRawJointSameCodeUniformity
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (Compatible : ProfiledRawJointMoveCompatibility A strategy (I := I)) :
    Prop :=
  ∀ left right,
    left.code A = right.code A →
      ∃ move, Compatible left move ∧ Compatible right move

end

end DetParityAutomaton

end DistributedSynthesis
