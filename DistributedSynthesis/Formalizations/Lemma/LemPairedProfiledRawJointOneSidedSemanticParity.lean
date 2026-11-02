/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedSemanticTree
import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeLiveness
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization

/-!
# Unconditional parity of the one-sided raw joint semantic tree

The objective monitor reads only successive finite incidence codes.  For one
canonical hidden side and lineage, either its run reaches the even dead sink,
or every positive-time slot names a literal member of the corresponding raw
semantic family.  In the latter case consecutive members are literal
`PairedStrategyMemory.step`s.  The resulting compressed memory branch is
accepted by `PairedStrategyMemory.switchingAccepts_of_winning`.

The side used below is a hidden objective coordinate and the side in an
actual direction is input-free proof-tree data.  Neither is an observation or
a strict-leader flag supplied to a process.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))

/-! ## The finite code-observable objective -/

/-- Deterministic parity monitor over successive finite one-sided codes. -/
noncomputable def profiledRawJointOneSidedCodeParityDPA
    (initialCode : ProfiledRawJointIncidenceCode A (I := I)) :
    DetParityAutomaton (ProfiledRawJointIncidenceCode A (I := I)) :=
  codedAlternatingIndexedLineageCodeDPA initialCode
    (profiledRawJointOneSidedCurrentSlots A)
    (profiledRawJointThreadRootPriority A)

/-- Exact semantic state at positive branch depth `n + 1`, corresponding to
letter `n` of the child-code word. -/
def profiledRawJointOneSidedPositiveBranchState
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) (n : Nat) :=
  (profiledRawJointOneSidedSemanticTree A initial).stateAt
    (branchNode branch (n + 1))

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Consecutive positive-depth semantic states are related by the literal
one-sided semantic step. -/
theorem profiledRawJointOneSidedPositiveBranchState_succ
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) (n : Nat) :
    profiledRawJointOneSidedPositiveBranchState A strategy initial branch
        (n + 1) =
      (profiledRawJointOneSidedPositiveBranchState A strategy initial branch
        n).step A (branch (n + 1)) := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  change raw.stateAt (branchNode branch (n + 2)) =
    raw.step (raw.stateAt (branchNode branch (n + 1))) (branch (n + 1))
  rw [show branchNode branch (n + 2) =
      branchNode branch (n + 1) ++ [branch (n + 1)] by rfl,
    raw.stateAt_append]

/-- Canonical positive-time live monitor record. -/
noncomputable def profiledRawJointOneSidedBranchLiveAt
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :=
  codedAlternatingIndexedLineageCodeLiveAtOfNeverDead (initial.code A)
    (profiledRawJointOneSidedCurrentSlots A)
    ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
    initialSide lineage hnever n

/-! ## Literal memories carried by live slots -/

/-- A positive-time live slot together with the exact semantic member that
it erases. -/
inductive ProfiledRawJointOneSidedBranchMemoryPackage
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) : Type _ where
  | right
      (hside : (profiledRawJointOneSidedBranchLiveAt A strategy initial branch
        initialSide lineage hnever n).side = .right)
      (member : ProcOnePairedEntryRep strategy × A.State)
      (hmember : (profiledRawJointOneSidedPositiveBranchState A strategy
        initial branch n).family.right lineage = some member)
      (hroot :
        (profiledRawJointOneSidedBranchLiveAt A strategy initial branch
          initialSide lineage hnever n).root =
          Sum.inl (((member.1.code, member.2),
            rightInitialFirstProfile member.1.lambdaOfStrategy)))
  | left
      (hside : (profiledRawJointOneSidedBranchLiveAt A strategy initial branch
        initialSide lineage hnever n).side = .left)
      (member : ProcTwoPairedEntryRep strategy × A.State)
      (hmember : (profiledRawJointOneSidedPositiveBranchState A strategy
        initial branch n).family.left lineage = some member)
      (hroot :
        (profiledRawJointOneSidedBranchLiveAt A strategy initial branch
          initialSide lineage hnever n).root =
          Sum.inr (((member.1.code, member.2),
            leftInitialFirstProfile member.1.lambdaOfStrategy)))

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Every live finite slot is the erasure of one literal semantic memory. -/
theorem exists_profiledRawJointOneSidedBranchMemoryPackage
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :
    Nonempty (ProfiledRawJointOneSidedBranchMemoryPackage A strategy initial
      branch initialSide lineage hnever n) := by
  classical
  let state := profiledRawJointOneSidedPositiveBranchState A strategy initial
    branch n
  let live := profiledRawJointOneSidedBranchLiveAt A strategy initial branch
    initialSide lineage hnever n
  have hslot := live.slot
  change profiledRawJointOneSidedCurrentSlots A live.side
      (state.code A) lineage = some live.root at hslot
  cases hside : live.side with
  | right =>
      cases hmember : state.family.right lineage with
      | none =>
          simp [profiledRawJointOneSidedCurrentSlots,
            ProfiledRawJointOneSidedSemanticState.code,
            ProfiledRawJointSemanticFamily.incidenceCode,
            ProfiledRawJointSemanticFamily.code, hside, hmember] at hslot
      | some member =>
          have hroot : live.root = Sum.inl (((member.1.code, member.2),
              rightInitialFirstProfile member.1.lambdaOfStrategy)) := by
            simpa [profiledRawJointOneSidedCurrentSlots,
              ProfiledRawJointOneSidedSemanticState.code,
              ProfiledRawJointSemanticFamily.incidenceCode,
              ProfiledRawJointSemanticFamily.code, hside, hmember] using
              hslot.symm
          exact ⟨ProfiledRawJointOneSidedBranchMemoryPackage.right
            (A := A) hside member hmember hroot⟩
  | left =>
      cases hmember : state.family.left lineage with
      | none =>
          simp [profiledRawJointOneSidedCurrentSlots,
            ProfiledRawJointOneSidedSemanticState.code,
            ProfiledRawJointSemanticFamily.incidenceCode,
            ProfiledRawJointSemanticFamily.code, hside, hmember] at hslot
      | some member =>
          have hroot : live.root = Sum.inr (((member.1.code, member.2),
              leftInitialFirstProfile member.1.lambdaOfStrategy)) := by
            simpa [profiledRawJointOneSidedCurrentSlots,
              ProfiledRawJointOneSidedSemanticState.code,
              ProfiledRawJointSemanticFamily.incidenceCode,
              ProfiledRawJointSemanticFamily.code, hside, hmember] using
              hslot.symm
          exact ⟨ProfiledRawJointOneSidedBranchMemoryPackage.left
            (A := A) hside member hmember hroot⟩

/-- Canonically choose the literal memory named at a live code slot. -/
noncomputable def profiledRawJointOneSidedBranchMemoryPackage
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :
    ProfiledRawJointOneSidedBranchMemoryPackage A strategy initial branch
      initialSide lineage hnever n :=
  Classical.choice (exists_profiledRawJointOneSidedBranchMemoryPackage A
    strategy initial branch initialSide lineage hnever n)

/-- Literal paired-strategy memory at positive monitor time `n + 1`. -/
noncomputable def profiledRawJointOneSidedBranchMemory
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) : PairedStrategyMemory A strategy :=
  match profiledRawJointOneSidedBranchMemoryPackage A strategy initial branch
      initialSide lineage hnever n with
  | .right _ member _ _ => .processOne member.1 member.2
  | .left _ member _ _ => .processTwo member.1 member.2

/-! ## Consecutive live memories are literal operational steps -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- At every live depth, the next literal memory is obtained by one genuine
compressed direction.  The row is recovered from the pivot-selected semantic
child; it is not guessed from equality of finite roots. -/
theorem exists_profiledRawJointOneSidedBranchMemory_step
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :
    ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
      profiledRawJointOneSidedBranchMemory A strategy initial branch
          initialSide lineage hnever (n + 1) =
        (profiledRawJointOneSidedBranchMemory A strategy initial branch
          initialSide lineage hnever n).step (A := A) direction := by
  classical
  have hflip :=
    codedAlternatingIndexedLineageCodeLiveAtOfNeverDead_side_succ
      (initial.code A) (profiledRawJointOneSidedCurrentSlots A)
      ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
      initialSide lineage hnever n
  change
    (profiledRawJointOneSidedBranchLiveAt A strategy initial branch
      initialSide lineage hnever (n + 1)).side =
      (profiledRawJointOneSidedBranchLiveAt A strategy initial branch
        initialSide lineage hnever n).side.other at hflip
  let pState := profiledRawJointOneSidedPositiveBranchState A strategy initial
    branch n
  let qState := profiledRawJointOneSidedPositiveBranchState A strategy initial
    branch (n + 1)
  have hstate : qState = pState.step A (branch (n + 1)) := by
    exact profiledRawJointOneSidedPositiveBranchState_succ A strategy initial
      branch n
  cases hpkg : profiledRawJointOneSidedBranchMemoryPackage A strategy initial
      branch initialSide lineage hnever n with
  | right hpSide pMember hpMember hpRoot =>
      change pState.family.right lineage = some pMember at hpMember
      cases qpkg : profiledRawJointOneSidedBranchMemoryPackage A strategy
          initial branch initialSide lineage hnever (n + 1) with
      | right hqSide qMember hqMember hqRoot =>
          rw [hpSide, hqSide] at hflip
          cases hflip
      | left hqSide qMember hqMember hqRoot =>
          change qState.family.left lineage = some qMember at hqMember
          cases hactual : (branch (n + 1)).side with
          | left =>
              rw [hstate] at hqMember
              simp [ProfiledRawJointOneSidedSemanticState.step, hactual,
                ProfiledRawJointSemanticFamily.leftActualChild] at hqMember
          | right =>
              rw [hstate] at hqMember
              have hselected : pState.family.rightSelectedChild A
                  (branch (n + 1)).direction lineage = some qMember := by
                simpa [ProfiledRawJointOneSidedSemanticState.step, hactual,
                  ProfiledRawJointSemanticFamily.rightActualChild] using
                  hqMember
              rcases pState.family.rightSelectedChild_eq_some_source A
                  (branch (n + 1)).direction lineage qMember hselected with
                ⟨source, row, hsource, hpattern, hq⟩
              have hsourceEq : source = pMember :=
                Option.some.inj (hsource.symm.trans hpMember)
              subst source
              subst qMember
              refine ⟨.fromOne row
                (branch (n + 1)).direction.rightPhysicalPast
                (branch (n + 1)).direction.rightInput, ?_⟩
              simp only [profiledRawJointOneSidedBranchMemory, hpkg, qpkg]
              exact (profiledRawRightSemanticChildMemory_eq_processTwo A
                pMember row
                (branch (n + 1)).direction.rightPhysicalPast
                (branch (n + 1)).direction.rightInput).symm
  | left hpSide pMember hpMember hpRoot =>
      change pState.family.left lineage = some pMember at hpMember
      cases qpkg : profiledRawJointOneSidedBranchMemoryPackage A strategy
          initial branch initialSide lineage hnever (n + 1) with
      | left hqSide qMember hqMember hqRoot =>
          rw [hpSide, hqSide] at hflip
          cases hflip
      | right hqSide qMember hqMember hqRoot =>
          change qState.family.right lineage = some qMember at hqMember
          cases hactual : (branch (n + 1)).side with
          | right =>
              rw [hstate] at hqMember
              simp [ProfiledRawJointOneSidedSemanticState.step, hactual,
                ProfiledRawJointSemanticFamily.rightActualChild] at hqMember
          | left =>
              rw [hstate] at hqMember
              have hselected : pState.family.leftSelectedChild A
                  (branch (n + 1)).direction lineage = some qMember := by
                simpa [ProfiledRawJointOneSidedSemanticState.step, hactual,
                  ProfiledRawJointSemanticFamily.leftActualChild] using
                  hqMember
              rcases pState.family.leftSelectedChild_eq_some_source A
                  (branch (n + 1)).direction lineage qMember hselected with
                ⟨source, row, hsource, hpattern, hq⟩
              have hsourceEq : source = pMember :=
                Option.some.inj (hsource.symm.trans hpMember)
              subst source
              subst qMember
              refine ⟨.fromTwo row
                (branch (n + 1)).direction.leftPhysicalPast
                (branch (n + 1)).direction.leftInput, ?_⟩
              simp only [profiledRawJointOneSidedBranchMemory, hpkg, qpkg]
              exact (profiledRawLeftSemanticChildMemory_eq_processOne A
                pMember row
                (branch (n + 1)).direction.leftPhysicalPast
                (branch (n + 1)).direction.leftInput).symm

/-- The recovered literal compressed direction at one live depth. -/
noncomputable def profiledRawJointOneSidedBranchMemoryDirection
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
  Classical.choose (exists_profiledRawJointOneSidedBranchMemory_step A strategy
    initial branch initialSide lineage hnever n)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Specification of the recovered direction. -/
theorem profiledRawJointOneSidedBranchMemory_step
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :
    profiledRawJointOneSidedBranchMemory A strategy initial branch initialSide
        lineage hnever (n + 1) =
      (profiledRawJointOneSidedBranchMemory A strategy initial branch
        initialSide lineage hnever n).step (A := A)
        (profiledRawJointOneSidedBranchMemoryDirection A strategy initial
          branch initialSide lineage hnever n) :=
  Classical.choose_spec
    (exists_profiledRawJointOneSidedBranchMemory_step A strategy initial branch
      initialSide lineage hnever n)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The selected memory at depth `n` is exactly the operational memory reached
by folding the recovered directions from the first live memory. -/
theorem profiledRawJointOneSidedBranchMemory_eq_atNode
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :
    profiledRawJointOneSidedBranchMemory A strategy initial branch initialSide
        lineage hnever n =
      PairedStrategyMemory.atNode (A := A)
        (profiledRawJointOneSidedBranchMemory A strategy initial branch
          initialSide lineage hnever 0)
        (branchNode (profiledRawJointOneSidedBranchMemoryDirection A strategy
          initial branch initialSide lineage hnever) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointOneSidedBranchMemory_step A strategy initial branch
        initialSide lineage hnever n, ih]
      rw [show branchNode
          (profiledRawJointOneSidedBranchMemoryDirection A strategy initial
            branch initialSide lineage hnever) (n + 1) =
        branchNode
            (profiledRawJointOneSidedBranchMemoryDirection A strategy initial
              branch initialSide lineage hnever) n ++
          [profiledRawJointOneSidedBranchMemoryDirection A strategy initial
            branch initialSide lineage hnever n] by rfl,
        PairedStrategyMemory.atNode_append]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At positive monitor time `n + 1`, the code-monitor priority is exactly
the paired-entry priority of the literal memory carried by that live slot. -/
theorem profiledRawJointOneSidedBranch_live_priority
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :
    (codedAlternatingIndexedLineageCodeThreadSystem (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)) =
      pairedEntryPriority A
        (profiledRawJointOneSidedBranchMemory A strategy initial branch
          initialSide lineage hnever n).toTreeState := by
  let live := profiledRawJointOneSidedBranchLiveAt A strategy initial branch
    initialSide lineage hnever n
  rw [live.run_eq]
  change profiledRawJointThreadRootPriority A live.root = _
  cases hpkg : profiledRawJointOneSidedBranchMemoryPackage A strategy initial
      branch initialSide lineage hnever n with
  | right hside member hmember hroot =>
      simp only [profiledRawJointOneSidedBranchMemory, hpkg]
      rw [hroot]
      rfl
  | left hside member hmember hroot =>
      simp only [profiledRawJointOneSidedBranchMemory, hpkg]
      rw [hroot]
      rfl

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The literal memory sequence extracted from a never-dead code lineage has
min-even parity, directly from the original winning strategy. -/
theorem profiledRawJointOneSidedBranchMemory_minEven
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A)
        ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch)
        initialSide lineage (n + 1)).2 ≠ .dead) :
    NatSeqMinEvenParity (fun n =>
      pairedEntryPriority A
        (profiledRawJointOneSidedBranchMemory A strategy initial branch
          initialSide lineage hnever n).toTreeState) := by
  let memory := profiledRawJointOneSidedBranchMemory A strategy initial branch
    initialSide lineage hnever
  let directions := profiledRawJointOneSidedBranchMemoryDirection A strategy
    initial branch initialSide lineage hnever
  have hparity := PairedStrategyMemory.switchingAccepts_of_winning
    (A := A) hwin (memory 0) directions
  convert hparity using 1
  funext n
  change pairedEntryPriority A (memory n).toTreeState = _
  have hmemory : memory n = PairedStrategyMemory.atNode (A := A) (memory 0)
      (branchNode directions n) := by
    exact profiledRawJointOneSidedBranchMemory_eq_atNode A strategy initial
      branch initialSide lineage hnever n
  rw [hmemory]
  rfl

/-! ## Unconditional code-parity acceptance -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every branch of the corrected one-sided semantic tree is accepted by the
finite code-observable objective monitor. -/
theorem profiledRawJointOneSidedSemanticTree_accepts
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (branch : Nat → ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointOneSidedCodeParityDPA A (initial.code A)).Accepts
      ((profiledRawJointOneSidedSemanticTree A initial).childCodeWord
        branch) := by
  classical
  let word :=
    (profiledRawJointOneSidedSemanticTree A initial).childCodeWord branch
  rw [profiledRawJointOneSidedCodeParityDPA,
    codedAlternatingIndexedLineageCodeDPA_accepts_iff]
  intro initialSide lineage
  by_cases hdead : ∃ n,
      (codedAlternatingIndexedLineageCodeRun (initial.code A)
        (profiledRawJointOneSidedCurrentSlots A) word initialSide lineage
        n).2 = .dead
  · rcases hdead with ⟨n, hdead⟩
    have hparity := codedAlternatingIndexedLineageRun_minEven_of_eventually_dead
      (initial.code A)
      (fun _ (_ : Unit) childCode => childCode)
      (profiledRawJointOneSidedCurrentSlots A)
      (codedAlternatingIndexedLineageCodeChild
        (profiledRawJointOneSidedCurrentSlots A))
      (profiledRawJointThreadRootPriority A)
      (fun k => (Unit.unit, word k)) initialSide lineage hdead
    simpa [codedAlternatingIndexedLineageCodeThreadSystem,
      codedAlternatingIndexedLineageCodeRun] using hparity
  · have hnever : ∀ n,
        (codedAlternatingIndexedLineageCodeRun (initial.code A)
          (profiledRawJointOneSidedCurrentSlots A) word initialSide lineage
          (n + 1)).2 ≠ .dead := by
      intro n hnow
      exact hdead ⟨n + 1, hnow⟩
    let priorities := fun n =>
      (codedAlternatingIndexedLineageCodeThreadSystem (initial.code A)
          (profiledRawJointOneSidedCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun (initial.code A)
          (profiledRawJointOneSidedCurrentSlots A) word initialSide lineage n)
    have hsemantic := profiledRawJointOneSidedBranchMemory_minEven A strategy
      hwin initial branch initialSide lineage hnever
    have htail : NatSeqMinEvenParity (fun n => priorities (1 + n)) := by
      convert hsemantic using 1
      funext n
      simpa [priorities, word, Nat.add_comm] using
        profiledRawJointOneSidedBranch_live_priority A strategy initial branch
          initialSide lineage hnever n
    exact (natSeqMinEvenParity_shift priorities 1).mp htail

/-! ## Complete source-free certificate and the single final basis call -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The corrected raw joint semantic tree satisfies legality, source-free T1,
and code-observable parity unconditionally from the original winner. -/
theorem profiledRawJointOneSidedSemanticTree_codeParityCertificate
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    let raw := profiledRawJointOneSidedSemanticTree A initial
    SourceFreeBeliefCodeParityCertificate
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointIncidenceMoveValid A)
      (profiledRawJointOneSidedNext A)
      raw := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact profiledRawJointOneSidedSemanticTree_valid A hwin initial node
  · intro node direction
    exact profiledRawJointOneSidedSemanticTree_next_code A initial node direction
  · intro branch
    exact profiledRawJointOneSidedSemanticTree_accepts A strategy hwin initial
      branch

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- One application of the named input-free rational basis yields the finite
code-observable policy.  No inner or per-lineage rational basis is used. -/
theorem nonempty_profiledRawJointOneSidedCodeParityRationalPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (basis :
      (sourceFreeBeliefCodeParityRunAutomaton
        (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
        (initial.code A)
        (ProfiledRawJointIncidenceMoveValid A)
        (profiledRawJointOneSidedNext A)).RationalRunBasis) :
    Nonempty (SourceFreeBeliefCodeParityRationalPolicy
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointIncidenceMoveValid A)
      (profiledRawJointOneSidedNext A)) := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  exact SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
    (initial.code A)
    (ProfiledRawJointIncidenceMoveValid A)
    (profiledRawJointOneSidedNext A)
    raw
    (profiledRawJointOneSidedSemanticTree_codeParityCertificate A strategy
      hwin initial)
    basis

end


end DetParityAutomaton

end DistributedSynthesis
