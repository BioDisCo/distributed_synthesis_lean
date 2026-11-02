/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedSemanticTree

/-!
# Literal memory bridges for one-sided raw successors

The code-parity proof follows one persistent lineage.  This file supplies its
local semantic step: whenever that lineage is present before and after a
matching one-sided update, the target entry is the literal
`PairedStrategyMemory.step` of the source entry for one recovered row.

The row is proof-side data recovered from the pivot equality class.  It is
not stored in a process state and is irrelevant to the finite code-parity
monitor, which reads only the target root.
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

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- A live right-to-left one-sided target is exactly one operational
process-one-to-process-two memory step. -/
theorem ProfiledRawJointOneSidedSemanticState.exists_right_memory_bridge
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hside : actual.side = .right)
    (lineage : I)
    (source : ProcOnePairedEntryRep strategy × A.State)
    (target : ProcTwoPairedEntryRep strategy × A.State)
    (hsource : state.family.right lineage = some source)
    (htarget : (state.step A actual).family.left lineage = some target) :
    ∃ row : PairedEntryRow,
      target = profiledRawRightSemanticChildPair A source row
        actual.direction.rightPhysicalPast actual.direction.rightInput ∧
      PairedStrategyMemory.processTwo target.1 target.2 =
        (PairedStrategyMemory.processOne source.1 source.2).step (A := A)
          (.fromOne row actual.direction.rightPhysicalPast
            actual.direction.rightInput) := by
  have hselected :
      state.family.rightSelectedChild A actual.direction lineage =
        some target := by
    simpa [ProfiledRawJointOneSidedSemanticState.step, hside] using htarget
  rcases state.family.rightSelectedChild_eq_some_source A actual.direction
      lineage target hselected with
    ⟨member, row, hmember, _hpattern, htargetEq⟩
  have hmemberEq : member = source :=
    Option.some.inj (hmember.symm.trans hsource)
  subst member
  subst target
  refine ⟨row, rfl, ?_⟩
  exact (profiledRawRightSemanticChildMemory_eq_processTwo A source row
    actual.direction.rightPhysicalPast actual.direction.rightInput).symm

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Left-to-right mirror. -/
theorem ProfiledRawJointOneSidedSemanticState.exists_left_memory_bridge
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hside : actual.side = .left)
    (lineage : I)
    (source : ProcTwoPairedEntryRep strategy × A.State)
    (target : ProcOnePairedEntryRep strategy × A.State)
    (hsource : state.family.left lineage = some source)
    (htarget : (state.step A actual).family.right lineage = some target) :
    ∃ row : PairedEntryRow,
      target = profiledRawLeftSemanticChildPair A source row
        actual.direction.leftPhysicalPast actual.direction.leftInput ∧
      PairedStrategyMemory.processOne target.1 target.2 =
        (PairedStrategyMemory.processTwo source.1 source.2).step (A := A)
          (.fromTwo row actual.direction.leftPhysicalPast
            actual.direction.leftInput) := by
  have hselected :
      state.family.leftSelectedChild A actual.direction lineage =
        some target := by
    simpa [ProfiledRawJointOneSidedSemanticState.step, hside] using htarget
  rcases state.family.leftSelectedChild_eq_some_source A actual.direction
      lineage target hselected with
    ⟨member, row, hmember, _hpattern, htargetEq⟩
  have hmemberEq : member = source :=
    Option.some.inj (hmember.symm.trans hsource)
  subst member
  subst target
  refine ⟨row, rfl, ?_⟩
  exact (profiledRawLeftSemanticChildMemory_eq_processOne A source row
    actual.direction.leftPhysicalPast actual.direction.leftInput).symm

/-! ## Finite roots are exact profiled memories -/

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- The finite right slot carried by a semantic member is its profiled
`PairedStrategyMemory` state. -/
theorem profiledRawJointThreadRoot_of_right_member
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State) :
    (Sum.inl (((member.1.code, member.2),
        rightInitialFirstProfile member.1.lambdaOfStrategy)) :
      ProfiledRawJointThreadRoot A) =
      Sum.inl (((member.1.code, member.2),
        rightInitialFirstProfile member.1.lambdaOfStrategy)) :=
  rfl

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- The root priority of a right semantic member is exactly its stored block
minimum priority. -/
@[simp] theorem profiledRawJointThreadRootPriority_right_member
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State) :
    profiledRawJointThreadRootPriority A
        (.inl (((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy))) =
      A.priority member.2 := by
  rfl

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Left priority mirror. -/
@[simp] theorem profiledRawJointThreadRootPriority_left_member
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State) :
    profiledRawJointThreadRootPriority A
        (.inr (((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy))) =
      A.priority member.2 := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
