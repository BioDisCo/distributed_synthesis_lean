/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedMemoryBridge

/-!
# Recovering semantic members from live one-sided slots

The code-only parity monitor follows a finite side/lineage/root.  For the
semantic parity proof a live current root must be inverted to the literal
strategy member erased into that slot.  This file provides the two typed
inversions and identifies the recovered slot with the corresponding
`PairedStrategyMemory` state.

It also records the small side fact used by a never-dead lineage: a live slot
on the opposite side of a one-sided successor forces Nature's actual side to
match the current hidden side.  These are proof-side eliminations only; no
side or leader is exposed to a process.
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

/-! ## Embedding a finite thread root back into the profiled memory state -/

/-- The two thread-root summands are exactly the two live summands of
`PairedProfiledTreeState`. -/
def profiledRawJointThreadRootTreeState :
    ProfiledRawJointThreadRoot A → PairedProfiledTreeState A
  | .inl root => .inr (.inl root)
  | .inr root => .inr (.inr root)

/-! ## Typed current-slot inversion -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- A live right-side finite slot comes from one literal process-one semantic
member at the same lineage. -/
theorem ProfiledRawJointOneSidedSemanticState.exists_right_member_of_currentSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (lineage : I) (root : ProfiledRawJointThreadRoot A)
    (hslot : profiledRawJointOneSidedCurrentSlots A .right (state.code A)
      lineage = some root) :
    ∃ member : ProcOnePairedEntryRep strategy × A.State,
      state.family.right lineage = some member ∧
      root = .inl (profiledRawRightSlotOfSemanticPair A member) ∧
      PairedStrategyMemory.toProfiledTreeState (A := A)
          (.processOne member.1 member.2) =
        profiledRawJointThreadRootTreeState A root := by
  cases hmember : state.family.right lineage with
  | none =>
      simp [profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code, hmember] at hslot
  | some member =>
      have hroot :
          root = .inl (profiledRawRightSlotOfSemanticPair A member) := by
        simpa [profiledRawJointOneSidedCurrentSlots,
          ProfiledRawJointOneSidedSemanticState.code,
          ProfiledRawJointSemanticFamily.incidenceCode,
          ProfiledRawJointSemanticFamily.code, hmember] using hslot.symm
      refine ⟨member, rfl, hroot, ?_⟩
      subst root
      rfl

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Left-side mirror. -/
theorem ProfiledRawJointOneSidedSemanticState.exists_left_member_of_currentSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (lineage : I) (root : ProfiledRawJointThreadRoot A)
    (hslot : profiledRawJointOneSidedCurrentSlots A .left (state.code A)
      lineage = some root) :
    ∃ member : ProcTwoPairedEntryRep strategy × A.State,
      state.family.left lineage = some member ∧
      root = .inr (profiledRawLeftSlotOfSemanticPair A member) ∧
      PairedStrategyMemory.toProfiledTreeState (A := A)
          (.processTwo member.1 member.2) =
        profiledRawJointThreadRootTreeState A root := by
  cases hmember : state.family.left lineage with
  | none =>
      simp [profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code, hmember] at hslot
  | some member =>
      have hroot :
          root = .inr (profiledRawLeftSlotOfSemanticPair A member) := by
        simpa [profiledRawJointOneSidedCurrentSlots,
          ProfiledRawJointOneSidedSemanticState.code,
          ProfiledRawJointSemanticFamily.incidenceCode,
          ProfiledRawJointSemanticFamily.code, hmember] using hslot.symm
      refine ⟨member, rfl, hroot, ?_⟩
      subst root
      rfl

/-! ## Live successors force the matching physical side -/

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- If the one-sided successor has a live slot on `side.other`, the actual
block side was `side`. -/
theorem profiledRawJoint_actualSide_eq_of_next_currentSlot
    (side : IndexedLineageSide)
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (root : ProfiledRawJointThreadRoot A)
    (hslot : profiledRawJointOneSidedCurrentSlots A side.other
      (profiledRawJointOneSidedNext A code move actual) lineage = some root) :
    actual.side = side := by
  cases side <;> cases hactual : actual.side
  · rfl
  · simp [profiledRawJointOneSidedNext,
      profiledRawJointOneSidedCurrentSlots,
      profiledRawJointLeftActualIncidenceNext,
      profiledRawJointLeftActualFamilyNext, IndexedLineageSide.other,
      hactual] at hslot
  · simp [profiledRawJointOneSidedNext,
      profiledRawJointOneSidedCurrentSlots,
      profiledRawJointRightActualIncidenceNext,
      profiledRawJointRightActualFamilyNext, IndexedLineageSide.other,
      hactual] at hslot
  · rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Equivalent side recovery directly from a live hidden child code. -/
theorem profiledRawJoint_actualSide_eq_of_childCode
    (side : IndexedLineageSide)
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (row : PairedEntryRow)
    (root : ProfiledRawJointThreadRoot A)
    (hchild : profiledRawJointOneSidedChildCode A side code move actual
      lineage = some (row, root)) :
    actual.side = side := by
  cases side <;> cases hactual : actual.side
  · rfl
  · simp [profiledRawJointOneSidedChildCode, hactual] at hchild
  · simp [profiledRawJointOneSidedChildCode, hactual] at hchild
  · rfl

end

end DetParityAutomaton

end DistributedSynthesis
