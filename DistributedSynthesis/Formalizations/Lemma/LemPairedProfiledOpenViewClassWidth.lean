/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenViewClassHandoff

/-!
# Successor view classes retain one indexed lineage per old member

The corrected reversal handoff first forms the full proof-side source
`I × PairedEntryRow`: every old semantic member has two possible physical
rows.  This file proves the model-specific fact that quotienting this source
by the new blind view never retains both rows of one old member.  Projection
to `I` is therefore injective on every successor view class.

In particular, a Boolean current class produces successor classes of size at
most two, even though the unquotiented source has four corners.  The member
and row are proof-side lineage coordinates only.  Neither is delivered to a
process and no strict-leader bit is assumed.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

/-- At a right-to-left reversal, the new process-two blind view determines
the physical row once the old semantic member is fixed. -/
theorem procTwoViewClassChild_row_injective
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (member : I) (left right : PairedEntryRow)
    (hview :
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input
            (member, left)).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input
            (member, right)).rightHistory) :
    left = right := by
  cases left <;> cases right
  · rfl
  · have hfour := procTwoFreshPairs_of_procOnePair_disjoint strategy
      (entry member) past input.2 input.1
    exact False.elim (hfour.2.2.1 hview)
  · have hfour := procTwoFreshPairs_of_procOnePair_disjoint strategy
      (entry member) past input.2 input.1
    exact False.elim (hfour.2.2.1 hview.symm)
  · rfl

/-- Left-to-right mirror: the new process-one view determines the row at a
fixed old semantic member. -/
theorem procOneViewClassChild_row_injective
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (member : I) (left right : PairedEntryRow)
    (hview :
      currentView Proc.one
          (procOneViewClassChild strategy entry past input
            (member, left)).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input
            (member, right)).leftHistory) :
    left = right := by
  cases left <;> cases right
  · rfl
  · have hfour := procOneFreshPairs_of_procTwoPair_disjoint strategy
      (entry member) past input.1 input.2
    exact False.elim (hfour.2.2.1 hview)
  · have hfour := procOneFreshPairs_of_procTwoPair_disjoint strategy
      (entry member) past input.1 input.2
    exact False.elim (hfour.2.2.1 hview.symm)
  · rfl

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- Projection to the old semantic member is injective on each new
process-two view class.  Thus a handoff updates lineages; it cannot reselect
two physical rows for one lineage. -/
theorem procTwoChildViewClass_fst_injOn
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : I × PairedEntryRow) :
    Set.InjOn Prod.fst
      (procTwoChildViewClass strategy entry past input pivot :
        Set (I × PairedEntryRow)) := by
  rintro ⟨leftMember, leftRow⟩ hleft ⟨rightMember, rightRow⟩ hright hfst
  simp only at hfst
  subst rightMember
  suffices leftRow = rightRow by simp [this]
  apply procTwoViewClassChild_row_injective strategy entry past input leftMember
  have hl := (mem_procTwoChildViewClass strategy entry past input pivot
    (leftMember, leftRow)).mp hleft
  have hr := (mem_procTwoChildViewClass strategy entry past input pivot
    (leftMember, rightRow)).mp hright
  exact hl.trans hr.symm

/-- Mirror injectivity on a new process-one view class. -/
theorem procOneChildViewClass_fst_injOn
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : I × PairedEntryRow) :
    Set.InjOn Prod.fst
      (procOneChildViewClass strategy entry past input pivot :
        Set (I × PairedEntryRow)) := by
  rintro ⟨leftMember, leftRow⟩ hleft ⟨rightMember, rightRow⟩ hright hfst
  simp only at hfst
  subst rightMember
  suffices leftRow = rightRow by simp [this]
  apply procOneViewClassChild_row_injective strategy entry past input leftMember
  have hl := (mem_procOneChildViewClass strategy entry past input pivot
    (leftMember, leftRow)).mp hleft
  have hr := (mem_procOneChildViewClass strategy entry past input pivot
    (leftMember, rightRow)).mp hright
  exact hl.trans hr.symm

/-- A successor process-two class is no wider than its old member index. -/
theorem procTwoChildViewClass_card_le
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : I × PairedEntryRow) :
    (procTwoChildViewClass strategy entry past input pivot).card ≤
      Fintype.card I := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro candidate _
    exact Finset.mem_univ candidate.1
  · exact procTwoChildViewClass_fst_injOn strategy entry past input pivot

/-- Mirror width bound. -/
theorem procOneChildViewClass_card_le
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : I × PairedEntryRow) :
    (procOneChildViewClass strategy entry past input pivot).card ≤
      Fintype.card I := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro candidate _
    exact Finset.mem_univ candidate.1
  · exact procOneChildViewClass_fst_injOn strategy entry past input pivot

/-- The concrete four-corner source of a Boolean family always collapses to
at most two process-two candidates. -/
theorem procTwoChildViewClass_bool_card_le_two
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : Bool × PairedEntryRow) :
    (procTwoChildViewClass strategy entry past input pivot).card ≤ 2 := by
  simpa using procTwoChildViewClass_card_le strategy entry past input pivot

/-- Boolean left-to-right mirror. -/
theorem procOneChildViewClass_bool_card_le_two
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : Bool × PairedEntryRow) :
    (procOneChildViewClass strategy entry past input pivot).card ≤ 2 := by
  simpa using procOneChildViewClass_card_le strategy entry past input pivot

end

end

end


end DetParityAutomaton

end DistributedSynthesis
