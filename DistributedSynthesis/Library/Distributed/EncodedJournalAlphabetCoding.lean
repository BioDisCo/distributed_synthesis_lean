/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalTransitionsCorrect

/-! # Label and branch coverage for the numeric journal tables -/
namespace DistributedSynthesis.EncodedJournalAlphabetCoding
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedJournalStateCoding EncodedJournalSubsets
  EncodedJournalTransitionsCorrect DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))

def labelCode (l : GlobalJournalLabel A) := EncodedJournalLabels.encode A (stateNumber d) l
theorem label_mem (l : GlobalJournalLabel A) : labelCode d l ∈ EncodedJournalTables.labels d := by
  unfold EncodedJournalTables.labels
  simpa only [stateCount_card] using EncodedJournalLabels.encode_mem A (stateNumber d) l
@[irreducible] def labelAt (l : Fin (EncodedJournalTables.labels d).length) :=
  EncodedOrdinaryThreads.label d (EncodedJournalTables.labels d)[l.val]
def labelNumber (l : GlobalJournalLabel A) : Fin (EncodedJournalTables.labels d).length :=
  ⟨(EncodedJournalTables.labels d).idxOf (labelCode d l),List.idxOf_lt_length_iff.mpr (label_mem d l)⟩
theorem labelAt_number (l : GlobalJournalLabel A) : labelAt d (labelNumber d l) = l := by
  unfold labelAt labelNumber
  rw [List.getElem_idxOf]
  exact EncodedJournalLabels.decode_encode A (stateNumber d) l
theorem labelAt_surjective : Function.Surjective (labelAt d) := fun l => ⟨labelNumber d l,labelAt_number d l⟩

def branchDecode (b : EncodedJournalTransitions.Branch) : GlobalJournalBranch A :=
  if b.1 = 0 then Sum.inl ((atomEquiv d).symm (bounded _ (atomCount_pos d) b.2))
  else if b.1 = 1 then Sum.inr (Sum.inl (bounded _ (Nat.succ_pos _) b.2))
  else Sum.inr (Sum.inr (bounded _ (Nat.succ_pos _) b.2))
theorem branchDecode_code (b : GlobalJournalBranch A) : branchDecode d (branchCode d b) = b := by
  rcases b with a | j | i
  · change Sum.inl ((atomEquiv d).symm (bounded _ _ (atomEquiv d a).val)) = (Sum.inl a : GlobalJournalBranch A)
    rw [bounded_val,Equiv.symm_apply_apply]
  · change Sum.inr (Sum.inl (bounded _ _ j.val)) = (Sum.inr (Sum.inl j) : GlobalJournalBranch A)
    rw [bounded_val]
  · change Sum.inr (Sum.inr (bounded _ _ i.val)) = (Sum.inr (Sum.inr i) : GlobalJournalBranch A)
    rw [bounded_val]
theorem branch_mem (b : GlobalJournalBranch A) : branchCode d b ∈ EncodedJournalTables.branches d := by
  rcases b with a | j | i
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
      ⟨pairedIndex d a,List.mem_range.mpr (pairedIndex_lt d a),rfl⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩))
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩)
theorem branches_sound (b : EncodedJournalTransitions.Branch) (h : b ∈ EncodedJournalTables.branches d) :
    ∃ s : GlobalJournalBranch A, branchCode d s = b := by
  simp only [EncodedJournalTables.branches,List.mem_append,List.mem_map] at h
  rcases h with (h | h) | h
  · obtain ⟨q,hq,rfl⟩ := h
    refine ⟨Sum.inl ((atomEquiv d).symm ⟨q,List.mem_range.mp hq⟩),?_⟩
    simp only [branchCode,← atomEquiv_val,Equiv.apply_symm_apply]
  · obtain ⟨j,hj,rfl⟩ := h
    exact ⟨Sum.inr (Sum.inl ⟨j,List.mem_range.mp hj⟩),rfl⟩
  · obtain ⟨i,hi,rfl⟩ := h
    exact ⟨Sum.inr (Sum.inr ⟨i,List.mem_range.mp hi⟩),rfl⟩
@[irreducible] def branchAt (b : Fin (EncodedJournalTables.branches d).length) :=
  branchDecode d (EncodedJournalTables.branches d)[b.val]
def branchNumber (b : GlobalJournalBranch A) : Fin (EncodedJournalTables.branches d).length :=
  ⟨(EncodedJournalTables.branches d).idxOf (branchCode d b),List.idxOf_lt_length_iff.mpr (branch_mem d b)⟩
theorem branchAt_number (b : GlobalJournalBranch A) : branchAt d (branchNumber d b) = b := by
  unfold branchAt branchNumber
  rw [List.getElem_idxOf,branchDecode_code]
theorem branchAt_surjective : Function.Surjective (branchAt d) := fun b => ⟨branchNumber d b,branchAt_number d b⟩
theorem code_branchAt (b : Fin (EncodedJournalTables.branches d).length) :
    branchCode d (branchAt d b) = (EncodedJournalTables.branches d)[b.val] := by
  obtain ⟨s,hs⟩ := branches_sound d _ (List.getElem_mem b.isLt)
  unfold branchAt
  rw [← hs,branchDecode_code]
end DistributedSynthesis.EncodedJournalAlphabetCoding
