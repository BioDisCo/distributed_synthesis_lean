/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalSubsets
import DistributedSynthesis.Library.Distributed.EncodedJournalBoundaryCorrect

/-! # Exact finite-set images for the numeric journal -/
namespace DistributedSynthesis.EncodedJournalSubsets
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))
def atomEquiv : (A).State × (A).State ≃ Fin (atomCount d) := finProdFinEquiv
theorem atomEquiv_val (qm : (A).State × (A).State) : (atomEquiv d qm).val = pairedIndex d qm := rfl
def atomEncode (s : Finset ((A).State × (A).State)) := FiniteSetCodes.encode (atomEquiv d) s
def chainEncode (s : Finset (ChainThread A)) := FiniteSetCodes.encode (chainEquiv d) s

theorem inputs_complete (ij : Fin (inputOne d) × Fin (inputTwo d)) : (ij.1.val,ij.2.val) ∈ inputs d :=
  List.mem_product.mpr ⟨List.mem_range.mpr ij.1.isLt,List.mem_range.mpr ij.2.isLt⟩
theorem inputs_sound (ij : Nat × Nat) (h : ij ∈ inputs d) :
    ∃ v : Fin (inputOne d) × Fin (inputTwo d), (v.1.val,v.2.val) = ij := by
  obtain ⟨hi,hj⟩ := List.mem_product.mp h
  exact ⟨(⟨ij.1,List.mem_range.mp hi⟩,⟨ij.2,List.mem_range.mp hj⟩),rfl⟩

theorem left_step (c : EncodedJournalLabels.Code) (s : Finset ((A).State × (A).State))
    (j : Fin (inputTwo d)) :
    step ((d,false,c),atomEncode d s,j.val) = atomEncode d (leftStepSubset s (label d c).leftNarrowed j) := by
  apply FiniteSetCodes.collect_raw (atomEquiv d) (atomEquiv d) s Fin.val (List.range (inputOne d))
    (fun i => List.mem_range.mpr i.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro qm i
  exact EncodedOrdinaryThreads.left_next d (A).initial c qm i j

theorem right_step (c : EncodedJournalLabels.Code) (s : Finset ((A).State × (A).State))
    (i : Fin (inputOne d)) :
    step ((d,true,c),atomEncode d s,i.val) = atomEncode d (rightStepSubset s (label d c).rightNarrowed i) := by
  apply FiniteSetCodes.collect_raw (atomEquiv d) (atomEquiv d) s Fin.val (List.range (inputTwo d))
    (fun j => List.mem_range.mpr j.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro qm j
  exact EncodedOrdinaryThreads.right_next d (A).initial c qm j i

theorem left_close (c : EncodedJournalLabels.Code) (s : Finset ((A).State × (A).State)) (sender : Nat) :
    close ((d,false,c),atomEncode d s,sender) =
      atomEncode d (leftCloseSubset s (label d c).leftNarrowed (label d c).leftClose) := by
  apply FiniteSetCodes.collect_raw (atomEquiv d) (atomEquiv d) s
    (fun ij : Fin (inputOne d) × Fin (inputTwo d) => (ij.1.val,ij.2.val)) (inputs d)
    (inputs_complete d) (inputs_sound d)
  intro qm ij
  exact EncodedJournalBoundary.close_correct d false c qm ij.1 ij.2

theorem right_close (c : EncodedJournalLabels.Code) (s : Finset ((A).State × (A).State)) (sender : Nat) :
    close ((d,true,c),atomEncode d s,sender) =
      atomEncode d (rightCloseSubset s (label d c).rightNarrowed (label d c).rightClose) := by
  have h := FiniteSetCodes.collect_raw (atomEquiv d) (atomEquiv d) s
    (fun ij : Fin (inputOne d) × Fin (inputTwo d) => (ij.1.val,ij.2.val)) (inputs d)
    (inputs_complete d) (inputs_sound d)
    (fun q ij => EncodedJournalBoundary.close ((d,true,c),q,ij))
    (fun qm ij => rightThreadClose qm (label d c).rightNarrowed (label d c).rightClose ij.2 ij.1)
    (fun qm ij => EncodedJournalBoundary.close_correct d true c qm ij.1 ij.2)
  refine h.trans (congrArg (atomEncode d) ?_)
  apply Finset.biUnion_congr rfl
  intro qm _
  ext th
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor <;> rintro ⟨⟨i,j⟩,he⟩ <;> exact ⟨(j,i),he⟩

theorem left_reverse (c : EncodedJournalLabels.Code) (s : Finset ((A).State × (A).State))
    (i : Fin (inputOne d)) :
    reverse ((d,false,c),atomEncode d s,i.val) =
      chainEncode d (leftReverseSubset s (label d c).leftClose (label d c).leftRev i) := by
  apply FiniteSetCodes.collect_raw (atomEquiv d) (chainEquiv d) s Fin.val (List.range (inputTwo d))
    (fun j => List.mem_range.mpr j.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro qm j
  exact EncodedJournalBoundary.reverse_correct d false c qm i j

theorem right_reverse (c : EncodedJournalLabels.Code) (s : Finset ((A).State × (A).State))
    (j : Fin (inputTwo d)) :
    reverse ((d,true,c),atomEncode d s,j.val) =
      chainEncode d (rightReverseSubset s (label d c).rightClose (label d c).rightRev j) := by
  apply FiniteSetCodes.collect_raw (atomEquiv d) (chainEquiv d) s Fin.val (List.range (inputOne d))
    (fun i => List.mem_range.mpr i.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro qm i
  exact EncodedJournalBoundary.reverse_correct d true c qm i j

theorem revLeft_close (c : EncodedJournalLabels.Code) (s : Finset (ChainThread A)) (sender : Nat) :
    chainClose ((d,true,c),chainEncode d s,sender) = atomEncode d (revLeftCloseSubset s (label d c).revLeft) := by
  apply FiniteSetCodes.collect_raw (chainEquiv d) (atomEquiv d) s
    (fun ij : Fin (inputOne d) × Fin (inputTwo d) => (ij.1.val,ij.2.val)) (inputs d)
    (inputs_complete d) (inputs_sound d)
  intro th ij
  exact EncodedJournalBoundary.chainClose_correct d true c th ij.1 ij.2

theorem revRight_close (c : EncodedJournalLabels.Code) (s : Finset (ChainThread A)) (sender : Nat) :
    chainClose ((d,false,c),chainEncode d s,sender) = atomEncode d (revRightCloseSubset s (label d c).revRight) := by
  apply FiniteSetCodes.collect_raw (chainEquiv d) (atomEquiv d) s
    (fun ij : Fin (inputOne d) × Fin (inputTwo d) => (ij.1.val,ij.2.val)) (inputs d)
    (inputs_complete d) (inputs_sound d)
  intro th ij
  exact EncodedJournalBoundary.chainClose_correct d false c th ij.1 ij.2

theorem left_open (c : EncodedJournalLabels.Code) (qm : (A).State × (A).State)
    (j : Fin (inputTwo d)) : openBlock ((d,false,c),pairedIndex d qm,j.val) =
      atomEncode d (leftOpenSubset qm (label d c).leftNarrowed j) := by
  have h := left_step d c {(qm.1,qm.1)} j
  simp only [atomEncode,FiniteSetCodes.encode_singleton,atomEquiv_val,leftStepSubset,
    Finset.singleton_biUnion] at h
  unfold openBlock
  dsimp only
  rw [pairedIndex_div]
  exact h

theorem right_open (c : EncodedJournalLabels.Code) (qm : (A).State × (A).State)
    (i : Fin (inputOne d)) : openBlock ((d,true,c),pairedIndex d qm,i.val) =
      atomEncode d (rightOpenSubset qm (label d c).rightNarrowed i) := by
  have h := right_step d c {(qm.1,qm.1)} i
  simp only [atomEncode,FiniteSetCodes.encode_singleton,atomEquiv_val,rightStepSubset,
    Finset.singleton_biUnion] at h
  unfold openBlock
  dsimp only
  rw [pairedIndex_div]
  exact h

theorem both_correct (side : Bool) (c : EncodedJournalLabels.Code) (qm : (A).State × (A).State) :
    both ((d,side,c),pairedIndex d qm) =
      atomEncode d (bothAtomSubset qm (label d c).leftNarrowed (label d c).rightNarrowed) := by
  have h := FiniteSetCodes.collect_raw (atomEquiv d) (atomEquiv d) {qm}
    (fun ij : Fin (inputOne d) × Fin (inputTwo d) => (ij.1.val,ij.2.val)) (inputs d)
    (inputs_complete d) (inputs_sound d)
    (fun q ij => EncodedJournalBoundary.both ((d,side,c),q,ij))
    (fun q ij => bothThreadAtom q (label d c).leftNarrowed (label d c).rightNarrowed ij.1 ij.2)
    (fun q ij => EncodedJournalBoundary.both_correct d side c q ij.1 ij.2)
  simpa only [FiniteSetCodes.encode_singleton,atomEquiv_val,Finset.singleton_biUnion] using h

theorem revLeft_step (c : EncodedJournalLabels.Code) (s : Finset (ChainThread A))
    (j : Fin (inputTwo d)) : chainStep ((d,true,false,c),chainEncode d s,j.val) =
      chainEncode d (revLeftStepSubset s (label d c).revLeft j) := by
  apply FiniteSetCodes.collect_raw (chainEquiv d) (chainEquiv d) s Fin.val (List.range (inputOne d))
    (fun i => List.mem_range.mpr i.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro th i
  exact EncodedChainThreads.next_correct d c true false th i j

theorem revRight_step (c : EncodedJournalLabels.Code) (s : Finset (ChainThread A))
    (i : Fin (inputOne d)) : chainStep ((d,false,true,c),chainEncode d s,i.val) =
      chainEncode d (revRightStepSubset s (label d c).revRight i) := by
  apply FiniteSetCodes.collect_raw (chainEquiv d) (chainEquiv d) s Fin.val (List.range (inputTwo d))
    (fun j => List.mem_range.mpr j.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro th j
  exact EncodedChainThreads.next_correct d c false true th i j

theorem revLeft_reverse (c : EncodedJournalLabels.Code) (s : Finset (ChainThread A))
    (i : Fin (inputOne d)) : chainStep ((d,true,true,c),chainEncode d s,i.val) =
      chainEncode d (revLeftReverseSubset s (label d c).revLeft i) := by
  apply FiniteSetCodes.collect_raw (chainEquiv d) (chainEquiv d) s Fin.val (List.range (inputTwo d))
    (fun j => List.mem_range.mpr j.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro th j
  exact EncodedChainThreads.next_correct d c true true th i j

theorem revRight_reverse (c : EncodedJournalLabels.Code) (s : Finset (ChainThread A))
    (j : Fin (inputTwo d)) : chainStep ((d,false,false,c),chainEncode d s,j.val) =
      chainEncode d (revRightReverseSubset s (label d c).revRight j) := by
  apply FiniteSetCodes.collect_raw (chainEquiv d) (chainEquiv d) s Fin.val (List.range (inputOne d))
    (fun i => List.mem_range.mpr i.isLt) (fun v hv => ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩)
  intro th i
  exact EncodedChainThreads.next_correct d c false false th i j
end DistributedSynthesis.EncodedJournalSubsets
