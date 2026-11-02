/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedOrdinaryThreads

/-! # Exact left/right thread correspondence for numeric parity objectives -/
namespace DistributedSynthesis.EncodedOrdinaryThreads
open EncodedNoDirect EncodedRoundObjectives DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d

local instance (b : (A).State) : DecidableEq ((A).leftBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (Fin (stateCount d) × Fin (stateCount d)))
local instance (b : (A).State) : DecidableEq ((A).rightBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (Fin (stateCount d) × Fin (stateCount d)))

def stateNumber : (A).State ≃ Fin (Fintype.card (A).State) :=
  finCongr (Fintype.card_fin (stateCount d)).symm
theorem stateNumber_val (q : (A).State) : (stateNumber d q).val = q.val := rfl
theorem stateCount_card : Fintype.card (A).State = stateCount d := Fintype.card_fin _
theorem stateCount_pos : 0 < stateCount d := Nat.succ_pos _

def pairedIndex (qm : (A).State × (A).State) : Nat := qm.2.val + stateCount d * qm.1.val
theorem pairedIndex_lt (qm : (A).State × (A).State) : pairedIndex d qm < stateCount d * stateCount d :=
  (finProdFinEquiv qm).isLt
theorem pairedIndex_div (qm : (A).State × (A).State) : pairedIndex d qm / stateCount d = qm.1.val := by
  simp [pairedIndex, Nat.add_mul_div_left _ _ (stateCount_pos d), Nat.div_eq_of_lt qm.2.isLt]
theorem pairedIndex_mod (qm : (A).State × (A).State) : pairedIndex d qm % stateCount d = qm.2.val := by
  simp [pairedIndex, Nat.mod_eq_of_lt qm.2.isLt]

theorem objectivePriority_correct (q : (A).State) : objectivePriority d q.val = (A).priority q := rfl
theorem objectiveStep_correct (q : (A).State) (a : Letter d) :
    objectiveStep d q.val (letterCode a) = ((A).step q a).val := rfl

def label (c : EncodedJournalLabels.Code) : GlobalJournalLabel A :=
  EncodedJournalLabels.decode A (stateNumber d) c

theorem left_roundCode (c : EncodedJournalLabels.Code) (qm : (A).State × (A).State)
    (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    roundCode ((d, false, c), pairedIndex d qm, i.val, j.val) =
      letterCode (leftRoundRecord (i,j) ((label d c).leftNarrowed.2 qm (i,j)) ((label d c).leftNarrowed.1 j)) := by
  have hs := EncodedJournalLabels.left_sender A (stateNumber d) c j
  have hr := EncodedJournalLabels.left_receiver A (stateNumber d) c qm.1 qm.2 i j
  simp only [stateNumber_val, stateCount_card] at hr
  change (_, _, _, _, _) = (_, _, _, _, _)
  simp only [roundCode, Bool.false_eq_true, Bool.cond_false]
  refine Prod.ext ?_ ?_
  · rfl
  refine Prod.ext ?_ ?_
  · rfl
  refine Prod.ext ?_ ?_
  · rfl
  apply Prod.ext
  · exact hr.symm
  · exact hs.symm

theorem right_roundCode (c : EncodedJournalLabels.Code) (qm : (A).State × (A).State)
    (j : Fin (inputTwo d)) (i : Fin (inputOne d)) :
    roundCode ((d, true, c), pairedIndex d qm, j.val, i.val) =
      letterCode (rightRoundRecord (j,i) ((label d c).rightNarrowed.1 i) ((label d c).rightNarrowed.2 qm (j,i))) := by
  have hs := EncodedJournalLabels.right_sender A (stateNumber d) c i
  have hr := EncodedJournalLabels.right_receiver A (stateNumber d) c qm.1 qm.2 j i
  simp only [stateNumber_val, stateCount_card] at hr
  change (_, _, _, _, _) = (_, _, _, _, _)
  simp only [roundCode, Bool.cond_true]
  refine Prod.ext ?_ ?_
  · rfl
  refine Prod.ext ?_ ?_
  · rfl
  refine Prod.ext ?_ ?_
  · rfl
  exact Prod.ext hs.symm hr.symm

theorem left_next (boundary : (A).State) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (i : Fin (inputOne d)) (j : Fin (inputTwo d)) :
    next ((d, false, c), pairedIndex d qm, i.val, j.val) =
      pairedIndex d (((A).leftBlockMonitor boundary).step qm
        (narrowedRecord ((A).leftBlockMonitor boundary) (label d c).leftNarrowed qm (i,j))) := by
  have hq : nextObjective ((d, false, c), pairedIndex d qm, i.val, j.val) =
      ((A).step qm.1 (leftRoundRecord (i,j) ((label d c).leftNarrowed.2 qm (i,j))
        ((label d c).leftNarrowed.1 j))).val := by
    unfold nextObjective
    rw [pairedIndex_div, left_roundCode, objectiveStep_correct]
  simp only [next, hq, pairedIndex_mod, objectivePriority_correct]
  dsimp only [pairedIndex, leftBlockMonitor, narrowedRecord, realizedRoundRecord, leftRoundRecord]
  split_ifs <;> rfl

theorem right_next (boundary : (A).State) (c : EncodedJournalLabels.Code)
    (qm : (A).State × (A).State) (j : Fin (inputTwo d)) (i : Fin (inputOne d)) :
    next ((d, true, c), pairedIndex d qm, j.val, i.val) =
      pairedIndex d (((A).rightBlockMonitor boundary).step qm
        (narrowedRecord ((A).rightBlockMonitor boundary) (label d c).rightNarrowed qm (j,i))) := by
  have hq : nextObjective ((d, true, c), pairedIndex d qm, j.val, i.val) =
      ((A).step qm.1 (rightRoundRecord (j,i) ((label d c).rightNarrowed.1 i)
        ((label d c).rightNarrowed.2 qm (j,i)))).val := by
    unfold nextObjective
    rw [pairedIndex_div, right_roundCode, objectiveStep_correct]
  simp only [next, hq, pairedIndex_mod, objectivePriority_correct]
  dsimp only [pairedIndex, rightBlockMonitor, narrowedRecord, realizedRoundRecordRight, rightRoundRecord]
  split_ifs <;> rfl

theorem mem_edges (x : Context) (q t sender : Nat) :
    (q,t) ∈ edges x sender ↔ q < stateCount x.1 * stateCount x.1 ∧
      ∃ i < receiverCount x, next (x,q,i,sender) = t := by
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨q', hq, i, hi, rfl, he⟩
    exact ⟨hq, i, hi, he⟩
  · rintro ⟨hq, i, hi, he⟩
    exact ⟨q, hq, i, hi, rfl, he⟩

theorem left_edges (boundary : (A).State) (c : EncodedJournalLabels.Code)
    (qm target : (A).State × (A).State) (j : Fin (inputTwo d)) :
    (pairedIndex d qm, pairedIndex d target) ∈ edges (d,false,c) j.val ↔
      ∃ i : Fin (inputOne d), target = ((A).leftBlockMonitor boundary).step qm
        (narrowedRecord ((A).leftBlockMonitor boundary) (label d c).leftNarrowed qm (i,j)) := by
  rw [mem_edges, and_iff_right (pairedIndex_lt d qm)]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [left_next d boundary c qm ⟨i,hi⟩ j] at he
    exact ⟨⟨i,hi⟩, finProdFinEquiv.injective (Fin.ext he.symm)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, left_next d boundary c qm i j⟩

theorem right_edges (boundary : (A).State) (c : EncodedJournalLabels.Code)
    (qm target : (A).State × (A).State) (i : Fin (inputOne d)) :
    (pairedIndex d qm, pairedIndex d target) ∈ edges (d,true,c) i.val ↔
      ∃ j : Fin (inputTwo d), target = ((A).rightBlockMonitor boundary).step qm
        (narrowedRecord ((A).rightBlockMonitor boundary) (label d c).rightNarrowed qm (j,i)) := by
  rw [mem_edges, and_iff_right (pairedIndex_lt d qm)]
  constructor
  · rintro ⟨j, hj, he⟩
    rw [right_next d boundary c qm ⟨j,hj⟩ i] at he
    exact ⟨⟨j,hj⟩, finProdFinEquiv.injective (Fin.ext he.symm)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, j.isLt, right_next d boundary c qm j i⟩

def pairNumber : ((A).State × (A).State) ≃ Fin (Fintype.card ((A).State × (A).State)) :=
  finProdFinEquiv.trans (finCongr (by simp only [Fintype.card_prod, stateCount_card]))

theorem pairNumber_val (qm : (A).State × (A).State) :
    (pairNumber d qm).val = pairedIndex d qm := rfl

theorem priorities_getD (qm : (A).State × (A).State) :
    (priorities d).getD (pairedIndex d qm) 0 = (A).priority qm.1 := by
  have h : pairedIndex d qm < (priorities d).length := by
    simpa only [priorities, List.length_map, List.length_range] using pairedIndex_lt d qm
  rw [List.getD_eq_getElem _ _ h]
  simp only [priorities, List.getElem_map, List.getElem_range, pairedIndex_div,
    objectivePriority_correct]

theorem mem_priorities (p : Nat) : p ∈ priorities d ↔ ∃ q : (A).State, (A).priority q = p := by
  simp only [priorities, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨q, hq, hp⟩
    exact ⟨⟨q / stateCount d, (Nat.div_lt_iff_lt_mul (stateCount_pos d)).mpr hq⟩, hp⟩
  · rintro ⟨q, rfl⟩
    refine ⟨pairedIndex d (q,q), pairedIndex_lt d (q,q), ?_⟩
    rw [pairedIndex_div, objectivePriority_correct]

theorem left_priorities (boundary : (A).State) (p : Nat) :
    p ∈ priorities d ↔ p ∈ ThreadComputable.priorityRange ((A).leftBlockMonitor boundary) := by
  rw [mem_priorities]
  simp only [ThreadComputable.priorityRange, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩; exact ⟨(q,q), hq⟩
  · rintro ⟨qm, hq⟩; exact ⟨qm.1, hq⟩

theorem right_priorities (boundary : (A).State) (p : Nat) :
    p ∈ priorities d ↔ p ∈ ThreadComputable.priorityRange ((A).rightBlockMonitor boundary) := by
  rw [mem_priorities]
  simp only [ThreadComputable.priorityRange, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩; exact ⟨(q,q), hq⟩
  · rintro ⟨qm, hq⟩; exact ⟨qm.1, hq⟩

set_option maxHeartbeats 800000 in
theorem left_badThread_step (boundary : (A).State) (c : EncodedJournalLabels.Code)
    (j : Fin (inputTwo d))
    (s t : ThreadComputable.GuessState ((A).leftBlockMonitor boundary)) :
    EncodedThreadBuchi.step ((priorities d, edges (d,false,c) j.val),
      EncodedThreadBuchi.encode _ (pairNumber d) s, EncodedThreadBuchi.encode _ (pairNumber d) t) ↔
      (ThreadComputable.buchi ((A).leftBlockMonitor boundary)).step s ((label d c).leftNarrowed, j) t :=
  EncodedThreadBuchi.step_correct ((A).leftBlockMonitor boundary) (pairNumber d) (priorities d)
    (priorities_getD d) (left_priorities d boundary) (edges (d,false,c) j.val)
    ((label d c).leftNarrowed,j) (left_edges d boundary c · · j) s t

set_option maxHeartbeats 800000 in
theorem right_badThread_step (boundary : (A).State) (c : EncodedJournalLabels.Code)
    (i : Fin (inputOne d))
    (s t : ThreadComputable.GuessState ((A).rightBlockMonitor boundary)) :
    EncodedThreadBuchi.step ((priorities d, edges (d,true,c) i.val),
      EncodedThreadBuchi.encode _ (pairNumber d) s, EncodedThreadBuchi.encode _ (pairNumber d) t) ↔
      (ThreadComputable.buchi ((A).rightBlockMonitor boundary)).step s ((label d c).rightNarrowed, i) t :=
  EncodedThreadBuchi.step_correct ((A).rightBlockMonitor boundary) (pairNumber d) (priorities d)
    (priorities_getD d) (right_priorities d boundary) (edges (d,true,c) i.val)
    ((label d c).rightNarrowed,i) (right_edges d boundary c · · i) s t

theorem left_badThread_accepting (boundary : (A).State)
    (s : ThreadComputable.GuessState ((A).leftBlockMonitor boundary)) :
    EncodedThreadBuchi.accepting (priorities d) (EncodedThreadBuchi.encode _ (pairNumber d) s) ↔
      (ThreadComputable.buchi ((A).leftBlockMonitor boundary)).accepting s :=
  EncodedThreadBuchi.accepting_correct _ (pairNumber d) (priorities d)
    (priorities_getD d) (left_priorities d boundary) s

theorem right_badThread_accepting (boundary : (A).State)
    (s : ThreadComputable.GuessState ((A).rightBlockMonitor boundary)) :
    EncodedThreadBuchi.accepting (priorities d) (EncodedThreadBuchi.encode _ (pairNumber d) s) ↔
      (ThreadComputable.buchi ((A).rightBlockMonitor boundary)).accepting s :=
  EncodedThreadBuchi.accepting_correct _ (pairNumber d) (priorities d)
    (priorities_getD d) (right_priorities d boundary) s

theorem left_badThread_initial (boundary : (A).State) :
    EncodedThreadBuchi.encode _ (pairNumber d)
      (ThreadComputable.buchi ((A).leftBlockMonitor boundary)).initial =
        (initial d boundary.val, none) := rfl

theorem right_badThread_initial (boundary : (A).State) :
    EncodedThreadBuchi.encode _ (pairNumber d)
      (ThreadComputable.buchi ((A).rightBlockMonitor boundary)).initial =
        (initial d boundary.val, none) := rfl

end DistributedSynthesis.EncodedOrdinaryThreads
