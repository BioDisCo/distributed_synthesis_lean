/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityProduct
import DistributedSynthesis.Library.Automata.SequenceParity

/-! Run-by-run correctness of the synchronous numeric product. Letter maps
are explicit, including when the two automata use different graph codes. -/
namespace Characterisation.EncodedParityProduct
open DistributedSynthesis

variable (d : Data)

theorem count_pos : 0 < count d := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
theorem size_transition : EncodedParityTables.size (transition d) = count d :=
  Nat.sub_add_cancel (count_pos d)
theorem alphabet_transition : (EncodedParityTables.rows (transition d)).length = (letters d).length := by
  simp [transition,EncodedParityTables.rows]

theorem join_lt {l r : Nat} (hl : l < EncodedParityTables.size (left d))
    (hr : r < EncodedParityTables.size (right d)) : join d l r < count d := by
  unfold join count
  calc
    r + EncodedParityTables.size (right d) * l <
        EncodedParityTables.size (right d) + EncodedParityTables.size (right d) * l := Nat.add_lt_add_right hr _
    _ = EncodedParityTables.size (right d) * (l+1) := by ring
    _ ≤ EncodedParityTables.size (right d) * EncodedParityTables.size (left d) := Nat.mul_le_mul_left _ hl
    _ = _ := Nat.mul_comm _ _

theorem leftState_join {l r : Nat} (hr : r < EncodedParityTables.size (right d)) :
    leftState d (join d l r) = l := by
  unfold leftState join
  rw [Nat.add_mul_div_left _ _ (show 0 < EncodedParityTables.size (right d) from Nat.succ_pos _),Nat.div_eq_of_lt hr,Nat.zero_add]
theorem rightState_join {l r : Nat} (hr : r < EncodedParityTables.size (right d)) :
    rightState d (join d l r) = r := by
  unfold rightState join
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
theorem first_lt : first d < count d := join_lt d (Nat.mod_lt _ (Nat.succ_pos _)) (Nat.mod_lt _ (Nat.succ_pos _))
theorem step_lt (q a : Nat) : step d q a < count d :=
  join_lt d (Nat.mod_lt _ (Nat.succ_pos _)) (Nat.mod_lt _ (Nat.succ_pos _))

theorem transition_next (q a : Nat) (hq : q < count d) (ha : a < (letters d).length) :
    EncodedParityTables.next (transition d) q a = step d q a := by
  have row : ((List.range (letters d).length).map
      (fun a => (List.range (count d)).map (fun q => step d q a))).getD a [] =
      (List.range (count d)).map (fun q => step d q a) := by
    rw [List.getD_eq_getElem _ _ (by simpa using ha)]
    simp only [List.getElem_map,List.getElem_range]
  unfold EncodedParityTables.next
  rw [size_transition]
  change (((List.range (letters d).length).map
    (fun a => (List.range (count d)).map (fun q => step d q a))).getD a []).getD q 0 % count d = _
  rw [row,List.getD_eq_getElem _ _ (by simpa using hq)]
  simp only [List.getElem_map,List.getElem_range]
  exact Nat.mod_eq_of_lt (step_lt d q a)

theorem leftPriorities_get (q : Nat) (hq : q < count d) :
    (leftPriorities d).getD q 0 = EncodedParityTables.priority (left d) (leftState d q) := by
  unfold leftPriorities
  rw [List.getD_eq_getElem _ _ (by simpa using hq)]
  simp only [List.getElem_map,List.getElem_range]
theorem rightPriorities_get (q : Nat) (hq : q < count d) :
    (rightPriorities d).getD q 0 = EncodedParityTables.priority (right d) (rightState d q) := by
  unfold rightPriorities
  rw [List.getD_eq_getElem _ _ (by simpa using hq)]
  simp only [List.getElem_map,List.getElem_range]

abbrev Alphabet := Fin (EncodedParityTables.rows (transition d)).length
/-- Priority profiles do not affect the underlying product run. -/
def test (d : Data) (ps : List Nat) := EncodedParityFamilies.condition (transition d,[],[]) ps

variable (leftLetter : Alphabet d → Fin (EncodedParityTables.rows (left d)).length)
variable (rightLetter : Alphabet d → Fin (EncodedParityTables.rows (right d)).length)
variable (hl : ∀ a, (letter d a.val).1 = (leftLetter a).val)
variable (hr : ∀ a, (letter d a.val).2 = (rightLetter a).val)

include hl hr in
theorem run_join (ps : List Nat) (word : OmegaWord (Alphabet d)) (t : Nat) :
    ((test d ps).run word t).val = join d
      (((EncodedParityTables.automaton (left d)).run (fun n => leftLetter (word n)) t).val)
      (((EncodedParityTables.automaton (right d)).run (fun n => rightLetter (word n)) t).val) := by
  induction t with
  | zero =>
    change first d % EncodedParityTables.size (transition d) = first d
    rw [size_transition,Nat.mod_eq_of_lt (first_lt d)]
  | succ t ih =>
    change EncodedParityTables.next (transition d) ((test d ps).run word t).val (word t).val = _
    rw [transition_next d _ _ (by have h := ((test d ps).run word t).isLt; simpa only [size_transition] using h)
      (by have h := (word t).isLt; simpa only [alphabet_transition] using h),step,ih,
      leftState_join d (by exact ((EncodedParityTables.automaton (right d)).run (fun n => rightLetter (word n)) t).isLt),
      rightState_join d (by exact ((EncodedParityTables.automaton (right d)).run (fun n => rightLetter (word n)) t).isLt),hl,hr]
    rfl

include hl hr in
theorem left_priority_run (word : OmegaWord (Alphabet d)) (t : Nat) :
    (test d (leftPriorities d)).priority ((test d (leftPriorities d)).run word t) =
      (EncodedParityTables.automaton (left d)).priority
        ((EncodedParityTables.automaton (left d)).run (fun n => leftLetter (word n)) t) := by
  change (leftPriorities d).getD _ 0 = _
  rw [leftPriorities_get d _ (by have h := ((test d (leftPriorities d)).run word t).isLt; simpa only [size_transition] using h),
    run_join d leftLetter rightLetter hl hr,leftState_join d
      (by exact ((EncodedParityTables.automaton (right d)).run (fun n => rightLetter (word n)) t).isLt)]
  rfl

include hl hr in
theorem right_priority_run (word : OmegaWord (Alphabet d)) (t : Nat) :
    (test d (rightPriorities d)).priority ((test d (rightPriorities d)).run word t) =
      (EncodedParityTables.automaton (right d)).priority
        ((EncodedParityTables.automaton (right d)).run (fun n => rightLetter (word n)) t) := by
  change (rightPriorities d).getD _ 0 = _
  rw [rightPriorities_get d _ (by have h := ((test d (rightPriorities d)).run word t).isLt; simpa only [size_transition] using h),
    run_join d leftLetter rightLetter hl hr,rightState_join d
      (by exact ((EncodedParityTables.automaton (right d)).run (fun n => rightLetter (word n)) t).isLt)]
  rfl

include hl hr in
theorem left_accepts_iff (word : OmegaWord (Alphabet d)) :
    (test d (leftPriorities d)).Accepts word ↔
      (EncodedParityTables.automaton (left d)).Accepts (fun n => leftLetter (word n)) := by
  change NatSeqMinEvenParity (fun t => (test d (leftPriorities d)).priority
      ((test d (leftPriorities d)).run word t)) ↔
    NatSeqMinEvenParity (fun t => (EncodedParityTables.automaton (left d)).priority
      ((EncodedParityTables.automaton (left d)).run (fun n => leftLetter (word n)) t))
  simp only [left_priority_run d leftLetter rightLetter hl hr]

include hl hr in
theorem right_accepts_iff (word : OmegaWord (Alphabet d)) :
    (test d (rightPriorities d)).Accepts word ↔
      (EncodedParityTables.automaton (right d)).Accepts (fun n => rightLetter (word n)) := by
  change NatSeqMinEvenParity (fun t => (test d (rightPriorities d)).priority
      ((test d (rightPriorities d)).run word t)) ↔
    NatSeqMinEvenParity (fun t => (EncodedParityTables.automaton (right d)).priority
      ((EncodedParityTables.automaton (right d)).run (fun n => rightLetter (word n)) t))
  simp only [right_priority_run d leftLetter rightLetter hl hr]

include hl hr in
/-- The generated guard recognizes exactly implication between the two
original automata, evaluated on the same physical time sequence. -/
theorem accepts_guard_iff (word : OmegaWord (Alphabet d)) :
    (EncodedParityFamilies.automaton (guardData d)).Accepts word ↔
      ((EncodedParityTables.automaton (left d)).Accepts (fun n => leftLetter (word n)) →
        (EncodedParityTables.automaton (right d)).Accepts (fun n => rightLetter (word n))) := by
  unfold guardData
  rw [EncodedParityFamilies.accepts_guard_iff]
  change (test d (leftPriorities d)).Accepts word → (test d (rightPriorities d)).Accepts word ↔ _
  rw [left_accepts_iff d leftLetter rightLetter hl hr,right_accepts_iff d leftLetter rightLetter hl hr]

include hl hr in
theorem accepts_conjunction_iff (word : OmegaWord (Alphabet d)) :
    (EncodedParityFamilies.automaton (conjunctionData d)).Accepts word ↔
      ((EncodedParityTables.automaton (left d)).Accepts (fun n => leftLetter (word n)) ∧
        (EncodedParityTables.automaton (right d)).Accepts (fun n => rightLetter (word n))) := by
  unfold conjunctionData
  rw [EncodedParityFamilies.accepts_conjunction_iff]
  change (∀ p ∈ [leftPriorities d,rightPriorities d], (test d p).Accepts word) ↔ _
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  rw [left_accepts_iff d leftLetter rightLetter hl hr,right_accepts_iff d leftLetter rightLetter hl hr]

end Characterisation.EncodedParityProduct
