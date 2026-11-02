/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedMuller
import DistributedSynthesis.Formalizations.Theorem.ThmMullerToDPA

/-! Numeric LAR correctness by simulation of the existing semantic LAR.
The numeric state enumeration may contain unused records; only the actual
run is compared, so these extra states cannot change word acceptance. -/
namespace Characterisation.EncodedMuller
open DistributedSynthesis DetMullerAutomaton.LAR
local instance : BEq State := instBEqOfDecidableEq
def semantic (d : Data) : DetMullerAutomaton (Fin (rows d).length) where
  State := Fin (size d)
  stateFinite := inferInstance
  initial := ⟨first d % size d,Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q a := ⟨next d q.val a.val,Nat.mod_lt _ (Nat.succ_pos _)⟩
  accepting S := ∃ t : Finset (Fin (size d)), (t : Set (Fin (size d))) = S ∧ FiniteSubsets.encode t ∈ accepting d

open DetMullerAutomaton.LAR

def encode (d : Data) (s : EventState (semantic d)) : State :=
  (s.1.val,s.2.1.order.map Fin.val,FiniteSubsets.encode s.2.2)

theorem accepting_encode (d : Data) (s : Finset (Fin (size d))) :
    (s : Set (Fin (size d))) ∈ (semantic d).accepting ↔ FiniteSubsets.encode s ∈ accepting d := by
  constructor
  · rintro ⟨t,h,hm⟩
    exact Finset.coe_injective h ▸ hm
  · intro h
    exact ⟨s,rfl,h⟩

theorem encode_mem (d : Data) (s : EventState (semantic d)) : encode d s ∈ rawStates d := by
  refine List.mem_product.mpr ⟨List.mem_range.mpr s.1.isLt,List.mem_product.mpr ⟨?_,FiniteSubsets.encode_mem_codes _⟩⟩
  have len : s.2.1.order.length = size d := by
    rw [s.2.1.length_eq_card]
    exact Fintype.card_fin _
  let f : Fin (size d) → Nat := fun i => (s.2.1.order[i.val]'(by omega)).val
  have eq : s.2.1.order.map Fin.val = List.ofFn f := by
    apply List.ext_getElem
    · exact (List.length_map ..).trans (len.trans List.length_ofFn.symm)
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_ofFn]
      rfl
  rw [eq]
  exact FiniteSearch.ofFn_mem_words _ f (fun i => List.mem_range.mpr (s.2.1.order[i.val]'(by omega)).isLt)

theorem name_lt (d : Data) (s : EventState (semantic d)) : name d (encode d s) < (states d).length := by
  unfold name states FiniteCodeNumbering.name
  exact List.idxOf_lt_length_iff.mpr ((FiniteCodeNumbering.mem_unique _ _).mpr (encode_mem d s))

def startRecord (d : Data) : Record (semantic d) where
  order := List.finRange (size d)
  nodup := List.nodup_finRange _
  complete := by intro q; exact List.mem_finRange q

def start (d : Data) : EventState (semantic d) := ((semantic d).initial,startRecord d,∅)
theorem initial_encode (d : Data) : initial d = encode d (start d) := by
  change (_,List.range (size d),[]) = (_, (List.finRange (size d)).map Fin.val,FiniteSubsets.encode (∅ : Finset (Fin (size d))))
  simp [start,semantic,FiniteSubsets.encode]

theorem states_pos (d : Data) : 0 < (states d).length :=
  lt_of_le_of_lt (Nat.zero_le _) (name_lt d (start d))


private abbrev finDecidable (n : Nat) : DecidableEq (Fin n) := inferInstance
private abbrev finBEq (n : Nat) : BEq (Fin n) := inferInstance
private instance (n : Nat) : @LawfulBEq (Fin n) (finBEq n) := inferInstanceAs (LawfulBEq (Fin n))

variable (d : Data)
local notation "M" => semantic d
local notation "L" => eventAutomaton (A:=M)

private theorem normalize_map (xs : List (Fin (size d))) :
    FiniteSubsets.normalize (size d) (xs.map Fin.val) = FiniteSubsets.encode xs.toFinset := by
  rw [← FiniteSubsets.normalize_encode xs.toFinset,FiniteSubsets.normalize_eq_iff]
  rw [FiniteSubsets.decode_encode]
  ext q
  simp only [FiniteSubsets.mem_decode,List.mem_map,List.mem_toFinset]
  constructor
  · rintro ⟨r,hr,eq⟩
    exact Fin.ext eq ▸ hr
  · intro h
    exact ⟨q,h,rfl⟩

private theorem filter_map (xs : List (Fin (size d))) (q : Fin (size d)) :
    (xs.map Fin.val).filter (fun r => decide (r ≠ q.val)) =
      (xs.filter (· != q)).map Fin.val := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    simp only [decide_not] at ih
    by_cases h : r = q
    · subst r
      simp
      exact ih
    · have hv : r.val ≠ q.val := fun eq => h (Fin.ext eq)
      simp [h,hv]
      exact ih

theorem step_encode (s : EventState M) (a : Fin (rows d).length) :
    step d (encode d s) a.val = encode d ((L).step s a) := by
  letI : DecidableEq (M).State := finDecidable (size d)
  letI : BEq (M).State := finBEq (size d)
  letI : LawfulBEq (M).State := inferInstanceAs (@LawfulBEq (Fin (size d)) (finBEq (size d)))
  dsimp only [step,encode,eventAutomaton,eventAutomatonWithPriority,eventStep,Record.refresh,Record.hitSet]
  have hd : (fun a b : (M).State => Classical.propDecidable (a=b)) = finDecidable (size d) := Subsingleton.elim _ _
  have hb : @instBEqOfDecidableEq (Fin (size d)) (finDecidable (size d)) = finBEq (size d) :=
    lawful_beq_subsingleton _ _
  erw [hd,hb]
  erw [s.2.1.nodup.erase_eq_filter]
  erw [List.map_cons]
  erw [← filter_map,FiniteSubsets.idxOf_map_val s.2.1.order ((M).step s.1 a),← List.map_take,normalize_map]
  rfl

theorem priority_encode (s : EventState M) : priority d (encode d s) = (L).priority s := by
  classical
  change (if FiniteSubsets.encode s.2.2 ∈ accepting d then
    2*(size d-(FiniteSubsets.encode s.2.2).length) else 2*(size d-(FiniteSubsets.encode s.2.2).length)+1) =
    (if (s.2.2 : Set (M).State) ∈ (M).accepting then
      2*(Fintype.card (M).State-s.2.2.card) else 2*(Fintype.card (M).State-s.2.2.card)+1)
  rw [FiniteSubsets.encode_length]
  erw [accepting_encode]
  have card : Fintype.card (M).State = size d := Fintype.card_fin _
  rw [card]
  split_ifs <;> rfl

theorem size_compile : EncodedParityTables.size (compile d) = (states d).length :=
  Nat.sub_add_cancel (states_pos d)
theorem alphabet_compile : (EncodedParityTables.rows (compile d)).length = (rows d).length := by
  change (transitions d).length = _
  simp [transitions]

/-- Read the compiled table on the source row-index alphabet. -/
def automaton : DetParityAutomaton (Fin (rows d).length) :=
  (EncodedParityTables.automaton (compile d)).comap (finCongr (alphabet_compile d).symm)

def embed (s : EventState M) : (automaton d).State :=
  ⟨name d (encode d s),by rw [size_compile]; exact name_lt d s⟩

theorem get_name (s : EventState M) :
    (states d)[name d (encode d s)]'(name_lt d s) = encode d s := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (name_lt d s)).symm.trans
  simpa only [states,name] using
    FiniteCodeNumbering.get_name (rawStates d) (encode d) (encode_mem d) s

theorem embed_initial : (automaton d).initial = embed d (start d) := by
  apply Fin.ext
  change name d (initial d) % EncodedParityTables.size (compile d) = _
  rw [initial_encode]
  exact Nat.mod_eq_of_lt (embed d (start d)).isLt

theorem embed_step (s : EventState M) (a : Fin (rows d).length) :
    (automaton d).step (embed d s) a = embed d ((L).step s a) := by
  apply Fin.ext
  change (((transitions d).getD a.val []).getD (name d (encode d s)) 0) %
    EncodedParityTables.size (compile d) = _
  have ha : a.val < (transitions d).length := by simpa only [transitions,List.length_map,List.length_range] using a.isLt
  rw [List.getD_eq_getElem _ _ ha]
  simp only [transitions,List.getElem_map,List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using name_lt d s),
    List.getElem_map,get_name,step_encode]
  exact Nat.mod_eq_of_lt (embed d ((L).step s a)).isLt

theorem embed_priority (s : EventState M) :
    (automaton d).priority (embed d s) = (L).priority s := by
  change ((states d).map (priority d)).getD (name d (encode d s)) 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using name_lt d s),
    List.getElem_map,get_name,priority_encode]

theorem run_embed (word : OmegaWord (Fin (rows d).length)) (t : Nat) :
    (automaton d).run word t = embed d ((L).runFrom (start d) word t) := by
  induction t with
  | zero => exact embed_initial d
  | succ t ih =>
    rw [DetParityAutomaton.run_succ,ih,embed_step]
    rfl

/-- The uniform numeric compiler recognizes exactly its Muller input. -/
theorem accepts_iff (word : OmegaWord (Fin (rows d).length)) :
    (automaton d).Accepts word ↔ (M).Accepts word := by
  have hp (t : Nat) : (automaton d).priority ((automaton d).run word t) =
      (L).priority ((L).runFrom (start d) word t) := by
    rw [run_embed,embed_priority]
  have same : (automaton d).Accepts word ↔ (L).AcceptsFrom (start d) word := by
    unfold DetParityAutomaton.Accepts DetParityAutomaton.AcceptsFrom
      DetParityAutomaton.PrioritySeenInfinitelyOftenFrom
    simp only [DetParityAutomaton.run] at hp
    simp only [hp]
  exact same.trans (eventAutomaton_correctFrom (A:=M) (start d) word)

end Characterisation.EncodedMuller
