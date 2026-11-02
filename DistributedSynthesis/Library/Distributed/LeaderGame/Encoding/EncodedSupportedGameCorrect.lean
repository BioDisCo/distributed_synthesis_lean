/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedSupportedGame
import DistributedSynthesis.Library.Distributed.LeaderPhases.SupportedPublicTree
import DistributedSynthesis.Library.Computability.FiniteTableLookup
import DistributedSynthesis.Library.Automata.TreeMonitorRetraction

/-! Correctness of the numeric supported-game compiler, using the existing
finite numbering, flattened-table lookup, and tree-monitor retraction. -/
namespace Characterisation.EncodedSupportedGame
open DistributedSynthesis

/-- The numeric progress table is read on move/observation pairs using the
same move-major indexing as the offer table. -/
def wordAutomaton (d : Data) : DetParityAutomaton (Fin (moves d) × Fin (observations d)) where
  State := Fin (EncodedParityTables.size (progress d))
  stateFinite := inferInstance
  initial := ⟨EncodedParityTables.initial (progress d) % EncodedParityTables.size (progress d),Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q a := ⟨EncodedParityTables.next (progress d) q.val (a.1.val*observations d+a.2.val),Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := EncodedParityTables.priority (progress d) q.val

def semantic (d : Data) := supportedPublicTreeMonitor (wordAutomaton d)
  (fun l b => offered d l.val b.val) (⟨first d % observations d,Nat.mod_lt _ (Nat.succ_pos _)⟩)
  (fun b l => allowed d b.val l.val = true)

def encode (d : Data) (s : (semantic d).State) : State := (s.1.val,s.2.1.val,s.2.2)

theorem encode_injective (d : Data) : Function.Injective (encode d) := by
  rintro ⟨b,q,s,v⟩ ⟨b',q',s',v'⟩ equal
  simp only [encode,Prod.mk.injEq] at equal
  rcases equal with ⟨hb,hq,hs,hv⟩
  cases Fin.ext hb
  cases Fin.ext hq
  cases hs
  cases hv
  rfl

theorem mem_rawStates (d : Data) (s : State) :
    s ∈ rawStates d ↔ s.1 < observations d ∧ s.2.1 < EncodedParityTables.size (progress d) := by
  rcases s with ⟨b,q,s,v⟩
  cases s <;> cases v <;> simp [rawStates]

theorem encode_mem (d : Data) (s : (semantic d).State) : encode d s ∈ rawStates d :=
  (mem_rawStates d _).mpr ⟨s.1.isLt,s.2.1.isLt⟩
theorem codes_complete (d : Data) (s : State) (member : s ∈ rawStates d) :
    ∃ q : (semantic d).State, encode d q = s := by
  obtain ⟨hb,hq⟩ := (mem_rawStates d s).mp member
  exact ⟨(⟨s.1,hb⟩,⟨s.2.1,hq⟩,s.2.2),rfl⟩

noncomputable def number (d : Data) : (semantic d).State ≃ Fin (states d).length :=
  (FiniteCodeNumbering.equiv (rawStates d) (encode d) (encode_injective d) (encode_mem d) (codes_complete d)).trans
    (finCongr (by rw [states]))
theorem number_val (d : Data) (q : (semantic d).State) : (number d q).val = name d (encode d q) := rfl

theorem states_pos (d : Data) : 0 < (states d).length :=
  lt_of_le_of_lt (Nat.zero_le _) (number d (semantic d).initial).isLt

theorem initial_encode (d : Data) : initial d = encode d (semantic d).initial := rfl

theorem step_encode (d : Data) (q : (semantic d).State) (l : Fin (moves d)) (b : Fin (observations d)) :
    step d (encode d q) l.val b.val = encode d ((semantic d).step q l b) := by
  simp [step,encode,semantic,supportedPublicTreeMonitor,wordAutomaton]
theorem priority_encode (d : Data) (q : (semantic d).State) :
    priority d (encode d q) = (semantic d).priority q := rfl


variable (d : Data)
local notation "S" => semantic d
local notation "N" => EncodedTreeNonemptiness.monitor (compile d)

theorem bound_eq : EncodedTreeNonemptiness.bound (compile d) = (states d).length :=
  Nat.sub_add_cancel (states_pos d)

noncomputable def stateNumber : (S).State ≃ (N).State :=
  (number d).trans (finCongr (bound_eq d).symm)
theorem stateNumber_val (q : (S).State) : (stateNumber d q).val = name d (encode d q) := rfl

theorem get_number (q : (S).State) : (states d)[(number d q).val] = encode d q := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (number d q).isLt).symm.trans
  simpa only [states,number_val,name] using
    (FiniteCodeNumbering.get_name (rawStates d) (encode d) (encode_mem d) q)

theorem raw_next (q : (S).State) (l : Fin (moves d)) (b : Fin (observations d)) :
    EncodedTreeNonemptiness.rawNext (compile d) (stateNumber d q).val l.val b.val =
      name d (encode d ((S).step q l b)) := by
  change (transitions d).getD (((number d q).val*moves d+l.val)*observations d+b.val) 0 = _
  have lookup := FiniteTableLookup.lookup3 (states d) (List.range (moves d)) (List.range (observations d))
    (fun s l b => name d (step d s l b)) (number d q)
    (⟨l.val,by simpa only [List.length_range] using l.isLt⟩)
    (⟨b.val,by simpa only [List.length_range] using b.isLt⟩) 0
  simp only [List.length_range,List.getElem_range,get_number] at lookup
  rw [transitions,lookup,step_encode]

theorem initial_number : (N).initial = stateNumber d (S).initial := by
  apply Fin.ext
  change name d (initial d) % EncodedTreeNonemptiness.bound (compile d) = _
  rw [initial_encode,← stateNumber_val]
  exact Nat.mod_eq_of_lt (stateNumber d (S).initial).isLt

theorem next_number (q : (S).State) (l : Fin (moves d)) (b : Fin (observations d)) :
    (N).step (stateNumber d q) l b = stateNumber d ((S).step q l b) := by
  apply Fin.ext
  change EncodedTreeNonemptiness.rawNext (compile d) (stateNumber d q).val l.val b.val %
    EncodedTreeNonemptiness.bound (compile d) = _
  rw [raw_next,← stateNumber_val]
  exact Nat.mod_eq_of_lt (stateNumber d ((S).step q l b)).isLt

theorem priority_number (q : (S).State) : (N).priority (stateNumber d q) = (S).priority q := by
  change ((states d).map (priority d)).getD (number d q).val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using (number d q).isLt),
    List.getElem_map,get_number,priority_encode]

theorem nonempty_iff : EncodedTreeNonemptiness.Nonempty (compile d) ↔
    ∃ tree, (S).toRunAutomaton.acceptsTree tree := by
  apply TreeMonitorRetraction.nonempty_iff N S (stateNumber d).symm id id
  · exact (congrArg (stateNumber d).symm (initial_number d)).trans ((stateNumber d).symm_apply_apply _)
  · intro q l b
    have h := (congrArg (fun r => (N).step r l b) ((stateNumber d).apply_symm_apply q)).symm.trans
      (next_number d ((stateNumber d).symm q) l b)
    exact (congrArg (stateNumber d).symm h).trans ((stateNumber d).symm_apply_apply _)
  · intro q
    exact (congrArg (N).priority ((stateNumber d).apply_symm_apply q)).symm.trans
      (priority_number d ((stateNumber d).symm q))
  · exact Function.surjective_id
  · exact Function.surjective_id

def solve (d : Data) := EncodedTreeNonemptiness.solve (compile d)
theorem solve_primrec : Primrec solve := EncodedTreeNonemptiness.solve_primrec.comp compile_primrec

theorem solve_correct : solve d = true ↔ ∃ tree, (S).WinningTree tree := by
  rw [solve,EncodedTreeNonemptiness.solve_correct,nonempty_iff]
  apply exists_congr
  intro tree
  exact (S).acceptsTree_iff_winningTree tree

/-- Legality at supported nodes and progress on every supported infinite
branch are both decided by the existing solver on the compiled data. -/
theorem solve_supported_iff : solve d = true ↔ ∃ tree,
    SupportedMovesValid (fun l b => offered d l.val b.val)
      (⟨first d % observations d,Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (observations d))
      (fun b l => allowed d b.val l.val = true) tree ∧
    ∀ branch, (∀ n, publicSupport (fun l b => offered d l.val b.val) tree (branchNode branch n) = true) →
      (wordAutomaton d).Accepts (observableThreadWord tree branch) := by
  letI : Inhabited (Fin (observations d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
  rw [solve_correct]
  apply exists_congr
  intro tree
  exact supportedPublicTreeMonitor_winning_iff (wordAutomaton d)
    (fun l b => offered d l.val b.val) _ (fun b l => allowed d b.val l.val = true) tree

end Characterisation.EncodedSupportedGame
