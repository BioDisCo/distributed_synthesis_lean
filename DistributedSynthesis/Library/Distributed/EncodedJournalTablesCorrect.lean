/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalAlphabetCoding
import DistributedSynthesis.Library.Distributed.EncodedJournalPriorities
import DistributedSynthesis.Library.Computability.FiniteTableLookup
import DistributedSynthesis.Library.Automata.TreeMonitorRetraction

/-! # Exact nonemptiness of the numeric journal tables -/
namespace DistributedSynthesis.EncodedJournalTablesCorrect
open EncodedRoundObjectives EncodedJournalStateCoding EncodedJournalAlphabetCoding
  EncodedJournalTransitionsCorrect DetParityAutomaton
variable (d : Data)
local notation "J" => EncodedJournalAssembly.compile d
local notation "N" => EncodedTreeNonemptiness.monitor (EncodedJournalTables.compile d)

theorem bound_eq : EncodedTreeNonemptiness.bound (EncodedJournalTables.compile d) =
    (EncodedJournalTables.states d).length := Nat.sub_add_cancel (states_pos d)

@[irreducible] noncomputable def stateNumber : Semantic d ≃ (N).State :=
  (number d).trans (finCongr (bound_eq d).symm)
theorem stateNumber_val (q : Semantic d) :
    (stateNumber d q).val = EncodedJournalTables.name d (encode d q) := by unfold stateNumber; rfl
theorem stateNumber_val_number (q : Semantic d) : (stateNumber d q).val = (number d q).val := by unfold stateNumber; rfl

theorem get_number_elem (q : Semantic d) :
    (EncodedJournalTables.states d)[(number d q).val] = encode d q := by
  apply Option.some.inj
  exact (List.getElem?_eq_getElem (number d q).isLt).symm.trans (get_number d q)

theorem raw_next (q : Semantic d) (l : Fin (EncodedJournalTables.labels d).length)
    (b : Fin (EncodedJournalTables.branches d).length) :
    EncodedTreeNonemptiness.rawNext (EncodedJournalTables.compile d) (stateNumber d q).val l.val b.val =
      EncodedJournalTables.name d (encode d ((J).step q (labelAt d l) (branchAt d b))) := by
  rw [stateNumber_val_number]
  change (EncodedJournalTables.transitions d).getD
    (((number d q).val*(EncodedJournalTables.labels d).length+l.val)*(EncodedJournalTables.branches d).length+b.val) 0 = _
  unfold EncodedJournalTables.transitions
  rw [FiniteTableLookup.lookup3,get_number_elem,← code_branchAt d b]
  rw [step_correct]
  unfold labelAt
  rfl

theorem initial_number : (N).initial = stateNumber d (J).initial := by
  apply Fin.ext
  change EncodedJournalTables.name d (EncodedJournalTransitions.initial d) %
    EncodedTreeNonemptiness.bound (EncodedJournalTables.compile d) = _
  rw [initial_correct,← stateNumber_val]
  exact Nat.mod_eq_of_lt (stateNumber d (J).initial).isLt

theorem next_number (q : Semantic d) (l : Fin (EncodedJournalTables.labels d).length)
    (b : Fin (EncodedJournalTables.branches d).length) :
    (N).step (stateNumber d q) l b = stateNumber d ((J).step q (labelAt d l) (branchAt d b)) := by
  apply Fin.ext
  change EncodedTreeNonemptiness.rawNext (EncodedJournalTables.compile d) (stateNumber d q).val l.val b.val %
    EncodedTreeNonemptiness.bound (EncodedJournalTables.compile d) = _
  rw [raw_next,← stateNumber_val]
  exact Nat.mod_eq_of_lt (stateNumber d ((J).step q (labelAt d l) (branchAt d b))).isLt

theorem priority_number (q : Semantic d) : (N).priority (stateNumber d q) = (J).priority q := by
  change ((EncodedJournalTables.states d).map (EncodedJournalTransitions.priority d)).getD (stateNumber d q).val 0 = _
  rw [stateNumber_val_number]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using (number d q).isLt),List.getElem_map,
    get_number_elem,EncodedJournalPriorities.priority_correct]

theorem nonempty_iff : EncodedTreeNonemptiness.Nonempty (EncodedJournalTables.compile d) ↔
    ∃ tree, (J).toRunAutomaton.acceptsTree tree := by
  apply TreeMonitorRetraction.nonempty_iff N J (stateNumber d).symm (branchAt d) (labelAt d)
  · exact (congrArg (stateNumber d).symm (initial_number d)).trans ((stateNumber d).symm_apply_apply _)
  · intro q l b
    have h := (congrArg (fun r => (N).step r l b) ((stateNumber d).apply_symm_apply q)).symm.trans
      (next_number d ((stateNumber d).symm q) l b)
    exact (congrArg (stateNumber d).symm h).trans ((stateNumber d).symm_apply_apply _)
  · intro q
    exact (congrArg (N).priority ((stateNumber d).apply_symm_apply q)).symm.trans
      (priority_number d ((stateNumber d).symm q))
  · exact branchAt_surjective d
  · exact labelAt_surjective d

theorem realizable_iff_nonempty : NoDirectJournal.Realizable (EncodedRoundObjectives.automaton d) ↔
    EncodedTreeNonemptiness.Nonempty (EncodedJournalTables.compile (EncodedReversalForgiving.compile d)) :=
  (EncodedJournalAssembly.realizable_iff_nonempty d).trans (nonempty_iff (EncodedReversalForgiving.compile d)).symm
end DistributedSynthesis.EncodedJournalTablesCorrect
