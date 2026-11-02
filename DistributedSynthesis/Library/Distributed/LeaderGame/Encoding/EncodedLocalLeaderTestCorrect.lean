/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLocalLeaderAlphabet
import DistributedSynthesis.Library.Distributed.ThreadWordMonitor
import DistributedSynthesis.Library.Computability.FiniteTableLookup
import DistributedSynthesis.Library.Automata.TreeMonitorRetraction

/-! Exact local-test correctness. All narrowed labels and hidden-input edges
are generated; the final decision is the existing parity-tree solver. -/
namespace Characterisation.EncodedLocalLeaderTest
open DistributedSynthesis

variable (d : Data)

local instance : DecidableEq (monitor d).State := inferInstanceAs (DecidableEq (Fin (states d)))
local instance : Fintype (SemanticLabel d) := inferInstanceAs
  (Fintype ((Fin (senderInputs d) → Fin (senderOutputs d)) ×
    (Fin (states d) → Fin (receiverInputs d) × Fin (senderInputs d) → Fin (receiverOutputs d))))

def stateNumber : (monitor d).State ≃ Fin (Fintype.card (monitor d).State) :=
  finCongr (Fintype.card_fin (states d)).symm

theorem stateNumber_val (q : (monitor d).State) : (stateNumber d q).val = q.val := rfl

def checker : DetParityAutomaton (BlockRecordMonitor.ThreadLetter (monitor d)) :=
  EncodedThreadStream.automaton (config d) (fun a => edges d (labelEncode d a.1) a.2.val)

theorem checker_accepts_iff (word : OmegaWord (BlockRecordMonitor.ThreadLetter (monitor d))) :
    (checker d).Accepts word ↔ ∀ q, (monitor d).IsThread word q →
      NatSeqMinEvenParity (fun n => (monitor d).priority (q n)) := by
  have hp : ∀ q, (priorities d).getD (stateNumber d q).val 0 = (monitor d).priority q := by
    intro q
    rw [stateNumber_val]
    exact priorities_get d q
  have he : ∀ (q : (monitor d).State) (a : BlockRecordMonitor.ThreadLetter (monitor d))
      (r : (monitor d).State), ((stateNumber d q).val,(stateNumber d r).val) ∈
        edges d (labelEncode d a.1) a.2.val ↔
          ∃ i : Fin (receiverInputs d), r = (monitor d).step q (narrowedRecord (monitor d) a.1 q (i,a.2)) := by
    intro q a r
    simp only [stateNumber_val]
    exact edges_encode d q r a.1 a.2
  have h := EncodedThreadStream.accepts_iff
    (L := BlockRecordMonitor.ThreadLetter (monitor d)) (monitor d) (stateNumber d) (priorities d)
    hp (priorities_range d)
    (fun a : BlockRecordMonitor.ThreadLetter (monitor d) => edges d (labelEncode d a.1) a.2.val)
    (fun a => a) he word
  have configEq : (Fintype.card (monitor d).State, (stateNumber d (monitor d).initial).val,priorities d) = config d := by
    change (Fintype.card (Fin (states d)),_,_) = _
    rw [Fintype.card_fin]
    rfl
  rw [configEq] at h
  exact h

theorem checkerStates_pos : 0 < checkerStates d :=
  lt_of_le_of_lt (Nat.zero_le _) (checker d).initial.isLt

theorem bound_compile : EncodedTreeNonemptiness.bound (compile d) = checkerStates d :=
  Nat.sub_add_cancel (checkerStates_pos d)

local notation "N" => EncodedTreeNonemptiness.monitor (compile d)
local notation "T" => WordTreeMonitor.monitor (checker d)

def projectState (q : (N).State) : (T).State := ⟨q.val,by simpa only [bound_compile] using q.isLt⟩

noncomputable def decodeLabel (l : Fin (labels d).length) : SemanticLabel d := (labelNumber d).symm l

theorem get_decodeLabel (l : Fin (labels d).length) : (labels d)[l.val] = labelEncode d (decodeLabel d l) := by
  have h := label_get d ((labelNumber d).symm l)
  simpa only [Equiv.apply_symm_apply,decodeLabel] using h

theorem rawNext_compile (q : (N).State) (l : Fin (labels d).length) (s : Fin (senderInputs d)) :
    EncodedTreeNonemptiness.rawNext (compile d) q.val l.val s.val =
      EncodedThreadStream.next (config d,edges d (labelEncode d (decodeLabel d l)) s.val,q.val) := by
  have bound : q.val < checkerStates d := by simpa only [bound_compile] using q.isLt
  have lookup := FiniteTableLookup.lookup3 (List.range (checkerStates d)) (labels d) (List.range (senderInputs d))
    (fun q l s => EncodedThreadStream.next (config d,edges d l s,q))
    ⟨q.val,by simpa only [List.length_range] using bound⟩ l
    ⟨s.val,by simpa only [List.length_range] using s.isLt⟩ 0
  simp only [List.length_range,List.getElem_range,get_decodeLabel] at lookup
  exact lookup

theorem project_initial : projectState d (N).initial = (T).initial := by
  apply Fin.ext
  change EncodedThreadStream.initial (config d) % EncodedTreeNonemptiness.bound (compile d) = _
  rw [bound_compile]
  exact Nat.mod_eq_of_lt (checker d).initial.isLt

theorem project_step (q : (N).State) (l : Fin (labels d).length) (s : Fin (senderInputs d)) :
    projectState d ((N).step q l s) = (T).step (projectState d q) (decodeLabel d l) s := by
  apply Fin.ext
  change EncodedTreeNonemptiness.rawNext (compile d) q.val l.val s.val % EncodedTreeNonemptiness.bound (compile d) = _
  rw [rawNext_compile]
  simp only [bound_compile]
  exact Nat.mod_eq_of_lt ((checker d).step (projectState d q) (decodeLabel d l,s)).isLt

theorem project_priority (q : (N).State) : (N).priority q = (T).priority (projectState d q) := by
  have bound : q.val < checkerStates d := by simpa only [bound_compile] using q.isLt
  change ((List.range (checkerStates d)).map (EncodedThreadStream.priority (config d))).getD q.val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa using bound)]
  simp only [List.getElem_map,List.getElem_range]
  rfl

/-- Uniform generation and solving are exactly the original local leader
test, including every state-contingent follower response and hidden input. -/
theorem solve_correct : solve d = true ↔ ∃ tree, NarrowedAllThreadsWin (monitor d) tree := by
  rw [solve,EncodedTreeNonemptiness.solve_correct]
  apply (TreeMonitorRetraction.nonempty_iff N T (projectState d) id (decodeLabel d)
    (project_initial d) (project_step d) (project_priority d)
    Function.surjective_id (labelNumber d).symm.surjective).trans
  apply exists_congr
  intro tree
  exact ((T).acceptsTree_iff_winningTree tree).trans
    (ThreadWordMonitor.winning_iff (monitor d) (checker d) (checker_accepts_iff d) tree)

theorem solve_eq_leaderThreadTest : solve d = leaderThreadTest (monitor d) := by
  apply Bool.eq_iff_iff.mpr
  exact (solve_correct d).trans (leaderThreadTest_correct (monitor d)).symm

end Characterisation.EncodedLocalLeaderTest
