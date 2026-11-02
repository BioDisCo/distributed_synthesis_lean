/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalStateCoding

/-! # Exact priority-table correspondence, including the even global shift -/
namespace DistributedSynthesis.EncodedJournalPriorities
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedJournalStateCoding DetParityAutomaton

theorem maximum_eq_sup (xs : List Nat) : EncodedJournalTransitions.maximum xs = xs.toFinset.sup id := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [EncodedJournalTransitions.maximum,List.foldr_cons,List.toFinset_cons,
      Finset.sup_insert,← ih]; rfl

variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))

theorem shift_correct : EncodedJournalTransitions.shift d = JournalCompilation.shift A := by
  unfold EncodedJournalTransitions.shift JournalCompilation.shift
  congr 2
  rw [maximum_eq_sup]
  apply le_antisymm
  · apply Finset.sup_le
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact Finset.le_sup (f := fun q : (A).State => (A).priority q)
      (Finset.mem_univ (⟨q,List.mem_range.mp hq⟩ : (A).State))
  · apply Finset.sup_le
    intro q _
    exact Finset.le_sup (f := id) (List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨q.val,List.mem_range.mpr q.isLt,rfl⟩))

theorem priority_correct (q : Semantic d) :
    EncodedJournalTransitions.priority d (encode d q) = (EncodedJournalAssembly.compile d).priority q := by
  rcases q with a | ⟨q,T⟩ | ⟨q,T⟩ | ⟨q,T⟩ | ⟨q,T⟩ | u
  all_goals simp only [EncodedJournalTransitions.priority,encode,EncodedJournalTransitions.sink,
    Nat.reduceLT,Nat.reduceEqDiff,if_true,if_false,pairedIndex_mod,shift_correct]
  all_goals rfl
end DistributedSynthesis.EncodedJournalPriorities
