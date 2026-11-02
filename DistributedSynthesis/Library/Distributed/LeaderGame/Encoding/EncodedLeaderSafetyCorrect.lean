/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderSafety
import DistributedSynthesis.Library.Automata.EncodedParityConjunctionCorrect
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderMemoryCompression

/-! The generated safety component accepts precisely when every check on
the evolving memory succeeds. Conjunction with the physical objective uses
the existing synchronous parity compiler. -/
namespace Characterisation.EncodedLeaderSafety
open DistributedSynthesis

variable (d : Data)
abbrev Alphabet := Fin (EncodedLocalLeaderTest.physicalSize (base d))
def automaton := EncodedParityConjunction.read (safety d) (EncodedLocalLeaderTest.physicalSize (base d))
def memoryRun (word : OmegaWord (Alphabet d)) :=
  phaseMemoryRun (initialMemory d) (fun m a : Nat => memoryNext d m a) (fun n => (word n).val)

theorem safety_alphabet : (EncodedParityTables.rows (safety d)).length =
    EncodedLocalLeaderTest.physicalSize (base d) := by simp [safety,EncodedParityTables.rows]

theorem step_lt (q a : Nat) : step d q a < memorySize d+1 := by
  unfold step
  split
  · exact Nat.succ_pos _
  · split
    · exact Nat.succ_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
    · exact Nat.succ_pos _

theorem next_val (q : (automaton d).State) (a : Alphabet d) :
    ((automaton d).step q a).val = step d q.val a.val := by
  have row : ((List.range (EncodedLocalLeaderTest.physicalSize (base d))).map
      (fun a => (List.range (memorySize d+1)).map (fun q => step d q a))).getD a.val [] =
      (List.range (memorySize d+1)).map (fun q => step d q a.val) := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using a.isLt)]
    simp only [List.getElem_map,List.getElem_range]
  change (((List.range (EncodedLocalLeaderTest.physicalSize (base d))).map
    (fun a => (List.range (memorySize d+1)).map (fun q => step d q a))).getD a.val []).getD q.val 0 %
      (memorySize d+1) = _
  rw [row]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using q.isLt)]
  simp only [List.getElem_map,List.getElem_range]
  exact Nat.mod_eq_of_lt (step_lt d q.val a.val)

theorem initial_val : (automaton d).initial.val = initialMemory d+1 :=
  Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.mod_lt _ (Nat.succ_pos _)))

theorem priority_val (q : (automaton d).State) : (automaton d).priority q = priority q.val := by
  change ((List.range (memorySize d+1)).map priority).getD q.val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using q.isLt)]
  simp only [List.getElem_map,List.getElem_range]

theorem run_succ (word : OmegaWord (Alphabet d)) (n : Nat) :
    ((automaton d).run word (n+1)).val = step d ((automaton d).run word n).val (word n).val :=
  next_val d _ _

theorem run_cases (word : OmegaWord (Alphabet d)) (n : Nat) :
    ((automaton d).run word n).val = 0 ∨
      ((automaton d).run word n).val = memoryRun d word n+1 := by
  induction n with
  | zero => exact Or.inr (initial_val d)
  | succ n ih =>
    rw [run_succ]
    rcases ih with dead | live
    · exact Or.inl (by simp [dead,step])
    · rw [live]
      by_cases check : valid d (memoryRun d word n) (word n).val = true
      · right
        simp only [step,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,
          check,if_true]
        rfl
      · left
        simp [step,check]

theorem dead_persists (word : OmegaWord (Alphabet d)) (n : Nat)
    (dead : ((automaton d).run word n).val = 0) (k : Nat) :
    ((automaton d).run word (n+k)).val = 0 := by
  induction k with
  | zero => exact dead
  | succ k ih => rw [Nat.add_succ,run_succ,ih]; simp [step]

theorem live_of_accepts (word : OmegaWord (Alphabet d))
    (accepts : (automaton d).Accepts word) (n : Nat) : ((automaton d).run word n).val ≠ 0 := by
  intro dead
  have parity := (DetParityAutomaton.accepts_iff_natSeqMinEvenParity _ _).mp accepts
  apply not_natSeqMinEvenParity_of_eventually_one _ n ?_ parity
  intro k lower
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le lower
  rw [priority_val,dead_persists d word n dead j]
  rfl

/-- A single failed promise is rejecting even if all later promises pass. -/
theorem accepts_iff (word : OmegaWord (Alphabet d)) : (automaton d).Accepts word ↔
    ∀ n, valid d (memoryRun d word n) (word n).val = true := by
  constructor
  · intro accepted n
    have live := (run_cases d word n).resolve_left (live_of_accepts d word accepted n)
    have nextLive := live_of_accepts d word accepted (n+1)
    rw [run_succ,live] at nextLive
    by_contra failed
    apply nextLive
    simp [step,failed]
  · intro checks
    have live : ∀ n, ((automaton d).run word n).val = memoryRun d word n+1 := by
      intro n
      induction n with
      | zero => exact initial_val d
      | succ n ih =>
        rw [run_succ,ih]
        simp only [step,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,
          checks n,if_true]
        rfl
    rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
    have ranks : ∀ n, (automaton d).priority ((automaton d).run word n) = 0 := by
      intro n
      rw [priority_val,live]
      simp [priority]
    simp only [ranks]
    exact ⟨0,⟨0,rfl⟩,(fun n => ⟨n,le_rfl,rfl⟩),fun _ _ => Nat.zero_le _⟩

theorem compile_accepts_iff
    (alphabet : (EncodedParityTables.rows (EncodedLocalLeaderTest.monitorData (base d))).length =
      EncodedLocalLeaderTest.physicalSize (base d)) (word : OmegaWord (Alphabet d)) :
    (EncodedParityConjunction.read (EncodedLocalLeaderTest.monitorData (compile d))
      (EncodedLocalLeaderTest.physicalSize (base d))).Accepts word ↔
      (EncodedParityConjunction.read (EncodedLocalLeaderTest.monitorData (base d))
        (EncodedLocalLeaderTest.physicalSize (base d))).Accepts word ∧
      ∀ n, valid d (memoryRun d word n) (word n).val = true := by
  have h := EncodedParityConjunction.accepts_iff
    (EncodedLocalLeaderTest.physicalSize (base d),[EncodedLocalLeaderTest.monitorData (base d),safety d])
    (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl
        · exact alphabet
        · exact safety_alphabet d) word
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at h
  exact h.trans (and_congr Iff.rfl (accepts_iff d word))

end Characterisation.EncodedLeaderSafety
