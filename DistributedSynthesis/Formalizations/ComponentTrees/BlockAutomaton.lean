/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockSoundness
import DistributedSynthesis.Library.Distributed.LeaderPhases.ContinuationParity

/-! The combined block automaton in `lem:tree-combined-automaton`.
`α` is the joint environment/output letter. A block of such letters is
equivalent to a pair of length-D environment and output words. The two
supplied machines are precisely the draft's prefix-liveness recognizer and
guarded specification automaton. Their existing language theorems are not
reproved here. The minimum includes the source and excludes the endpoint.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

variable {α S : Type} [Fintype S]
variable (M : Recognizer α S) (A : DetParityAutomaton.{0,0} α) (D : Nat)

def blockPriorities : Finset Nat := insert 0 (Finset.univ.image A.priority)

def blockMinimumFrom (q : A.State) (w : BlockWord α D) : Nat :=
  rangeMin (fun t => A.priority ((w.val.take t).foldl A.step q)) 0 (D-1)

theorem blockMinimumFrom_mem (q : A.State) (w : BlockWord α D) :
    blockMinimumFrom A D q w ∈ blockPriorities A := by
  obtain ⟨t, _, attained⟩ := rangeMin_attained
    (fun t => A.priority ((w.val.take t).foldl A.step q)) 0 (D-1)
  apply Finset.mem_insert_of_mem
  rw [blockMinimumFrom, attained]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The state space is exactly S × Qφ × (χφ(Qφ) ∪ {0}). -/
def blockAutomaton : DetParityAutomaton (BlockWord α D) where
  State := S × A.State × {p : Nat // p ∈ blockPriorities A}
  stateFinite := inferInstance
  initial := (M.start, A.initial, ⟨0, Finset.mem_insert_self _ _⟩)
  step := fun q w => (M.evalFrom q.1 w.val, w.val.foldl A.step q.2.1,
    ⟨blockMinimumFrom A D q.2.1 w, blockMinimumFrom_mem A D q.2.1 w⟩)
  priority := fun q => q.2.2.val

def blockLive : Set (blockAutomaton M A D).State := {q | q.1 ∈ M.accept}

@[simp] theorem blockAutomaton_initial_priority :
    (blockAutomaton M A D).priority (blockAutomaton M A D).initial = 0 := rfl

@[simp] theorem blockAutomaton_step_priority (q : (blockAutomaton M A D).State)
    (w : BlockWord α D) :
    (blockAutomaton M A D).priority ((blockAutomaton M A D).step q w) =
      rangeMin (fun t => A.priority ((w.val.take t).foldl A.step q.2.1)) 0 (D-1) := rfl

/-- Finite-prefix version, with no assumption that a finite word has an
infinite extension. This is used for the position reachability invariant. -/
theorem blockAutomaton_finite_states (words : List (BlockWord α D)) :
    (words.foldl (blockAutomaton M A D).step (blockAutomaton M A D).initial).1 =
      M.eval ((words.map Subtype.val).flatten) ∧
    (words.foldl (blockAutomaton M A D).step (blockAutomaton M A D).initial).2.1 =
      ((words.map Subtype.val).flatten).foldl A.step A.initial := by
  induction words using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton words w ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_append, List.map_cons, List.map_nil, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil]
    change M.evalFrom _ w.val = _ ∧ w.val.foldl A.step _ = _
    rw [ih.1, ih.2]
    exact ⟨(M.evalFrom_of_append M.start _ _).symm, rfl⟩

/-- The existing fixed-length word type, with the usual decomposition of a stream. -/
def groupedWord (word : Nat → α) (D n : Nat) : BlockWord α D :=
  ⟨List.ofFn (fun i : Fin D => word (n*D+i.val)), List.length_ofFn⟩

theorem groupedWord_take (word : Nat → α) (D n t : Nat) (within : t ≤ D) :
    (groupedWord word D n).val.take t = List.ofFn (fun i : Fin t => word (n*D+i.val)) := by
  apply List.ext_getElem
  · simp [groupedWord, Nat.min_eq_left within]
  · intro i hi hj
    simp [groupedWord]

theorem blockAutomaton_run_states (word : Nat → α) (n : Nat) :
    ((blockAutomaton M A D).run (groupedWord word D) n).1 = M.eval (branchNode word (n*D)) ∧
    ((blockAutomaton M A D).run (groupedWord word D) n).2.1 =
      (branchNode word (n*D)).foldl A.step A.initial := by
  induction n with
  | zero => simp only [Nat.zero_mul]; exact ⟨rfl, rfl⟩
  | succ n ih =>
    change M.evalFrom ((blockAutomaton M A D).run (groupedWord word D) n).1
        (groupedWord word D n).val = _ ∧
      (groupedWord word D n).val.foldl A.step
        ((blockAutomaton M A D).run (groupedWord word D) n).2.1 = _
    rw [ih.1, ih.2, Nat.succ_mul]
    rw [← prefix_append_segment word (n*D) D]
    exact ⟨(M.evalFrom_of_append M.start _ _).symm, List.foldl_append.symm⟩

/-- Liveness is exact at every block boundary, including boundary zero. -/
theorem blockAutomaton_run_live (word : Nat → α) (n : Nat) :
    (blockAutomaton M A D).run (groupedWord word D) n ∈ blockLive M A D ↔
      M.eval (branchNode word (n*D)) ∈ M.accept := by
  change _ ∈ M.accept ↔ _
  rw [(blockAutomaton_run_states M A D word n).1]

/-- The priority at boundary n+1 is the minimum of rounds nD,...,(n+1)D-1. -/
theorem blockAutomaton_run_priority (positive : 0 < D) (word : Nat → α) (n : Nat) :
    (blockAutomaton M A D).priority ((blockAutomaton M A D).run (groupedWord word D) (n+1)) =
      cutBlockMin (fun t => A.priority (A.run word t)) (fun n => n*D) n := by
  change blockMinimumFrom A D ((blockAutomaton M A D).run (groupedWord word D) n).2.1 _ = _
  rw [(blockAutomaton_run_states M A D word n).2]
  unfold blockMinimumFrom cutBlockMin
  have span : (n+1)*D - n*D - 1 = D-1 := by simp [Nat.add_mul]
  rw [span]
  apply rangeMin_congr
  intro t within
  simp only [Nat.zero_add]
  rw [groupedWord_take word D n t (by omega), ← List.foldl_append,
    prefix_append_segment word (n*D) t, branchNode_fold_runFrom]
  rfl

/-- Acceptance for ALL executions, not just for executions of a chosen
strategy. Finite-block minima and the extra initial zero preserve parity. -/
theorem blockAutomaton_accepts (positive : 0 < D) (word : Nat → α) :
    (blockAutomaton M A D).Accepts (groupedWord word D) ↔ A.Accepts word := by
  rw [(blockAutomaton M A D).accepts_iff_natSeqMinEvenParity,
    A.accepts_iff_natSeqMinEvenParity]
  rw [← natSeqMinEvenParity_shift
    (fun n => (blockAutomaton M A D).priority
      ((blockAutomaton M A D).run (groupedWord word D) n)) 1]
  simp only [Nat.add_comm 1, blockAutomaton_run_priority M A D positive word]
  exact natSeqMinEvenParity_cutBlockMin (fun n => A.priority (A.run word n))
    (fun _ _ h => Nat.mul_lt_mul_of_pos_right h positive) (by simp)

end Characterisation.ComponentTrees
