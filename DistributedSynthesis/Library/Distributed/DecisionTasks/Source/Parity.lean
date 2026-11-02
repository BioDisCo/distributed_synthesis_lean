/- Decision-task compatibility notation over the shared automata library. -/

import DistributedSynthesis.Library.Automata.RunTreeNonemptiness

/-!
The task proof uses the shared run-based parity tree automaton and the existing
finite-policy/finite-orbit nonemptiness procedure. Only the source proof's
priority notation and tree-address abbreviations remain here; there is no
separate parity game, tree-automaton structure, or regular-tree construction.
-/

namespace DistributedSynthesis.DecisionTasks.Source.FiniteParity

/-- A predicate holds infinitely often when it holds beyond every finite index. -/
def InfOften (P : ℕ → Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ P n

/-- Deleting a finite prefix preserves infinite occurrence. -/
theorem infOften_shift (P : ℕ → Prop) (k : ℕ) :
    InfOften (fun n => P (k + n)) ↔ InfOften P := by
  constructor
  · intro h N
    obtain ⟨n, hn, hp⟩ := h N
    exact ⟨k + n, by omega, hp⟩
  · intro h N
    obtain ⟨n, hn, hp⟩ := h (k + N)
    refine ⟨n - k, by omega, ?_⟩
    simpa [Nat.add_sub_of_le (show k ≤ n by omega)] using hp

/-- A predicate which does not recur is eventually always false. -/
theorem not_infOften (P : ℕ → Prop) :
    ¬ InfOften P ↔ ∃ N, ∀ n, N ≤ n → ¬ P n := by
  classical
  simp only [InfOften, not_forall, not_exists, not_and]

/-- Parity winning stated directly for a sequence of priorities. -/
def ColourWins (c : ℕ → ℕ) (p : Bool) : Prop :=
  ∃ d, (InfOften (fun n => c n = d) ∧
    ∀ e, InfOften (fun n => c n = e) → d ≤ e) ∧ decide (d % 2 = 1) = p

/-- The source priority convention is the library's min-even condition. -/
theorem colourWins_false_iff (c : ℕ → ℕ) :
    ColourWins c false ↔ DistributedSynthesis.NatSeqMinEvenParity c := by
  simp only [ColourWins, InfOften, DistributedSynthesis.NatSeqMinEvenParity,
    DistributedSynthesis.NatSeqSeenInfinitelyOften]
  apply exists_congr
  intro d
  have heven : decide (d % 2 = 1) = false ↔
      DistributedSynthesis.DetParityAutomaton.NatEven d := by
    simp only [decide_eq_false_iff_not, DistributedSynthesis.DetParityAutomaton.NatEven]
    constructor
    · intro h
      exact ⟨d / 2, by omega⟩
    · rintro ⟨k, rfl⟩
      omega
  rw [heven]
  tauto

namespace TreeAutomaton

/-- Source notation for the shared finite-word tree addresses. -/
abbrev Node (k : ℕ) := DistributedSynthesis.TreeNode (Fin k)

/-- Source notation for the shared branch-prefix recursion. -/
abbrev branchNode {k : ℕ} (b : ℕ → Fin k) := DistributedSynthesis.branchNode b

end TreeAutomaton
end DistributedSynthesis.DecisionTasks.Source.FiniteParity
