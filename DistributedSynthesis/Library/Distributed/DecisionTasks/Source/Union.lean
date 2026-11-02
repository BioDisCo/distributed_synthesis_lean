/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.PriorityPairMonitor
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Parity
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.ParityCommit

/-! # Task-monitor interface to the shared parity-family compiler

The memory, transition, priorities, and combination correctness are supplied by
`PriorityPairMonitor`, using `EncodedParityFamilies`. This file only translates
the task proof's acceptance notation and Boolean combinations.
-/

set_option autoImplicit false

namespace DistributedSynthesis.DecisionTasks.Source.ParityUnion

open DistributedSynthesis.DecisionTasks.Source.FiniteParity

abbrev UnionMemory := PriorityPairMonitor.Memory
abbrev initial := PriorityPairMonitor.initial
abbrev unionUpdate := PriorityPairMonitor.update
abbrev unionPriority := PriorityPairMonitor.priority
abbrev unionRun := PriorityPairMonitor.run
abbrev combined := PriorityPairMonitor.combined
abbrev unionBound := PriorityPairMonitor.bound

theorem priority_bound (b₁ b₂ : ℕ) (m : UnionMemory b₁ b₂) (x : ℕ × ℕ) :
    unionPriority b₁ b₂ m x ≤ unionBound b₁ b₂ :=
  PriorityPairMonitor.priority_le b₁ b₂ m x

theorem union_correct {b₁ b₂ : ℕ} {c₁ c₂ : ℕ → ℕ}
    (h₁ : ∀ n, c₁ n ≤ b₁) (h₂ : ∀ n, c₂ n ≤ b₂) :
    ColourWins (combined b₁ b₂ c₁ c₂) false ↔
      ColourWins c₁ false ∨ ColourWins c₂ false := by
  simp only [colourWins_false_iff]
  exact PriorityPairMonitor.combined_correct h₁ h₂

theorem combined_bound (b₁ b₂ : ℕ) (c₁ c₂ : ℕ → ℕ)
    (n : ℕ) : combined b₁ b₂ c₁ c₂ n ≤ unionBound b₁ b₂ :=
  priority_bound _ _ _ _

/-- Direct branch condition for the task monitor's implication. -/
theorem implication_correct {bAdv bClauses : ℕ} {adv clauses : ℕ → ℕ}
    (hAdv : ∀ n, adv n ≤ bAdv) (hClauses : ∀ n, clauses n ≤ bClauses) :
    ColourWins (combined (bAdv + 1) bClauses (fun n => adv n + 1) clauses) false ↔
      (ColourWins adv false → ColourWins clauses false) := by
  classical
  rw [union_correct (fun n => Nat.add_le_add_right (hAdv n) 1) hClauses,
    colourWins_succ hAdv, imp_iff_not_or]

abbrev MeetMemory (b₁ b₂ : ℕ) := UnionMemory (b₁ + 1) (b₂ + 1)

/-- Conjunction uses disjunction and the parity shift implementing negation. -/
def meet (b₁ b₂ : ℕ) (c₁ c₂ : ℕ → ℕ) : ℕ → ℕ :=
  fun n => combined (b₁ + 1) (b₂ + 1) (fun k => c₁ k + 1) (fun k => c₂ k + 1) n + 1

theorem meet_correct {b₁ b₂ : ℕ} {c₁ c₂ : ℕ → ℕ}
    (h₁ : ∀ n, c₁ n ≤ b₁) (h₂ : ∀ n, c₂ n ≤ b₂) :
    ColourWins (meet b₁ b₂ c₁ c₂) false ↔
      ColourWins c₁ false ∧ ColourWins c₂ false := by
  classical
  have hb : ∀ n, combined (b₁ + 1) (b₂ + 1) (fun k => c₁ k + 1) (fun k => c₂ k + 1) n ≤
      unionBound (b₁ + 1) (b₂ + 1) := combined_bound _ _ _ _
  show ColourWins (fun n =>
    combined (b₁ + 1) (b₂ + 1) (fun k => c₁ k + 1) (fun k => c₂ k + 1) n + 1) false ↔ _
  rw [colourWins_succ hb,
    union_correct (fun n => Nat.succ_le_succ (h₁ n)) (fun n => Nat.succ_le_succ (h₂ n)),
    colourWins_succ h₁, colourWins_succ h₂]
  tauto

end DistributedSynthesis.DecisionTasks.Source.ParityUnion
