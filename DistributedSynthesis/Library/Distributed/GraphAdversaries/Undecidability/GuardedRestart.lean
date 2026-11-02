/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.RestartViews

namespace Characterisation
open DistributedSynthesis FullViewPath GraphExecutions

private theorem prefix_agrees (x : Nat → Graph) (n : Nat) :
    BlockEmbedding.graphPrefix x n = graphPrefix x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [BlockEmbedding.prefix_succ, graphPrefix_succ, ih]

private theorem prepend_prefix_add (h : List Graph) (x : Nat → Graph) (n : Nat) :
    graphPrefix (prependGraphs h x) (h.length + n) = h ++ graphPrefix x n := by
  rw [graphPrefix_split, prependGraphs_prefix, prependGraphs_drop]

private theorem outputs_at {O₁ O₂ : Type*} (σ : StrategyPair Unit Unit O₁ O₂)
    (x : Nat → Graph) (n : Nat) :
    (execution σ (ofGraphs x) n).outputOne = σ.one (evaluate (graphPrefix x (n+1))).one ∧
    (execution σ (ofGraphs x) n).outputTwo = σ.two (evaluate (graphPrefix x (n+1))).two := by
  simpa only [ofGraphs, prefix_agrees] using execution_outputs σ (ofGraphs x) n

private theorem record_eq {O₁ O₂ : Type*}
    (r s : RoundRecord Unit Unit Graph O₁ O₂)
    (hg : r.graph = s.graph) (h₁ : r.outputOne = s.outputOne)
    (h₂ : r.outputTwo = s.outputTwo) : r = s := by
  cases r; cases s
  simp_all

/-- Simulating a past reproduces exactly the suffix of the original execution. -/
theorem seedStrategy_execution {O₁ O₂ : Type*} (h : List Graph)
    (σ : StrategyPair Unit Unit O₁ O₂) (x : Nat → Graph) :
    execution (seedStrategy h σ) (ofGraphs x) =
      OmegaWord.drop (execution σ (ofGraphs (prependGraphs h x))) h.length := by
  funext n
  apply record_eq
  · simp only [OmegaWord.drop, execution_graph, ofGraphs]
    simp [prependGraphs]
  · have a := (outputs_at (seedStrategy h σ) x n).1
    have b := (outputs_at σ (prependGraphs h x) (h.length + n)).1
    rw [Nat.add_assoc, prepend_prefix_add] at b
    simp only [OmegaWord.drop]
    rw [a, b]
    exact congrArg σ.one (seedView_evaluate h _).1
  · have a := (outputs_at (seedStrategy h σ) x n).2
    have b := (outputs_at σ (prependGraphs h x) (h.length + n)).2
    rw [Nat.add_assoc, prepend_prefix_add] at b
    simp only [OmegaWord.drop]
    rw [a, b]
    exact congrArg σ.two (seedView_evaluate h _).2

/-- Erasing a past reproduces exactly a fresh execution of the source strategy. -/
theorem resetStrategy_execution {O₁ O₂ : Type*} (h : List Graph)
    (σ : StrategyPair Unit Unit O₁ O₂) (x : Nat → Graph) :
    OmegaWord.drop (execution (resetStrategy h.length σ)
      (ofGraphs (prependGraphs h x))) h.length = execution σ (ofGraphs x) := by
  funext n
  apply record_eq
  · simp only [OmegaWord.drop, execution_graph, ofGraphs]
    simp [prependGraphs]
  · have a := (outputs_at (resetStrategy h.length σ) (prependGraphs h x) (h.length+n)).1
    rw [Nat.add_assoc, prepend_prefix_add, (resetStrategy_evaluate h _ σ).1] at a
    simp only [OmegaWord.drop, a, (outputs_at σ x n).1]
  · have a := (outputs_at (resetStrategy h.length σ) (prependGraphs h x) (h.length+n)).2
    rw [Nat.add_assoc, prepend_prefix_add, (resetStrategy_evaluate h _ σ).2] at a
    simp only [OmegaWord.drop, a, (outputs_at σ x n).2]

/-- Semantic guarded restart for an arbitrary objective on execution words.
The guard is part of the objective; the processes need not decide it. -/
theorem guarded_restart_iff {O₁ O₂ : Type*} (A : Set (Nat → Graph)) (h : List Graph)
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) :
    (∃ σ : StrategyPair Unit Unit O₁ O₂,
      ∀ x ∈ Residual A h, execution σ (ofGraphs x) ∈ S) ↔
    (∃ τ : StrategyPair Unit Unit O₁ O₂,
      ∀ y ∈ A, graphPrefix y h.length = h →
        OmegaWord.drop (execution τ (ofGraphs y)) h.length ∈ S) := by
  constructor
  · rintro ⟨σ, hs⟩
    refine ⟨resetStrategy h.length σ, ?_⟩
    intro y hy hp
    have he := prepend_drop_of_prefix y h hp
    have hx : OmegaWord.drop y h.length ∈ Residual A h := by
      change prependGraphs h (OmegaWord.drop y h.length) ∈ A
      rwa [he]
    have eq := resetStrategy_execution h σ (OmegaWord.drop y h.length)
    rw [he] at eq
    rw [eq]
    exact hs _ hx
  · rintro ⟨τ, ht⟩
    refine ⟨seedStrategy h τ, ?_⟩
    intro x hx
    rw [seedStrategy_execution]
    exact ht _ hx (prependGraphs_prefix h x)

end Characterisation
