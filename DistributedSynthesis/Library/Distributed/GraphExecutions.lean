/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Execution
import DistributedSynthesis.Library.Distributed.BlockEmbedding

/-! # Graph histories and actual singleton-input executions

This adapter connects the lightweight view-path APIs to the original execution
semantics for arbitrary output types. It deliberately imports `Execution`;
the combinatorial projection modules do not acquire that dependency.
-/

namespace DistributedSynthesis.GraphExecutions
open FullViewPath BlockEmbedding

def ofGraphs (source : Nat → Graph) : EnvironmentSequence Unit Unit :=
  fun t ↦ ⟨(), (), source t⟩

def extend (h : List Graph) : EnvironmentSequence Unit Unit :=
  ofGraphs (fun t ↦ h.getD t .both)

theorem execution_graphs {O₁ O₂ : Type*} (σ : StrategyPair Unit Unit O₁ O₂)
    (env : EnvironmentSequence Unit Unit) (t : Nat) :
    History.graphSequence (executionPrefix σ env t) = graphPrefix (fun k ↦ (env k).graph) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [executionPrefix_succ, History.graphSequence_append, prefix_succ, ih]
    rfl

/-- The pair of local views at depth `t` is independent of the chosen outputs. -/
theorem execution_views {O₁ O₂ : Type*} (σ : StrategyPair Unit Unit O₁ O₂)
    (env : EnvironmentSequence Unit Unit) (t : Nat) :
    viewPair (executionPrefix σ env t) =
      ((evaluate (graphPrefix (fun k ↦ (env k).graph) t)).one,
       (evaluate (graphPrefix (fun k ↦ (env k).graph) t)).two) := by
  rw [← execution_graphs σ env t]
  exact (evaluate_graphSequence _).symm

/-- Reception precedes output: word position `t` uses the views at depth `t+1`. -/
theorem execution_outputs {O₁ O₂ : Type*} (σ : StrategyPair Unit Unit O₁ O₂)
    (env : EnvironmentSequence Unit Unit) (t : Nat) :
    (execution σ env t).outputOne =
      σ.one (evaluate (graphPrefix (fun k ↦ (env k).graph) (t+1))).one ∧
    (execution σ env t).outputTwo =
      σ.two (evaluate (graphPrefix (fun k ↦ (env k).graph) (t+1))).two := by
  have hv := execution_views σ env (t+1)
  have h₁ := congrArg Prod.fst hv
  have h₂ := congrArg Prod.snd hv
  change currentView .one (executionPrefix σ env (t+1)) = _ at h₁
  change currentView .two (executionPrefix σ env (t+1)) = _ at h₂
  rw [currentView_executionPrefix_succ] at h₁ h₂
  rw [execution_apply]
  exact ⟨congrArg σ.one h₁, congrArg σ.two h₂⟩

theorem execution_graph {O₁ O₂ : Type*} (σ : StrategyPair Unit Unit O₁ O₂)
    (env : EnvironmentSequence Unit Unit) (t : Nat) :
    (execution σ env t).graph = (env t).graph := by rw [execution_apply]; rfl

theorem extend_prefix (h : List Graph) (t : Nat) (ht : t ≤ h.length) :
    graphPrefix (fun k ↦ (extend h k).graph) t = h.take t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [prefix_succ, ih (by omega)]
    change h.take t ++ [h.getD t .both] = h.take (t+1)
    rw [List.take_add_one, List.getD, List.getElem?_eq_getElem (by omega : t < h.length)]
    rfl

theorem extend_fault (before after : List Graph) (g : Graph) :
    (extend (before ++ [g] ++ after) before.length).graph = g := by
  simp [extend, ofGraphs, List.getD, List.getElem?_append]

/-- Every nonempty finite graph history is realized as the view prefix of an
actual infinite execution, with no restriction on the strategy pair. -/
theorem extend_outputs {O₁ O₂ : Type*} (σ : StrategyPair Unit Unit O₁ O₂)
    (h : List Graph) (hn : 0 < h.length) :
    (execution σ (extend h) (h.length-1)).outputOne = σ.one (evaluate h).one ∧
    (execution σ (extend h) (h.length-1)).outputTwo = σ.two (evaluate h).two := by
  have he := execution_outputs σ (extend h) (h.length-1)
  rw [show h.length-1+1 = h.length by omega, extend_prefix h h.length le_rfl,
    List.take_length] at he
  exact he

theorem graphPrefix_add (source : Nat → Graph) (t d : Nat) :
    graphPrefix source (t+d) = graphPrefix source t ++ graphPrefix (fun k ↦ source (t+k)) d := by
  induction d with
  | zero => simp [graphPrefix]
  | succ d ih =>
    rw [Nat.add_succ, prefix_succ, ih, prefix_succ]
    simp only [List.append_assoc]

end DistributedSynthesis.GraphExecutions
