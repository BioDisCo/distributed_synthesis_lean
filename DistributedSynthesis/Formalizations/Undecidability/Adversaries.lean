/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.GraphAdversaries.SafetyClosure
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.GuardedRestart
import Mathlib.Topology.GDelta.Basic

/-! Exact topological statements from the undecidability section of main.tex.
The geometric, causal, and restart constructions are reused unchanged. -/
namespace Characterisation
open DistributedSynthesis

/-- Lemma guarded-safety-reduction for arbitrary safety objectives and the
paper's actual distributed strategies, with both constructions explicit in
the reused `guarded_restart_iff`. -/
theorem guarded_safety_reduction {O₁ O₂ : Type*} (A : Set (Nat → Graph))
    (h : List Graph) (dense : PrefixDense (Residual A h))
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) (safety : IsSafety S) :
    RealizesSafety Set.univ S ↔
    (∃ τ : StrategyPair Unit Unit O₁ O₂,
      ∀ y ∈ A, graphPrefix y h.length = h →
        OmegaWord.drop (execution τ (GraphExecutions.ofGraphs y)) h.length ∈ S) := by
  exact (actual_safety_realizability_transfer (Residual A h) dense S safety).symm.trans
    (guarded_restart_iff A h S)

/-- Lemma nowhere-dense-live, with every prefix quantified as in main.tex,
including prefixes that are already nonlive. -/
theorem nowhere_dense_iff_missing_extension (A : Set (Nat → Graph)) :
    IsNowhereDense (geometricMap '' A) ↔
      ∀ h : List Graph, ∃ k : List Graph, ¬ LivePrefix A (h ++ k) := by
  change interior (closure (geometricMap '' A)) = ∅ ↔ _
  rw [← geometricHoles_iff, geometric_holes_iff_prefix_holes]
  constructor
  · intro holes h
    by_cases live : LivePrefix A h
    · exact holes h live
    · exact ⟨[],by simpa using live⟩
  · intro holes h _
    exact holes h

/-- Lemma not:nowhere:dense:is:dense:somewhere, in the standard discrete
product topology on graph sequences. No omega-regularity premise is needed. -/
theorem non_nowhere_dense_has_dense_residual
    [TopologicalSpace Graph] [DiscreteTopology Graph] (A : Set (Nat → Graph))
    (notDense : ¬ IsNowhereDense (geometricMap '' A)) :
    ∃ h : List Graph, Dense (Residual A h) := by
  obtain ⟨h,dense⟩ := no_geometric_holes_has_prefixDense_residual A
    (fun holes => notDense ((geometricHoles_iff A).mp holes))
  exact ⟨h,(prefixDense_iff_dense _).mp dense⟩

/-- A finite graph-prefix guard followed by a fixed shift preserves safety.
This justifies applying the closure lemma to the guarded formula in the
English reverse implication. -/
theorem guarded_objective_safety {O₁ O₂ : Type*} (h : List Graph)
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) (safety : IsSafety S) :
    IsSafety {w | graphPrefix (fun n => (w n).graph) h.length = h →
      OmegaWord.drop w h.length ∈ S} := by
  intro x bad
  obtain ⟨prefixEq,violates⟩ := Classical.not_imp.mp bad
  obtain ⟨n,forbidden⟩ := safety _ violates
  refine ⟨h.length+n,?_⟩
  intro y agree good
  have samePrefix : graphPrefix (fun k => (y k).graph) h.length =
      graphPrefix (fun k => (x k).graph) h.length := by
    unfold graphPrefix
    congr 1
    funext i
    exact congrArg (fun r => r.graph) (agree i.val (by have := i.isLt; omega)).symm
  apply forbidden (OmegaWord.drop y h.length) _ (good (samePrefix.trans prefixEq))
  intro t ht
  exact agree (h.length+t) (by omega)

/-- Prefixing by a fixed finite history is continuous in the product topology. -/
theorem continuous_prependGraphs [TopologicalSpace Graph] (h : List Graph) :
    Continuous (prependGraphs h) := by
  apply continuous_pi
  intro n
  by_cases before : n < h.length
  · simpa only [prependGraphs,if_pos before] using
      (continuous_const : Continuous (fun _ : Nat → Graph => h.getD n Graph.both))
  · simpa only [prependGraphs,if_neg before] using continuous_apply (n-h.length)

/-- The density hypothesis in the manuscript puts the entire cylinder
below `h` into the closure of the original adversary. -/
theorem prefixed_mem_closure_of_dense_residual
    [TopologicalSpace Graph] (A : Set (Nat → Graph)) (h : List Graph)
    (dense : Dense (Residual A h)) (x : Nat → Graph) :
    prependGraphs h x ∈ closure A := by
  exact map_mem_closure (continuous_prependGraphs h) (dense x) (fun _ hx => hx)

/-- The topological prefix chosen in the English reduction really supports
every infinite suffix in the closure. No regularity of the adversary is used. -/
theorem non_nowhere_dense_has_closed_cone
    [TopologicalSpace Graph] [DiscreteTopology Graph] (A : Set (Nat → Graph))
    (notDense : ¬ IsNowhereDense (geometricMap '' A)) :
    ∃ h : List Graph, ∀ x : Nat → Graph, prependGraphs h x ∈ closure A := by
  obtain ⟨h,dense⟩ := non_nowhere_dense_has_dense_residual A notDense
  exact ⟨h,prefixed_mem_closure_of_dense_residual A h dense⟩

/-- The guarded reduction through the manuscript's closure argument:
extend the same strategy to the closure, then seed it with the fixed history.
The reverse implication uses safety of the guarded objective explicitly. -/
theorem guarded_safety_reduction_of_dense
    [TopologicalSpace Graph] [DiscreteTopology Graph]
    {O₁ O₂ : Type*} (A : Set (Nat → Graph)) (h : List Graph)
    (dense : Dense (Residual A h))
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) (safety : IsSafety S) :
    RealizesSafety Set.univ S ↔
    (∃ τ : StrategyPair Unit Unit O₁ O₂,
      ∀ y ∈ A, graphPrefix y h.length = h →
        OmegaWord.drop (execution τ (GraphExecutions.ofGraphs y)) h.length ∈ S) := by
  constructor
  · rintro ⟨σ,win⟩
    exact (guarded_restart_iff A h S).mp ⟨σ,fun x _ => win x (Set.mem_univ x)⟩
  · rintro ⟨τ,win⟩
    let T : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂) :=
      {w | graphPrefix (fun n => (w n).graph) h.length = h → OmegaWord.drop w h.length ∈ S}
    have winA : ∀ y ∈ A, execution τ (GraphExecutions.ofGraphs y) ∈ T := by
      intro y hy
      simpa only [T,Set.mem_setOf_eq,GraphExecutions.execution_graph,GraphExecutions.ofGraphs]
        using win y hy
    have winClosure := (safety_closure_transfer A
      (fun x => execution τ (GraphExecutions.ofGraphs x)) (actual_execution_causal τ)
      T (guarded_objective_safety h S safety)).mp winA
    refine ⟨seedStrategy h τ,fun x _ => ?_⟩
    rw [seedStrategy_execution]
    have wins := winClosure (prependGraphs h x)
      (prefixed_mem_closure_of_dense_residual A h dense x)
    apply wins
    simpa only [GraphExecutions.execution_graph,GraphExecutions.ofGraphs] using
      prependGraphs_prefix h x

end Characterisation
