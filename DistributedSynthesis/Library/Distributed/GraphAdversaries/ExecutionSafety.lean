/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Safety
import DistributedSynthesis.Library.Distributed.GraphExecutions

/-! Safety transfer specialized to the original distributed strategies and
execution semantics. Inputs are singletons; output alphabets are arbitrary. -/

namespace Characterisation

open DistributedSynthesis

variable {O₁ O₂ : Type*}

theorem actual_execution_causal (σ : StrategyPair Unit Unit O₁ O₂) :
    Causal (fun x => execution σ (GraphExecutions.ofGraphs x)) := by
  intro x y n agree t ht
  have envEq : ∀ k, k < n →
      GraphExecutions.ofGraphs x k = GraphExecutions.ofGraphs y k := by
    intro k hk
    simp only [GraphExecutions.ofGraphs, agree k hk]
  have prefixEq := executionPrefix_congr_of_env_eq_lt σ
    (n := t) (fun k hk => envEq k (Nat.lt_trans hk ht))
  simp only [execution_apply, prefixEq, envEq t ht]

def RealizesSafety (A : Set (Nat → Graph))
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) : Prop :=
  ∃ σ : StrategyPair Unit Unit O₁ O₂,
    ∀ x ∈ A, execution σ (GraphExecutions.ofGraphs x) ∈ S

theorem actual_safety_realizability_transfer
    (A : Set (Nat → Graph)) (dense : PrefixDense A)
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) (safety : IsSafety S) :
    RealizesSafety A S ↔ RealizesSafety Set.univ S := by
  constructor
  · rintro ⟨σ, win⟩
    refine ⟨σ, fun x _ => ?_⟩
    exact (safety_transfer A dense _ (actual_execution_causal σ) S safety).mp win x
  · rintro ⟨σ, win⟩
    exact ⟨σ, fun x _ => win x (Set.mem_univ x)⟩

theorem eventual_both_actual_realizability
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) (safety : IsSafety S) :
    RealizesSafety {x | ∃ N, ∀ t, N ≤ t → x t = Graph.both} S ↔
      RealizesSafety Set.univ S :=
  actual_safety_realizability_transfer _
    (eventually_constant_prefixDense Graph.both) S safety

end Characterisation
