/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ExecutionSafety
import DistributedSynthesis.Library.Distributed.GraphAdversaries.SafetyClosure

/-!
# Safety and closure of the adversary

Manuscript source label: `lem:safety:is:safe`.

## Paper statement

Let~$\phi$ be a safety formula and let~$f$ be a distributed algorithm.
    Then~$f$ realizes~$\phi$ under~$A$ if and only if it realizes~$\phi$ under~$\overline{A}$.

## Reading the proof

See the [proof locations](PROOFS.md#safety-and-closure-of-the-adversary) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.SafetyClosure

universe u_1 u_2

/-- Reuses `Characterisation.safety_closure_transfer`. -/
theorem safety_closure_transfer :
    ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [DiscreteTopology α]
      (A : Set (ℕ → α)) (run : (ℕ → α) → ℕ → β),
      Causal run → ∀ (S : Set (ℕ → β)), IsSafety S → ((∀ x ∈ A, run x ∈ S) ↔ ∀ x ∈ closure A, run x ∈ S) :=
  @_root_.Characterisation.safety_closure_transfer

/-- Reuses `Characterisation.actual_execution_causal`. -/
theorem actual_execution_causal :
    ∀ {O₁ : Type u_1} {O₂ : Type u_2} (σ : StrategyPair Unit Unit O₁ O₂),
      Causal fun (x : ℕ → Graph) => execution σ (GraphExecutions.ofGraphs x) :=
  @_root_.Characterisation.actual_execution_causal


/-- The same fixed distributed algorithm realizes the safety language under
A exactly when it realizes it under the closure of A. -/
theorem same_strategy_closure {O₁ O₂ : Type*}
    [TopologicalSpace Graph] [DiscreteTopology Graph]
    (A : Set (Nat → Graph)) (f : StrategyPair Unit Unit O₁ O₂)
    (S : Set (Nat → RoundRecord Unit Unit Graph O₁ O₂)) (safe : IsSafety S) :
    (∀ h ∈ A, execution f (GraphExecutions.ofGraphs h) ∈ S) ↔
      ∀ h ∈ closure A, execution f (GraphExecutions.ofGraphs h) ∈ S :=
  safety_closure_transfer A _ (actual_execution_causal f) S safe

end DistributedSynthesis.Paper.SafetyClosure
