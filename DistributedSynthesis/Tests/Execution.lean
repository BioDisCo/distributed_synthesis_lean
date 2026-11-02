/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Execution

/-! Standalone clients: this import supplies no parity-game certificate API. -/
namespace DistributedSynthesis.Tests.Execution
open DistributedSynthesis

universe u v x y
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

example (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) (t : Nat) :
    History.length (executionPrefix σ env t) = t :=
  executionPrefix_length σ env t

/-- Each output is chosen from the view after receiving this round's input
and any delivered message, not from the pre-round view. -/
example (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) (t : Nat) :
    (execution σ env t).outputOne =
      σ.one (nextView Proc.one (executionPrefix σ env t) (env t)) := by
  rw [execution_apply, nextRound_outputOne]

example (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    StrategyGeneratedPrefix σ h ↔
      ∃ envs : List (EnvironmentRound In₁ In₂), h = executionPrefixFromList σ envs :=
  strategyGeneratedPrefix_iff_exists_executionPrefixFromList σ h

example (φ : Specification In₁ In₂ Out₁ Out₂) :
    SynthesisProblem φ ↔ ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂, φ (execution σ env) := Iff.rfl

end DistributedSynthesis.Tests.Execution
