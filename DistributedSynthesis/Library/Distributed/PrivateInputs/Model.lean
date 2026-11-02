/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Execution
import DistributedSynthesis.Library.Logic.LTL
import Mathlib.Tactic

/-! # Two processes with private inputs and no communication

The graph alphabet is a singleton representing the empty graph. A local view
is the complete private input word. Round records reuse the existing generic
`RoundRecord`, and outputs follow the current input, as in the communication
model. No legality assumption or encoding is built into this model.
-/

namespace DistributedSynthesis.PrivateInputs

/-- The unique graph has no edge between the processes. -/
abbrev EmptyGraph := Unit
/-- A process observes exactly its finite private input history. -/
abbrev LocalView (I : Type*) := List I

/-- The environment chooses one input value for each process in each round. -/
structure EnvironmentRound (I₁ I₂ : Type*) where
  inputOne : I₁
  inputTwo : I₂

abbrev EnvironmentSequence (I₁ I₂ : Type*) := Nat → EnvironmentRound I₁ I₂

/-- Two deterministic strategies with unrestricted perfect recall. Each output
depends only on that process's input history, including the current input. -/
structure StrategyPair (I₁ I₂ O₁ O₂ : Type*) where
  one : LocalView I₁ → O₁
  two : LocalView I₂ → O₂

def inputPrefix {I : Type*} (x : Nat → I) : Nat → List I
  | 0 => []
  | n+1 => inputPrefix x n ++ [x n]

@[simp] theorem prefix_length {I : Type*} (x : Nat → I) (n : Nat) :
    (inputPrefix x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [inputPrefix, ih]

theorem prefix_map {I J : Type*} (f : I → J) (x : Nat → I) (n : Nat) :
    inputPrefix (fun t ↦ f (x t)) n = (inputPrefix x n).map f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [inputPrefix, ih]

abbrev Letter (I₁ I₂ O₁ O₂ : Type*) := RoundRecord I₁ I₂ EmptyGraph O₁ O₂

/-- At round `t`, each strategy receives its first `t + 1` private inputs.
The resulting infinite word records both current inputs and both outputs. -/
def execution {I₁ I₂ O₁ O₂ : Type*} (σ : StrategyPair I₁ I₂ O₁ O₂)
    (env : EnvironmentSequence I₁ I₂) : OmegaWord (Letter I₁ I₂ O₁ O₂) :=
  fun t ↦ ⟨(env t).inputOne, (env t).inputTwo, (),
    σ.one (inputPrefix (fun k ↦ (env k).inputOne) (t+1)),
    σ.two (inputPrefix (fun k ↦ (env k).inputTwo) (t+1))⟩

def executionPrefix {I₁ I₂ O₁ O₂ : Type*} (σ : StrategyPair I₁ I₂ O₁ O₂)
    (env : EnvironmentSequence I₁ I₂) (n : Nat) : List (Letter I₁ I₂ O₁ O₂) :=
  inputPrefix (execution σ env) n

@[simp] theorem executionPrefix_length {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    (executionPrefix σ env n).length = n := prefix_length _ _

@[simp] theorem executionPrefix_succ {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    executionPrefix σ env (n+1) = executionPrefix σ env n ++ [execution σ env n] := rfl

abbrev Specification (I₁ I₂ O₁ O₂ : Type*) := OmegaWord (Letter I₁ I₂ O₁ O₂) → Prop

/-- The fixed strategies satisfy the specification for every pair of private
input streams. The two streams are universally quantified without a constraint
relating them. -/
def Realizes {I₁ I₂ O₁ O₂ : Type*} (φ : Specification I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) : Prop := ∀ env, φ (execution σ env)

/-- There exist two local strategies that satisfy the specification against
every environment input sequence, with no communication between the processes. -/
def SynthesisProblem {I₁ I₂ O₁ O₂ : Type*} (φ : Specification I₁ I₂ O₁ O₂) : Prop :=
  ∃ σ, Realizes φ σ

end DistributedSynthesis.PrivateInputs
