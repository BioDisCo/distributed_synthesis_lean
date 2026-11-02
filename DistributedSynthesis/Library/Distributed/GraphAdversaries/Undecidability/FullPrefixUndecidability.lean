/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ExecutionSafety
import DistributedSynthesis.Library.Computability.CounterMachines.Source
import DistributedSynthesis.Formalizations.Theorem.ThmCounterMachineEncodedUndecidability

/-! Unconditional encoded LTL undecidability for every adversary preserving
all finite graph prefixes. This imports the real counter-machine source
theorem and compiler, rather than postulating either reduction endpoint. -/

namespace Characterisation

open DistributedSynthesis DistributedSynthesis.CounterMachine
open DistributedSynthesis.CounterMachine.ResidueLTL

theorem counter_conditions_safety {Q : Type*} [Fintype Q] [DecidableEq Q]
    (M : Machine Q) : IsSafety {w | Conditions M w} := by
  intro x hx
  change ¬ Conditions M x at hx
  simp only [Conditions, not_and_or, not_forall] at hx
  rcases hx with bad | ⟨n, bad⟩ | ⟨n, bad⟩ | ⟨n, bad⟩ | ⟨n, bad⟩
  · refine ⟨1, fun y eqPrefix hy => ?_⟩
    apply bad
    rw [eqPrefix 0 (by omega)]
    exact hy.1
  · refine ⟨n + 1, fun y eqPrefix hy => ?_⟩
    apply bad
    rw [eqPrefix n (by omega)]
    exact hy.2.1 n
  · refine ⟨n + 2, fun y eqPrefix hy => ?_⟩
    apply bad
    rw [eqPrefix n (by omega), eqPrefix (n + 1) (by omega)]
    exact hy.2.2.1 n
  · obtain ⟨prefixRight, bad⟩ := bad
    refine ⟨n + 1, fun y eqPrefix hy => ?_⟩
    apply bad
    rw [eqPrefix n (by omega)]
    apply hy.2.2.2.1 n
    intro k hk
    rw [← eqPrefix k (by omega)]
    exact prefixRight k hk
  · obtain ⟨prefixLeft, bad⟩ := bad
    refine ⟨n + 1, fun y eqPrefix hy => ?_⟩
    apply bad
    rw [eqPrefix n (by omega)]
    apply hy.2.2.2.2 n
    intro k hk
    rw [← eqPrefix k (by omega)]
    exact prefixLeft k hk

def RestrictedEncodedRealizable (A : Set (Nat → Graph)) (I : Compiler.Instance) : Prop :=
  ∃ σ : StrategyPair Unit Unit (Output (Fin (I.1 + 1))) (Output (Fin (I.1 + 1))),
    ∀ x ∈ A, LTL.Satisfies FiniteLetterLTL.interp
      (fun n => Compiler.raw (execution σ (GraphExecutions.ofGraphs x) n))
      (EncodedFiniteLTL.decode I.2)

theorem environment_of_graphs (env : EnvironmentSequence Unit Unit) :
    GraphExecutions.ofGraphs (fun n => (env n).graph) = env := by
  funext n
  cases he : env n with
  | mk a b g => cases a; cases b; simp [GraphExecutions.ofGraphs, he]

theorem compiled_restricted_iff (A : Set (Nat → Graph)) (dense : PrefixDense A)
    (P : MM2.Program) :
    RestrictedEncodedRealizable A (Compiler.compileInstance P) ↔ ¬ MM2.ZeroHalts P := by
  rw [← Compiler.compiled_realizable_iff P]
  constructor
  · rintro ⟨σ, win⟩
    have conditions : ∀ x ∈ A,
        Conditions (MM2.compile P) (execution σ (GraphExecutions.ofGraphs x)) := by
      intro x hx
      exact (Compiler.compiled_formula_iff_conditions P _).mp (win x hx)
    have allConditions := (safety_transfer A dense _ (actual_execution_causal σ)
      _ (counter_conditions_safety (MM2.compile P))).mp conditions
    refine ⟨σ, fun env => (Compiler.compiled_formula_iff_conditions P _).mpr ?_⟩
    simpa only [environment_of_graphs] using
      allConditions (fun n => (env n).graph)
  · rintro ⟨σ, win⟩
    exact ⟨σ, fun x _ => win (GraphExecutions.ofGraphs x)⟩

theorem prefixDense_encoded_undecidable (A : Set (Nat → Graph))
    (dense : PrefixDense A) : ¬ ComputablePred (RestrictedEncodedRealizable A) :=
  SourcePort.source.transfer (RestrictedEncodedRealizable A)
    ⟨Compiler.compileInstance, Compiler.compileInstance_computable,
      fun P => (compiled_restricted_iff A dense P).symm⟩

/-- Even a promise of eventually permanent bidirectional communication does
not make encoded LTL synthesis decidable. -/
theorem eventual_both_encoded_undecidable :
    ¬ ComputablePred (RestrictedEncodedRealizable
      {x | ∃ N, ∀ t, N ≤ t → x t = Graph.both}) :=
  prefixDense_encoded_undecidable _ (eventually_constant_prefixDense Graph.both)

/-- Removing only the all-bidirectional execution also leaves undecidability. -/
theorem exclude_both_forever_encoded_undecidable :
    ¬ ComputablePred (RestrictedEncodedRealizable {x | x ≠ fun _ => Graph.both}) :=
  prefixDense_encoded_undecidable _
    (exclude_constant_prefixDense Graph.both Graph.right (by decide))

end Characterisation
