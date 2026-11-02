/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.Adversaries
import DistributedSynthesis.Formalizations.Undecidability.GuardedFormulaCorrespondence

/-!
# Reduction to an adversary with a dense residual

Manuscript source label: `lem:guarded-safety-reduction`.

## Paper statement

A safety formula~$\phi$ is realizable under~$\Gamma^\omega$ if and only if~$\widehat{\phi}$ is realizable under~$A$.

## Reading the proof

See the [proof locations](PROOFS.md#reduction-to-an-adversary-with-a-dense-residual) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.GuardedReduction

universe u_1 u_2

/-- Reuses `Characterisation.guarded_safety_reduction_of_dense`. -/
theorem guarded_safety_reduction_of_dense :
    ∀ [inst : TopologicalSpace Graph] [DiscreteTopology Graph] {O₁ : Type u_1}
      {O₂ : Type u_2} (A : Set (ℕ → Graph)) (h : List Graph),
      Dense (Residual A h) →
        ∀ (S : Set (ℕ → RoundRecord Unit Unit Graph O₁ O₂)),
          IsSafety S →
            (RealizesSafety Set.univ S ↔
              ∃ (τ : StrategyPair Unit Unit O₁ O₂),
                ∀ y ∈ A,
                  graphPrefix y h.length = h → OmegaWord.drop (execution τ (GraphExecutions.ofGraphs y)) h.length ∈ S) :=
  @_root_.Characterisation.guarded_safety_reduction_of_dense

/-- Reuses `Characterisation.guardFormula_realizable_iff`. -/
theorem guardFormula_realizable_iff :
    ∀ [inst : TopologicalSpace Graph] [DiscreteTopology Graph] (A : Set (ℕ → Graph))
      (h : List Graph),
      Dense (Residual A h) →
        ∀ (n : ℕ) (φ : LTL CounterMachine.Compiler.RawLetter),
          IsSafety
              {w : ℕ → CounterMachine.ResidueLTL.Letter (Fin (n + 1)) |
                LTL.Satisfies FiniteLetterLTL.interp (fun (k : ℕ) => CounterMachine.Compiler.raw (w k)) φ} →
            (RealizesSafety Set.univ
                {w : ℕ → CounterMachine.ResidueLTL.Letter (Fin (n + 1)) |
                  LTL.Satisfies FiniteLetterLTL.interp (fun (k : ℕ) => CounterMachine.Compiler.raw (w k)) φ} ↔
              RealizesSafety A
                {w : ℕ → CounterMachine.ResidueLTL.Letter (Fin (n + 1)) |
                  LTL.Satisfies FiniteLetterLTL.interp (fun (k : ℕ) => CounterMachine.Compiler.raw (w k))
                    (guardFormula h n φ)}) :=
  @_root_.Characterisation.guardFormula_realizable_iff

/-- Reuses `Characterisation.guardFormula_safety`. -/
theorem guardFormula_safety :
    ∀ (h : List Graph) (n : ℕ) (φ : LTL CounterMachine.Compiler.RawLetter),
      IsSafety
          {w : ℕ → CounterMachine.ResidueLTL.Letter (Fin (n + 1)) |
            LTL.Satisfies FiniteLetterLTL.interp (fun (k : ℕ) => CounterMachine.Compiler.raw (w k)) φ} →
        IsSafety
          {w : ℕ → CounterMachine.ResidueLTL.Letter (Fin (n + 1)) |
            LTL.Satisfies FiniteLetterLTL.interp (fun (k : ℕ) => CounterMachine.Compiler.raw (w k)) (guardFormula h n φ)} :=
  @_root_.Characterisation.guardFormula_safety

end DistributedSynthesis.Paper.GuardedReduction
