/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Undecidability.Adversaries
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.GuardedEncoding

/-! The manuscript's guarded formula, over the actual finite output alphabet.
The existing guard compiler and its exact LTL semantics are reused. -/
namespace Characterisation
open DistributedSynthesis CounterMachine ResidueLTL EncodedFiniteLTL Compiler

/-- A safety formula remains a safety formula after the finite prefix guard
and shift. Safety is stated over all words in the actual finite alphabet,
not merely over executions of a particular strategy. -/
theorem guardFormula_safety (h : List Graph) (n : Nat) (φ : LTL RawLetter)
    (safety : IsSafety {w : Nat → ResidueLTL.Letter (Fin (n+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) φ}) :
    IsSafety {w : Nat → ResidueLTL.Letter (Fin (n+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) (guardFormula h n φ)} := by
  have eq : {w : Nat → ResidueLTL.Letter (Fin (n+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) (guardFormula h n φ)} =
      {w | graphPrefix (fun k => (w k).graph) h.length = h →
        OmegaWord.drop w h.length ∈ {v | LTL.Satisfies FiniteLetterLTL.interp
          (fun k => raw (v k)) φ}} := by
    ext w
    exact satisfies_guardFormula h n φ w
  rw [eq]
  exact guarded_objective_safety h _ safety

/-- The reduction for the literal guarded LTL formula. The safety premise is
on the source formula; there is no extra safety premise on its guarded form. -/
theorem guardFormula_realizable_iff
    [TopologicalSpace Graph] [DiscreteTopology Graph]
    (A : Set (Nat → Graph)) (h : List Graph) (dense : Dense (Residual A h))
    (n : Nat) (φ : LTL RawLetter)
    (safety : IsSafety {w : Nat → ResidueLTL.Letter (Fin (n+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) φ}) :
    RealizesSafety Set.univ {w : Nat → ResidueLTL.Letter (Fin (n+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) φ} ↔
    RealizesSafety A {w : Nat → ResidueLTL.Letter (Fin (n+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) (guardFormula h n φ)} := by
  rw [guarded_safety_reduction_of_dense A h dense _ safety]
  unfold RealizesSafety
  apply exists_congr
  intro σ
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  simpa only [Set.mem_setOf_eq,GraphExecutions.execution_graph,GraphExecutions.ofGraphs,
    OmegaWord.drop] using (satisfies_guardFormula h n φ
      (execution σ (GraphExecutions.ofGraphs x))).symm

/-- In particular, the actual guarded output of the counter-machine compiler
is a safety specification, as required by the English closure proof. -/
theorem guardedCompile_safety (h : List Graph) (P : MM2.Program) :
    IsSafety {w : Nat → ResidueLTL.Letter (Fin (P.length+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k))
        (decode (guardedCompile h P).2)} := by
  have source : IsSafety {w : Nat → ResidueLTL.Letter (Fin (P.length+1)) |
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k))
        (decode (compileInstance P).2)} := by
    have eq : {w : Nat → ResidueLTL.Letter (Fin (P.length+1)) |
        LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k))
          (decode (compileInstance P).2)} = {w | Conditions (MM2.compile P) w} := by
      ext w
      exact compiled_formula_iff_conditions P w
    rw [eq]
    exact counter_conditions_safety (MM2.compile P)
  have rep := guardCode_rep h P.length (assemble_rep (tables P))
  have formulaEq : decode (guardedCompile h P).2 =
      guardFormula h P.length (decode (compileInstance P).2) := by
    change decode (guardCode h P.length (assemble (tables P))) = _
    rw [rep.decode]
    change _ = guardFormula h P.length (decode (assemble (tables P)))
    rw [(assemble_rep (tables P)).decode]
  rw [formulaEq]
  exact guardFormula_safety h P.length _ source

end Characterisation
