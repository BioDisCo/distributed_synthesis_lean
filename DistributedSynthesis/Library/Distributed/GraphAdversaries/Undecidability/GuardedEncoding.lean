/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.GuardedRestart

/-! A primitive-recursive prefix guard for the existing encoded compiler.
This construction uses the next operator. -/
namespace Characterisation
open DistributedSynthesis CounterMachine ResidueLTL EncodedFiniteLTL
open Compiler

noncomputable def graphTest (n : Nat) (g : Graph) : Code RawLetter :=
  test ((letters n).filter (fun r => decide (r.1.1 = g)))

noncomputable def guardCode (h : List Graph) (n : Nat) (c : Code RawLetter) : Code RawLetter :=
  match h with
  | [] => c
  | g :: t => binary 4 (unary 2 (graphTest n g)) (unary 5 (guardCode t n c))

noncomputable def guardFormula (h : List Graph) (n : Nat) (φ : LTL RawLetter) : LTL RawLetter :=
  match h with
  | [] => φ
  | g :: t => .disj (.neg (decode (graphTest n g))) (.next (guardFormula t n φ))

theorem guardCode_rep (h : List Graph) (n : Nat) {c : Code RawLetter} {φ : LTL RawLetter}
    (hc : Represents c φ) : Represents (guardCode h n c) (guardFormula h n φ) := by
  induction h with
  | nil => exact hc
  | cons g t ih =>
    apply disj_rep
    · apply unary_rep 2 LTL.neg (fun _ _ => rfl)
      exact (test_rep _).decode ▸ test_rep _
    · exact next_rep ih

theorem graphTest_primrec (g : Graph) : Primrec (fun n => graphTest n g) :=
  test_primrec.comp (filter_primrec letters_primrec
    ((Primrec.dom_finite (fun s : Shape => decide (s.1 = g))).comp
      (Primrec.fst.comp Primrec.snd)).to₂)

theorem guardCode_primrec (h : List Graph) :
    Primrec (fun z : Nat × Code RawLetter => guardCode h z.1 z.2) := by
  induction h with
  | nil => exact Primrec.snd
  | cons g t ih =>
    exact (binary_primrec 4).comp
      ((unary_primrec 2).comp ((graphTest_primrec g).comp Primrec.fst))
      ((unary_primrec 5).comp ih)

private theorem prefix_cons (x : Nat → Graph) (n : Nat) :
    graphPrefix x (n+1) = x 0 :: graphPrefix (OmegaWord.drop x 1) n := by
  simp [graphPrefix, List.ofFn_succ, OmegaWord.drop, Nat.add_comm]

theorem satisfies_graphTest (n : Nat) (g : Graph) (w : Nat → ResidueLTL.Letter (Fin (n+1))) :
    LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) (decode (graphTest n g)) ↔
      (w 0).graph = g := by
  simp only [graphTest, satisfies_test, List.mem_filter, raw_mem, true_and,
    decide_eq_true_eq]
  rfl

theorem satisfies_guardFormula (h : List Graph) (n : Nat) (φ : LTL RawLetter)
    (w : Nat → ResidueLTL.Letter (Fin (n+1))) :
    LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) (guardFormula h n φ) ↔
      (graphPrefix (fun k => (w k).graph) h.length = h →
        LTL.Satisfies FiniteLetterLTL.interp
          (fun k => raw (w (h.length + k))) φ) := by
  induction h generalizing w with
  | nil => simp [guardFormula, graphPrefix]
  | cons g t ih =>
    change (¬ LTL.Satisfies _ _ (decode (graphTest n g)) ∨
      LTL.Satisfies _ (fun k => raw (w (1+k))) (guardFormula t n φ)) ↔ _
    have tail := ih (OmegaWord.drop w 1)
    simp only [OmegaWord.drop] at tail
    rw [satisfies_graphTest, tail]
    simp only [List.length_cons, prefix_cons, List.cons.injEq]
    have shift : (fun k => raw (w (1 + (t.length + k)))) =
        (fun k => raw (w (t.length + 1 + k))) := by
      funext k
      congr 2
      omega
    rw [shift]
    tauto

noncomputable def guardedCompile (h : List Graph) (P : MM2.Program) : Compiler.Instance :=
  (P.length, guardCode h P.length (compileInstance P).2)

/-- For each fixed prefix, the complete machine-to-guarded-formula compiler
is primitive recursive under the existing numerical encodings. -/
theorem guardedCompile_primrec (h : List Graph) : Primrec (guardedCompile h) :=
  Primrec.pair Primrec.list_length
    ((guardCode_primrec h).comp compileInstance_primrec)

theorem guardedCompile_computable (h : List Graph) : Computable (guardedCompile h) :=
  (guardedCompile_primrec h).to_comp

theorem guardedCompile_iff (A : Set (Nat → Graph)) (h : List Graph) (P : MM2.Program) :
    RestrictedEncodedRealizable A (guardedCompile h P) ↔
      RestrictedEncodedRealizable (Residual A h) (compileInstance P) := by
  have rep := guardCode_rep h P.length (assemble_rep (tables P))
  have sem (w : Nat → ResidueLTL.Letter (Fin (P.length+1))) :
      LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k))
          (decode (guardedCompile h P).2) ↔
        (graphPrefix (fun k => (w k).graph) h.length = h →
          LTL.Satisfies FiniteLetterLTL.interp
            (fun k => raw (w (h.length+k))) (decode (compileInstance P).2)) := by
    change LTL.Satisfies _ _ (decode (guardCode h P.length (assemble (tables P)))) ↔ _
    rw [rep.decode]
    change _ ↔ (_ → LTL.Satisfies _ _ (decode (assemble (tables P))))
    rw [(assemble_rep (tables P)).decode]
    exact satisfies_guardFormula h _ _ w
  refine Iff.trans ?_ (guarded_restart_iff A h
    {w : Nat → ResidueLTL.Letter (Fin (P.length+1)) | LTL.Satisfies FiniteLetterLTL.interp
      (fun k => raw (w k)) (decode (compileInstance P).2)}).symm
  change (∃ σ : StrategyPair Unit Unit (Output (Fin (P.length+1)))
      (Output (Fin (P.length+1))), _) ↔ _
  apply exists_congr
  intro σ
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  simpa only [GraphExecutions.execution_graph, GraphExecutions.ofGraphs, OmegaWord.drop]
    using sem (execution σ (GraphExecutions.ofGraphs x))

/-- Failure of open holes implies undecidability on the original adversary,
not only on a residual. No regularity hypothesis is needed in this direction. -/
theorem no_geometric_holes_encoded_undecidable (A : Set (Nat → Graph))
    (noHoles : ¬ GeometricHoles A) : ¬ ComputablePred (RestrictedEncodedRealizable A) := by
  obtain ⟨h, dense⟩ := no_geometric_holes_has_prefixDense_residual A noHoles
  exact SourcePort.source.transfer (RestrictedEncodedRealizable A)
    ⟨guardedCompile h, guardedCompile_computable h, fun P =>
      ((guardedCompile_iff A h P).trans (compiled_restricted_iff _ dense P)).symm⟩

end Characterisation
