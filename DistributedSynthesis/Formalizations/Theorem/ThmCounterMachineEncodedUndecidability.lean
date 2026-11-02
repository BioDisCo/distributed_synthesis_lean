/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineTableCorrectness

/-! # Encoded LTL synthesis is undecidable relative only to the classical source theorem

An instance is a natural alphabet parameter and a finite postfix LTL string.
Its semantics uses the original local perfect-recall execution model.
The compiler is primitive recursive, and the source undecidability theorem
is an explicit parameter, not an axiom of the development.
-/
namespace DistributedSynthesis.CounterMachine.Compiler
open MM2 ResidueLTL
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

private theorem release_tests {A : Type*} (w : OmegaWord A) (xs ys : List A)
    (stays good : Nat → Prop)
    (hl : ∀ n, w n ∈ xs ↔ ¬ stays n)
    (hr : ∀ n, w n ∈ ys ↔ ¬ stays n ∨ good n) :
    LTL.Satisfies FiniteLetterLTL.interp w (.release (EncodedFiniteLTL.decode (EncodedFiniteLTL.test xs)) (EncodedFiniteLTL.decode (EncodedFiniteLTL.test ys))) ↔
      ∀ n, (∀ k, k ≤ n → stays k) → good n := by
  simp only [LTL.Satisfies,EncodedFiniteLTL.satisfies_test,OmegaWord.drop_apply,Nat.add_zero,hl,hr]
  constructor
  · intro h n hn
    rcases h n with (hleave | hg) | ⟨k,hk,hleave⟩
    · exact False.elim (hleave (hn n le_rfl))
    · exact hg
    · exact False.elim (hleave (hn k (Nat.le_of_lt hk)))
  · intro h n
    by_cases hn : ∀ k, k ≤ n → stays k
    · exact Or.inl (Or.inr (h n hn))
    · push Not at hn
      obtain ⟨k,hk,hleave⟩ := hn
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact Or.inr ⟨k,hk,hleave⟩
      · exact Or.inl (Or.inl hleave)

theorem compiled_formula_iff_conditions (P : Program) (w : OmegaWord (Letter (Fin (P.length+1)))) :
    LTL.Satisfies FiniteLetterLTL.interp (fun n ↦ raw (w n))
      (EncodedFiniteLTL.decode (compileInstance P).2) ↔ Conditions (compile P) w := by
  change LTL.Satisfies _ _ (EncodedFiniteLTL.decode (EncodedFiniteLTL.assemble (tables P))) ↔ _
  rw [(EncodedFiniteLTL.assemble_rep (tables P)).decode]
  have hl := release_tests (fun n ↦ raw (w n))
    ((letters P.length).filter (fun r ↦ leaveRight r.1))
    ((letters P.length).filter (fun r ↦ guardLeft r.1))
    (fun n ↦ (w n).graph = .right) (fun n ↦ leftCheck (w n).outputOne.base)
    (fun n ↦ by
      simp only [List.mem_filter,raw_mem,true_and]
      exact decide_eq_true_iff)
    (fun n ↦ by
      simp only [List.mem_filter,raw_mem,true_and]
      change decide (¬ (w n).graph = .right ∨ leftCheck (w n).outputOne.base) = true ↔ _
      exact decide_eq_true_iff)
  have hr := release_tests (fun n ↦ raw (w n))
    ((letters P.length).filter (fun r ↦ leaveLeft r.1))
    ((letters P.length).filter (fun r ↦ guardRight r.1))
    (fun n ↦ (w n).graph = .left) (fun n ↦ rightCheck (w n).outputTwo.base)
    (fun n ↦ by
      simp only [List.mem_filter,raw_mem,true_and]
      exact decide_eq_true_iff)
    (fun n ↦ by
      simp only [List.mem_filter,raw_mem,true_and]
      change decide (¬ (w n).graph = .left ∨ rightCheck (w n).outputTwo.base) = true ↔ _
      exact decide_eq_true_iff)
  change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
  simp only [tables]
  rw [hl,hr]
  simp only [EncodedFiniteLTL.satisfies_test,LTL.satisfies_always,EncodedFiniteLTL.satisfies_relation,
    OmegaWord.drop_apply,Nat.add_zero,List.mem_filter,raw_mem,true_and,
    initialTest_correct,localTest_correct,pairTest_correct,mem_pairs,and_self,Conditions]

/-- The target predicate does not mention a source program. It interprets
the supplied LTL string over the supplied finite output alphabet. -/
def EncodedRealizable (I : Instance) : Prop :=
  ∃ σ : StrategyPair Unit Unit (Output (Fin (I.1+1))) (Output (Fin (I.1+1))),
    ∀ env, LTL.Satisfies FiniteLetterLTL.interp (fun n ↦ raw (execution σ env n)) (EncodedFiniteLTL.decode I.2)

/-- The compiled LTL instance is realizable exactly when the source machine
does not halt from its zero-initialized configuration. The environment may
choose any graph sequence, and both input alphabets are singletons. -/
theorem compiled_realizable_iff (P : Program) :
    EncodedRealizable (compileInstance P) ↔ ¬ ZeroHalts P := by
  rw [← ltl_realizable_iff_not_zeroHalts P]
  change (∃ σ : StrategyPair Unit Unit (Output (Fin (P.length+1))) (Output (Fin (P.length+1))), _) ↔ _
  apply exists_congr
  intro σ
  apply forall_congr'
  intro env
  exact (compiled_formula_iff_conditions P (execution σ env)).trans (satisfies_iff (compile P) _).symm

/-- The effective many-one reduction includes both semantic correctness and
the primitive-recursive compiler; neither is an external hypothesis. -/
theorem nonhalting_manyOneReducible :
    (fun P : Program ↦ ¬ ZeroHalts P) ≤₀ EncodedRealizable :=
  ⟨compileInstance,compileInstance_computable,fun P ↦ (compiled_realizable_iff P).symm⟩

/-- Undecidability of zero-initialized two-counter-machine halting implies
undecidability of finite-output LTL synthesis. The source theorem is an explicit
parameter here; `CounterMachine.Unconditional` supplies its proved inhabitant. -/
theorem encoded_ltl_synthesis_undecidable (source : SourceUndecidability) :
    ¬ ComputablePred EncodedRealizable :=
  source.transfer EncodedRealizable nonhalting_manyOneReducible

end DistributedSynthesis.CounterMachine.Compiler
