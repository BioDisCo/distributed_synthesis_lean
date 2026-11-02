/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineLTL
import DistributedSynthesis.Formalizations.Lemma.LemMM2SourceInterface

/-! # Adapter for the zero-initialized MM2 source problem

The source instruction and transition definitions below follow `MM2.v` in
the Coq library of undecidability proofs, revision
`11c41e0637f0c5219ad1c4c92d11609b7e072c31`.
In particular, addresses start at one and conditional decrement jumps on
the *positive* branch. Every missing instruction halts.

This file proves the semantic adapter. It does not import the Coq theorem
`MM2_ZERO_HALTING_undec` or assert its Lean counterpart as an axiom.
-/
namespace DistributedSynthesis.CounterMachine.MM2


/-- One finite sink represents all missing source addresses. Addresses
`1,...,length P` keep their literal values. No jump bound is assumed. -/
def address (P : Program) (i : Nat) : Fin (P.length+1) :=
  if h : i ≤ P.length then ⟨i,by omega⟩ else 0
theorem lookup_address (P : Program) (i : Nat) :
    lookup P (address P i).val = lookup P i := by
  by_cases hi : i ≤ P.length
  · simp [address,hi]
  · have hz : i ≠ 0 := by omega
    simp [address,hi,lookup,hz,List.getElem?_eq_none (by omega : P.length ≤ i-1)]
def instruction (P : Program) (i : Nat) : Instr → CounterMachine.Instruction (Fin (P.length+1))
  | .incA => .inc 0 (address P (i+1))
  | .incB => .inc 1 (address P (i+1))
  | .decA j => .dec 0 (address P (i+1)) (address P j)
  | .decB j => .dec 1 (address P (i+1)) (address P j)
def compile (P : Program) : Machine (Fin (P.length+1)) where
  initial := address P 1
  code := fun q ↦ (lookup P q.val).map (instruction P q.val)
def counters (x : Nat × Nat) : Fin 2 → Nat := fun k ↦ if k = 0 then x.1 else x.2
def configuration (P : Program) (x : Cfg) : Fin (P.length+1) × (Fin 2 → Nat) :=
  (address P x.1,counters x.2)
theorem address_of_lookup (P : Program) {i : Nat} {ρ : Instr} (h : lookup P i = some ρ) :
    (address P i).val = i := by
  have hi : i ≠ 0 := by intro hi; simp [lookup,hi] at h
  have hg : P[i-1]? = some ρ := by simpa [lookup,hi] using h
  have hb := (List.getElem?_eq_some_iff.mp hg).1
  simp [address,show i ≤ P.length by omega]

theorem compile_halts (P : Program) (x : Cfg) :
    (compile P).code (configuration P x).1 = none ↔ lookup P x.1 = none := by
  simp [compile,configuration,lookup_address]

theorem compile_step (P : Program) (x : Cfg) :
    (compile P).advance (configuration P x) = configuration P (advance P x) := by
  cases h : lookup P x.1 with
  | none =>
    have hc : (compile P).code (configuration P x).1 = none := (compile_halts P x).mpr h
    simp [Machine.advance,Machine.next,Machine.op,hc,TernaryCounter.Operation.applyCount,advance,h]
  | some ρ =>
    have ha := address_of_lookup P h
    have hc : (compile P).code (configuration P x).1 = some (instruction P x.1 ρ) := by
      simp [compile,configuration,ha,h]
    rcases x with ⟨i,a,b⟩
    dsimp only [configuration,Prod.fst] at hc
    apply Prod.ext
    · cases ρ <;> simp [Machine.advance,Machine.next,hc,instruction,flags,configuration,
        advance,h,atomNext,counters] <;> split <;> rfl
    · funext k
      fin_cases k <;> cases ρ <;> by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;>
        simp [Machine.advance,Machine.op,hc,instruction,flags,configuration,
          advance,h,atomNext,counters,TernaryCounter.Operation.applyCount,ha0,hb0]

theorem compile_run (P : Program) (n : Nat) :
    (compile P).run n = configuration P (run P n) := by
  induction n with
  | zero =>
    change (address P 1,fun _ ↦ 0) = (address P 1,counters (0,0))
    apply Prod.ext
    · rfl
    · funext k; simp [counters]
  | succ n ih => rw [Machine.run,ih,compile_step,run]

/-- The exact relational zero-initialized MM2 halting predicate is the
complement of the nonhalting predicate used by the distributed reduction. -/
theorem compile_nonhalting_iff (P : Program) : (compile P).Nonhalting ↔ ¬ ZeroHalts P := by
  rw [zeroHalts_iff_run]
  simp only [Machine.Nonhalting,compile_run,not_exists]
  exact forall_congr' fun n ↦ not_congr (compile_halts P (run P n))

theorem ltl_realizable_iff_not_zeroHalts (P : Program) :
    ResidueLTL.Realizable (ResidueLTL.formula (compile P)) ↔ ¬ ZeroHalts P :=
  (ResidueLTL.ltl_realizable_iff_nonhalting (compile P)).trans (compile_nonhalting_iff P)

/-- Conditional consequence of precisely the deferred classical theorem.
This is the source-indexed predicate; undecidability for encoded LTL inputs
also needs the effective compiler and `SourceUndecidability.transfer`. -/
theorem sourceIndexedRealizability_not_computable (source : SourceUndecidability) :
    ¬ ComputablePred (fun P : Program ↦ ResidueLTL.Realizable (ResidueLTL.formula (compile P))) := by
  intro h
  exact source.nonhalting_not_computable (h.of_eq ltl_realizable_iff_not_zeroHalts)

end DistributedSynthesis.CounterMachine.MM2
