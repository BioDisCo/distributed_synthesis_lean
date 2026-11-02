/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Composition with the MM-to-FRACTRAN construction credited to Dominique
Larchey-Wendling and Yannick Forster. Mathlib computability proofs are added
by this Lean port. See README.md.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMSource
import DistributedSynthesis.Library.Computability.CounterMachines.MMToFRACTRAN.Compiler
import DistributedSynthesis.Library.Computability.CounterMachines.MMToFRACTRAN.Computable

/-! # Unconditional regular FRACTRAN halting source

The program and its finitely many primes are fixed. All varying-input work is
primitive recursive; no uniform effective prime enumeration is assumed.
-/
namespace DistributedSynthesis.CounterMachine.FRACTRANSource

noncomputable def program : FRACTRAN.Program := MMToFRACTRAN.compile MMSource.program
theorem program_regular : FRACTRAN.Regular program := MMToFRACTRAN.compile_regular _

noncomputable def input (w : List Bool) : Nat := MMToFRACTRAN.state (1,MMSource.inputRegisters w)
theorem input_primrec : Primrec input := MMToFRACTRAN.initial_primrec.comp MMSource.inputRegisters_primrec
theorem input_positive (w : List Bool) : 0 < input w :=
  Nat.mul_pos (MMToFRACTRAN.entry_prime 1).pos (MMToFRACTRAN.registers_positive _)

def WordHalts (w : List Bool) : Prop := FRACTRAN.Halts (program,input w)
theorem wordHalts_correct (w : List Bool) : WordHalts w ↔ MMSource.WordHalts w :=
  MMToFRACTRAN.compile_correct MMSource.program (MMSource.inputRegisters w)
theorem wordHalting_manyOneReducible : MMSource.WordHalts ≤₀ WordHalts :=
  ⟨id,Computable.id,fun w => (wordHalts_correct w).symm⟩
theorem wordHalting_not_computable : ¬ ComputablePred WordHalts := by
  intro h
  exact MMSource.wordHalting_not_computable
    (ComputablePred.computable_of_manyOneReducible wordHalting_manyOneReducible h)

noncomputable def reduce (p : Nat.Partrec.Code) : FRACTRAN.HaltingInput :=
  (program,input (MathlibBridge.BinaryUniversal.inputWord p))
theorem reduce_primrec : Primrec reduce :=
  (Primrec.const program).pair (input_primrec.comp MathlibBridge.BinaryUniversal.inputWord_primrec)
theorem reduce_correct (p : Nat.Partrec.Code) : FRACTRAN.Halts (reduce p) ↔ (p.eval 0).Dom :=
  (wordHalts_correct _).trans (MMSource.reduce_correct p)
theorem reduce_regular (p : Nat.Partrec.Code) : FRACTRAN.Regular (reduce p).1 := program_regular
theorem reduce_regular_correct (p : Nat.Partrec.Code) : FRACTRAN.RegularHalts (reduce p) ↔ (p.eval 0).Dom := by
  simp only [FRACTRAN.RegularHalts,reduce_regular,true_and,reduce_correct]

theorem halting_manyOneReducible :
    (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ FRACTRAN.Halts :=
  ⟨reduce,reduce_primrec.to_comp,fun p => (reduce_correct p).symm⟩
theorem regularHalting_manyOneReducible :
    (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ FRACTRAN.RegularHalts :=
  ⟨reduce,reduce_primrec.to_comp,fun p => (reduce_regular_correct p).symm⟩
theorem halting_not_computable : ¬ ComputablePred FRACTRAN.Halts := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible h)
theorem regularHalting_not_computable : ¬ ComputablePred FRACTRAN.RegularHalts := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible regularHalting_manyOneReducible h)

end DistributedSynthesis.CounterMachine.FRACTRANSource
