/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Composition of the proved BSM source with the credited BSM-to-MM compiler.
The stack/register simulation follows Dominique Larchey-Wendling's mm_comp.v;
its Lean computability certification is added by this project. See README.md.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.BSMSource
import DistributedSynthesis.Library.Computability.CounterMachines.BSMToMM.Compiler

/-! # Unconditional six-register MM halting source

Four BSM stacks become four positive sentinel-encoded registers. Two additional
registers start at zero and are restored to zero after each simulated step.
The compiled program is fixed; all varying input work is primitive recursive.
No MMA/MM2 undecidability premise or register/FRACTRAN theorem is used here.
-/
namespace DistributedSynthesis.CounterMachine.MMSource

noncomputable def program : MM.Program 6 := BSMToMM.compile BSMSource.program

def inputRegisters (w : List Bool) : MM.Registers 6 := BSMToMM.state (BSMSource.inputStacks w)

theorem inputRegisters_primrec : Primrec inputRegisters :=
  BSMToMM.state_primrec.comp BSMSource.inputStacks_primrec

def WordHalts (w : List Bool) : Prop := MM.Halts (program,inputRegisters w)

theorem wordHalts_correct (w : List Bool) : WordHalts w ↔ BSMSource.WordHalts w :=
  BSMToMM.compile_correct BSMSource.program (BSMSource.inputStacks w)

theorem wordHalting_manyOneReducible : BSMSource.WordHalts ≤₀ WordHalts :=
  ⟨id,Computable.id,fun w => (wordHalts_correct w).symm⟩

theorem wordHalting_not_computable : ¬ ComputablePred WordHalts := by
  intro h
  exact BSMSource.wordHalting_not_computable
    (ComputablePred.computable_of_manyOneReducible wordHalting_manyOneReducible h)

noncomputable def reduce (p : Nat.Partrec.Code) : MM.HaltingInput 6 :=
  (program,inputRegisters (MathlibBridge.BinaryUniversal.inputWord p))

theorem reduce_primrec : Primrec reduce :=
  (Primrec.const program).pair
    (inputRegisters_primrec.comp MathlibBridge.BinaryUniversal.inputWord_primrec)

theorem reduce_correct (p : Nat.Partrec.Code) : MM.Halts (reduce p) ↔ (p.eval 0).Dom :=
  (wordHalts_correct _).trans (BSMSource.reduce_correct p)

theorem halting_manyOneReducible :
    (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ @MM.Halts 6 :=
  ⟨reduce,reduce_primrec.to_comp,fun p => (reduce_correct p).symm⟩

theorem halting_not_computable : ¬ ComputablePred (@MM.Halts 6) := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible h)

end DistributedSynthesis.CounterMachine.MMSource
