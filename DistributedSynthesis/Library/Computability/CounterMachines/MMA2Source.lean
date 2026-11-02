/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Composition with Dominique Larchey-Wendling's FRACTRAN-to-MMA2 construction.
The explicit Mathlib primitive-recursive reduction is added by this port.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRANSource
import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRANToMMA.Compiler

namespace DistributedSynthesis.CounterMachine.MMA2Source

noncomputable def program : MMA.Program 2 := FRACTRANToMMA.compile FRACTRANSource.program
noncomputable def input (w : List Bool) : MMA.Registers 2 := FRACTRANToMMA.initial (FRACTRANSource.input w)
theorem input_primrec : Primrec input := FRACTRANToMMA.initial_primrec.comp FRACTRANSource.input_primrec

def WordHalts (w : List Bool) : Prop := MMA.Halts (program,input w)
theorem wordHalts_correct (w : List Bool) : WordHalts w ↔ FRACTRANSource.WordHalts w :=
  FRACTRANToMMA.compile_correct FRACTRANSource.program FRACTRANSource.program_regular (FRACTRANSource.input w)
theorem wordHalting_manyOneReducible : FRACTRANSource.WordHalts ≤₀ WordHalts :=
  ⟨id,Computable.id,fun w => (wordHalts_correct w).symm⟩
theorem wordHalting_not_computable : ¬ ComputablePred WordHalts := by
  intro h
  exact FRACTRANSource.wordHalting_not_computable
    (ComputablePred.computable_of_manyOneReducible wordHalting_manyOneReducible h)

noncomputable def reduce (p : Nat.Partrec.Code) : MMA.HaltingInput 2 :=
  (program,input (MathlibBridge.BinaryUniversal.inputWord p))
theorem reduce_primrec : Primrec reduce :=
  (Primrec.const program).pair (input_primrec.comp MathlibBridge.BinaryUniversal.inputWord_primrec)
theorem reduce_correct (p : Nat.Partrec.Code) : MMA.Halts (reduce p) ↔ (p.eval 0).Dom :=
  (wordHalts_correct _).trans (FRACTRANSource.reduce_correct p)
theorem halting_manyOneReducible :
    (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ @MMA.Halts 2 :=
  ⟨reduce,reduce_primrec.to_comp,fun p => (reduce_correct p).symm⟩
theorem halting_not_computable : ¬ ComputablePred (@MMA.Halts 2) := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible h)

end DistributedSynthesis.CounterMachine.MMA2Source
