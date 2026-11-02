/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Final composition of the credited Rocq-to-Lean source reductions with Mathlib
halting undecidability. See README.md for individual authors and adaptations.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA2Source
import DistributedSynthesis.Library.Computability.CounterMachines.MMA2ToMM2

/-! # The proved zero-initialized two-counter source theorem

This is the sole composition point that discharges the stable source interface.
It imports no distributed-synthesis result. No new axiom or global instance is
introduced; consumers may explicitly pass `SourcePort.source`.
-/
namespace DistributedSynthesis.CounterMachine.SourcePort

noncomputable def reduce (p : Nat.Partrec.Code) : MM2.Program := MMA2ToMM2.toZero (MMA2Source.reduce p)
theorem reduce_primrec : Primrec reduce := MMA2ToMM2.toZero_primrec.comp MMA2Source.reduce_primrec
theorem reduce_correct (p : Nat.Partrec.Code) : MM2.ZeroHalts (reduce p) ↔ (p.eval 0).Dom :=
  (MMA2ToMM2.toZero_correct _).trans (MMA2Source.reduce_correct p)
theorem halting_manyOneReducible_zeroHalting :
    (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ MM2.ZeroHalts :=
  ⟨reduce,reduce_primrec.to_comp,fun p => (reduce_correct p).symm⟩
theorem source : MM2.SourceUndecidability :=
  MM2.SourceUndecidability.of_halting_reduction halting_manyOneReducible_zeroHalting
theorem zeroHalting_not_computable : ¬ ComputablePred MM2.ZeroHalts := source.zeroHalting_not_computable

end DistributedSynthesis.CounterMachine.SourcePort
