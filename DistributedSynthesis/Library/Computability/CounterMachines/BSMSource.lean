/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Composition of the credited Mathlib halting source with the TM2-to-BSM compiler.
Mathlib's source compiler is due to Mario Carneiro (Apache-2.0); the BSM model
is due to Dominique Larchey-Wendling (MPL-2.0). See README.md for provenance.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.TM2ToBSM
import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.BinaryUniversalStackMachine
import Mathlib.Tactic.FinCases

/-! # Unconditional halting undecidability for the Rocq BSM model

One fixed four-stack BSM program, placed at base address one, simulates the
fixed Mathlib universal program. Only its initial binary word varies. This
module proves the explicit primitive-recursive input reduction, not merely an
implication from an assumed BSM undecidability theorem. The separate `MMSource`
module composes this with the proved register simulation, and `FRACTRANSource`
continues to regular FRACTRAN. `SourcePort.source` completes the chain to zero-MM2.
-/
namespace DistributedSynthesis.CounterMachine.BSMSource
open Turing Turing.PartrecToTM2 MathlibBridge

def stackEquiv : K' ≃ Fin 4 where
  toFun
    | .main => 0
    | .rev => 1
    | .aux => 2
    | .stack => 3
  invFun k := match k.val with
    | 0 => .main
    | 1 => .rev
    | 2 => .aux
    | _ => .stack
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

noncomputable def program : BSM.Program 4 :=
  TM2ToBSM.compile (BinaryUniversal.program universalCode) stackEquiv 0
    (initialLabel universalCode) (none,none)

def inputStacks (w : List Bool) : BSM.Stacks 4 := fun k => if k = 0 then w else []

theorem inputStacks_correct (w : List Bool) :
    inputStacks w = TM2ToBSM.mapStacks stackEquiv (BinaryUniversal.initial universalCode w).stk := by
  funext k
  fin_cases k <;> rfl

def WordHalts (w : List Bool) : Prop := BSM.Halts (1,program,inputStacks w)

theorem wordHalts_correct (w : List Bool) :
    WordHalts w ↔ BinaryUniversal.WordHalts universalCode w := by
  unfold WordHalts
  rw [inputStacks_correct]
  exact TM2ToBSM.compile_correct (BinaryUniversal.program universalCode) stackEquiv 0
    (initialLabel universalCode) (none,none) (BinaryUniversal.initial universalCode w).stk

theorem inputStacks_primrec : Primrec inputStacks := by
  apply Primrec.fin_curry.mpr
  exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    Primrec.fst (Primrec.const [])).to₂

theorem wordHalting_manyOneReducible : BinaryUniversal.WordHalts universalCode ≤₀ WordHalts :=
  ⟨id,Computable.id,fun w => (wordHalts_correct w).symm⟩

theorem wordHalting_not_computable : ¬ ComputablePred WordHalts := by
  intro h
  exact BinaryUniversal.wordHalting_not_computable
    (ComputablePred.computable_of_manyOneReducible wordHalting_manyOneReducible h)

noncomputable def reduce (p : Nat.Partrec.Code) : BSM.HaltingInput 4 :=
  (1,program,inputStacks (BinaryUniversal.inputWord p))

theorem reduce_primrec : Primrec reduce :=
  (Primrec.const 1).pair ((Primrec.const program).pair
    (inputStacks_primrec.comp BinaryUniversal.inputWord_primrec))

theorem reduce_correct (p : Nat.Partrec.Code) : BSM.Halts (reduce p) ↔ (p.eval 0).Dom :=
  (wordHalts_correct _).trans (BinaryUniversal.inputWord_correct p)

theorem halting_manyOneReducible :
    (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ @BSM.Halts 4 :=
  ⟨reduce,reduce_primrec.to_comp,fun p => (reduce_correct p).symm⟩

theorem halting_not_computable : ¬ ComputablePred (@BSM.Halts 4) := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible h)

end DistributedSynthesis.CounterMachine.BSMSource
