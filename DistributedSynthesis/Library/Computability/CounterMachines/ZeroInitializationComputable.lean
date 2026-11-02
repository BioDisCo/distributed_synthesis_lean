/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Computability certification for the Lean adaptation of Andrej Dudenhefner's
MM2_HALTING_to_MM2_ZERO_HALTING.v (Coq library of undecidability proofs).
Upstream revision: 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
The explicit Mathlib Primrec proofs are additions of the Lean port.
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.ZeroInitialization
import Mathlib.Computability.Primrec.List

namespace DistributedSynthesis.CounterMachine.MM2.ZeroInitialization

theorem shiftAddress_primrec : Primrec₂ shiftAddress :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const 0) (Primrec.nat_add.comp Primrec.snd Primrec.fst)

theorem shiftInstr_primrec : Primrec₂ shiftInstr := by
  have hc : Primrec (fun x : Nat × Instr => x.2.equivCode) :=
    (Primrec.of_equiv (e := Instr.equivCode)).comp Primrec.snd
  have hp : Primrec (fun x : Nat × Instr =>
      (x.2.equivCode.1, x.2.equivCode.2.map (shiftAddress x.1))) :=
    Primrec.pair (Primrec.fst.comp hc)
      (Primrec.option_map (Primrec.snd.comp hc)
        (shiftAddress_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
  apply ((Primrec.of_equiv_symm (e := Instr.equivCode)).comp hp).of_eq
  rintro ⟨k, ρ⟩
  cases ρ <;> rfl

/-- Mathlib's range/map primitives certify the unary loading prefix. -/
theorem replicate_primrec (ρ : Instr) : Primrec (fun n => List.replicate n ρ) := by
  apply (Primrec.list_map Primrec.list_range (Primrec.const ρ).to₂).of_eq
  intro n
  simp

def reduce (d : HaltingInput) : Program := compile d.1 d.2.1 d.2.2

theorem reduce_primrec : Primrec reduce := by
  have hk : Primrec (fun d : HaltingInput => d.2.1+d.2.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      ((replicate_primrec .incA).comp (Primrec.fst.comp Primrec.snd))
      ((replicate_primrec .incB).comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.list_map Primrec.fst
      (shiftInstr_primrec.comp (hk.comp Primrec.fst) Primrec.snd).to₂)

theorem reduce_correct (d : HaltingInput) : ZeroHalts (reduce d) ↔ Halts d :=
  compile_correct d.1 d.2.1 d.2.2

/-- The ported reduction includes the actual computability witness required
by Mathlib's many-one reducibility, not just a definable function. -/
theorem halting_manyOneReducible_zeroHalting : Halts ≤₀ ZeroHalts :=
  ⟨reduce, reduce_primrec.to_comp, fun d => (reduce_correct d).symm⟩

/-- A universality proof may target arbitrary initial counter
values; the zero-initialization step and final source interface are now joined.
The reduction premise is deliberately visible and is not supplied here. -/
theorem source_of_halting_reduction
    (h : (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ Halts) :
    SourceUndecidability :=
  SourceUndecidability.of_halting_reduction (h.trans halting_manyOneReducible_zeroHalting)

end DistributedSynthesis.CounterMachine.MM2.ZeroInitialization
