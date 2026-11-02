/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Port of MMA2_to_MM2.v by Dominique Larchey-Wendling (LORIA -- CNRS), from
the Coq library of undecidability proofs.
Upstream revision: 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
Upstream path: theories/MinskyMachines/Reductions/MMA2_to_MM2.v
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA
import DistributedSynthesis.Library.Computability.CounterMachines.ZeroInitializationComputable

/-! # From two-register MMA to the fixed MM2 interface

As in the Rocq proof, this is a change of representation, with exact instruction,
configuration, step, reachability, and halting correspondence. The compiler and
its composition with zero-initialization are additionally certified primitive
recursive for the explicit Lean encodings.
-/
namespace DistributedSynthesis.CounterMachine.MMA2ToMM2

def instrEquiv : MMA.Instr 2 ≃ MM2.Instr where
  toFun ρ := MM2.Instr.equivCode.symm (decide (ρ.1 = 1), ρ.2)
  invFun ρ := (if ρ.equivCode.1 then 1 else 0, ρ.equivCode.2)
  left_inv := by
    rintro ⟨r,j⟩
    fin_cases r <;> cases j <;> rfl
  right_inv := by intro ρ; cases ρ <;> rfl

def stateEquiv : MMA.Cfg 2 ≃ MM2.Cfg where
  toFun x := (x.1,(x.2 0,x.2 1))
  invFun x := (x.1,![x.2.1,x.2.2])
  left_inv := by
    rintro ⟨i,v⟩
    change (i, ![v 0,v 1]) = (i,v)
    congr 1
    funext r
    fin_cases r <;> rfl
  right_inv := by rintro ⟨i,a,b⟩; rfl

def compile (P : MMA.Program 2) : MM2.Program := P.map instrEquiv

theorem next_correct (ρ : MMA.Instr 2) (x : MMA.Cfg 2) :
    stateEquiv (MMA.next ρ x) = MM2.atomNext (instrEquiv ρ) (stateEquiv x) := by
  rcases ρ with ⟨r,j⟩
  rcases x with ⟨i,v⟩
  fin_cases r <;> cases j <;>
    simp [MMA.next, instrEquiv, stateEquiv, MM2.Instr.equivCode, MM2.atomNext]
  all_goals split_ifs <;> simp_all [stateEquiv]

theorem lookup_correct (P : MMA.Program 2) (i : Nat) :
    MM2.lookup (compile P) i = (MMA.lookup P i).map instrEquiv := by
  by_cases h : i = 0 <;> simp [MM2.lookup,MMA.lookup,compile,h,List.getElem?_map]

theorem step_correct (P : MMA.Program 2) (x y : MMA.Cfg 2) :
    MM2.Step (compile P) (stateEquiv x) (stateEquiv y) ↔ MMA.Step P x y := by
  constructor
  · rintro ⟨ρ,hl,ha⟩
    change MM2.lookup (compile P) x.1 = some ρ at hl
    rw [lookup_correct] at hl
    obtain ⟨τ,ht,rfl⟩ := Option.map_eq_some_iff.mp hl
    refine ⟨τ,ht,?_⟩
    apply stateEquiv.injective
    exact ((MM2.atom_iff _ _ _).mp ha).trans (next_correct τ x).symm
  · rintro ⟨ρ,hl,rfl⟩
    refine ⟨instrEquiv ρ, ?_, (MM2.atom_iff _ _ _).mpr (next_correct ρ x)⟩
    simpa [stateEquiv,hl] using lookup_correct P x.1

theorem reaches_forward {P : MMA.Program 2} {x y : MMA.Cfg 2}
    (h : MMA.Reaches P x y) :
    MM2.Reaches (compile P) (stateEquiv x) (stateEquiv y) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ((step_correct P _ _).mpr hs)

theorem reaches_backward {P : MMA.Program 2} {x y : MM2.Cfg}
    (h : MM2.Reaches (compile P) x y) :
    MMA.Reaches P (stateEquiv.symm x) (stateEquiv.symm y) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    apply ih.tail
    apply (step_correct P _ _).mp
    simpa using hs

theorem stops_correct (P : MMA.Program 2) (x : MMA.Cfg 2) :
    MM2.Stops (compile P) (stateEquiv x) ↔ MMA.Stops P x := by
  simp only [MM2.stops_iff, MMA.stops_iff]
  change MM2.lookup (compile P) x.1 = none ↔ _
  rw [lookup_correct,Option.map_eq_none_iff]

theorem terminates_correct (P : MMA.Program 2) (x : MMA.Cfg 2) :
    MM2.Terminates (compile P) (stateEquiv x) ↔ MMA.Terminates P x := by
  constructor
  · rintro ⟨y,hy,hs⟩
    refine ⟨stateEquiv.symm y, ?_, ?_⟩
    · simpa using reaches_backward hy
    · apply (stops_correct P _).mp
      simpa using hs
  · rintro ⟨y,hy,hs⟩
    exact ⟨stateEquiv y,reaches_forward hy,(stops_correct P y).mpr hs⟩

def reduce (d : MMA.HaltingInput 2) : MM2.HaltingInput :=
  (compile d.1,d.2 0,d.2 1)

theorem reduce_correct (d : MMA.HaltingInput 2) : MM2.Halts (reduce d) ↔ MMA.Halts d :=
  terminates_correct d.1 (1,d.2)

theorem instrEquiv_primrec : Primrec instrEquiv :=
  (Primrec.of_equiv_symm (e := MM2.Instr.equivCode)).comp
    (Primrec.pair ((Primrec.dom_finite (fun r : Fin 2 => decide (r = 1))).comp Primrec.fst)
      Primrec.snd)

theorem compile_primrec : Primrec compile :=
  Primrec.list_map Primrec.id (instrEquiv_primrec.comp Primrec.snd).to₂

theorem reduce_primrec : Primrec reduce :=
  Primrec.pair (compile_primrec.comp Primrec.fst)
    (Primrec.pair (Primrec.fin_app.comp Primrec.snd (Primrec.const 0))
      (Primrec.fin_app.comp Primrec.snd (Primrec.const 1)))

theorem halting_manyOneReducible : @MMA.Halts 2 ≤₀ MM2.Halts :=
  ⟨reduce,reduce_primrec.to_comp,fun d => (reduce_correct d).symm⟩

def toZero (d : MMA.HaltingInput 2) : MM2.Program :=
  MM2.ZeroInitialization.reduce (reduce d)

theorem toZero_primrec : Primrec toZero :=
  MM2.ZeroInitialization.reduce_primrec.comp reduce_primrec

theorem toZero_correct (d : MMA.HaltingInput 2) : MM2.ZeroHalts (toZero d) ↔ MMA.Halts d :=
  (MM2.ZeroInitialization.reduce_correct (reduce d)).trans (reduce_correct d)

theorem halting_manyOneReducible_zeroHalting : @MMA.Halts 2 ≤₀ MM2.ZeroHalts :=
  ⟨toZero,toZero_primrec.to_comp,fun d => (toZero_correct d).symm⟩

end DistributedSynthesis.CounterMachine.MMA2ToMM2
