/-
Lean development: the paper authors listed in AUTHORS.md at the repository root.
The Mathlib credits below refer to reused upstream definitions and proofs.
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0; see ../LICENSE-APACHE-2.0.

Uses Mario Carneiro's partial-recursive-code compiler and simulation proofs
in Mathlib.Computability.TuringMachine.{Config,ToPartrec} (Apache-2.0).
This is not a port of Rocq's binary stack machine model; see ../README.md.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.FiniteControl
import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.InputEncoding
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

/-! # An unconditional finite-control stack-machine halting source

One fixed universal program suffices: only its initial word varies with the
source code. Thus choosing this constant program does not require a computable
compiler from arbitrary partial-recursive proofs. The input-dependent map is
explicit and primitive recursive. The resulting machine has four stacks, four
stack symbols, five local-store values, and finitely many control labels.

This closes the Mathlib side of the bridge. The separate `TM2ToBSM` compiler and
`BSMSource` composition connect it to Rocq BSM without coupling this source to
that target. Separate compositions now reach six-register MM and regular
FRACTRAN. `SourcePort.source` completes the chain through MMA2 to zero-MM2.
-/
namespace DistributedSynthesis.CounterMachine.MathlibBridge
open Turing Turing.PartrecToTM2

def universal (n : Nat) : Part Nat :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0

theorem universal_partrec : Partrec universal :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)

theorem exists_universalCode : ∃ c : ToPartrec.Code, ∀ n : Nat,
    c.eval [n] = (universal n).map (fun m => [m]) := by
  have hf : @Nat.Partrec' 1 (fun v : List.Vector Nat 1 => universal v.head) :=
    Nat.Partrec'.part_iff₁.mpr universal_partrec
  obtain ⟨c,hc⟩ := ToPartrec.Code.exists_code hf
  exact ⟨c,fun n => hc ⟨[n],rfl⟩⟩

/-- A single constant program, not a proposed effective syntax compiler. -/
noncomputable def universalCode : ToPartrec.Code := Classical.choose exists_universalCode

theorem universalCode_correct (p : Nat.Partrec.Code) :
    universalCode.eval [Encodable.encode p] =
      (Nat.Partrec.Code.eval p 0).map (fun m => [m]) := by
  simpa [universal] using Classical.choose_spec exists_universalCode (Encodable.encode p)

def support (c : ToPartrec.Code) : Finset Λ' := codeSupp c .halt

def initialLabel (c : ToPartrec.Code) : support c :=
  ⟨trNormal c .halt,(tr_supports c .halt).1⟩

def program (c : ToPartrec.Code) : support c → TM2.Stmt (fun _ : K' => Γ') (support c) (Option Γ') :=
  FiniteControl.machine (support c) (initialLabel c) tr

def initial (c : ToPartrec.Code) (w : List Γ') :
    TM2.Cfg (fun _ : K' => Γ') (support c) (Option Γ') :=
  ⟨some (initialLabel c),none,K'.elim w [] [] []⟩

/-- Halting is termination of the actual finite-control stack transition system. -/
def WordHalts (c : ToPartrec.Code) (w : List (Fin 4)) : Prop :=
  (StateTransition.eval (TM2.step (program c)) (initial c (InputEncoding.decodeWord w))).Dom

theorem wordHalts_iff_reaches_halt (c : ToPartrec.Code) (w : List (Fin 4)) :
    WordHalts c w ↔ ∃ y,
      TM2.Reaches (program c) (initial c (InputEncoding.decodeWord w)) y ∧ y.l = none := by
  rw [WordHalts,Part.dom_iff_mem]
  apply exists_congr
  intro y
  rw [StateTransition.mem_eval]
  have he : TM2.step (program c) y = none ↔ y.l = none := by
    cases y with
    | mk q v stk => cases q <;> simp [TM2.step]
  exact and_congr Iff.rfl he

theorem halts_encoded_list (c : ToPartrec.Code) (v : List Nat) :
    (StateTransition.eval (TM2.step (program c)) (initial c (trList v))).Dom ↔
      (c.eval v).Dom := by
  have h := FiniteControl.halts_iff (support c) (initialLabel c) tr
    (tr_supports c .halt).2 (initial c (trList v))
  change _ ↔ (StateTransition.eval (TM2.step tr) (PartrecToTM2.init c v)).Dom at h
  rw [tr_eval] at h
  exact h

theorem inputWord_correct (p : Nat.Partrec.Code) :
    WordHalts universalCode (InputEncoding.inputWord p) ↔ (Nat.Partrec.Code.eval p 0).Dom := by
  unfold WordHalts
  rw [InputEncoding.inputWord_correct,halts_encoded_list,universalCode_correct]
  rfl

theorem halting_manyOneReducible :
    (fun p : Nat.Partrec.Code => (Nat.Partrec.Code.eval p 0).Dom) ≤₀ WordHalts universalCode :=
  ⟨InputEncoding.inputWord,InputEncoding.inputWord_primrec.to_comp,
    fun p => (inputWord_correct p).symm⟩

theorem wordHalting_not_computable : ¬ ComputablePred (WordHalts universalCode) := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible h)

deriving instance Fintype for K'

theorem four_stacks : Fintype.card K' = 4 := by decide
theorem four_symbols : Fintype.card Γ' = 4 := by decide
theorem five_store_values : Fintype.card (Option Γ') = 5 := by decide
theorem finite_control (c : ToPartrec.Code) : Finite (support c) := inferInstance

end DistributedSynthesis.CounterMachine.MathlibBridge
