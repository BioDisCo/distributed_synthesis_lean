/-
Lean development: the paper authors listed in AUTHORS.md at the repository root.
The Mathlib credits below refer to reused upstream definitions and proofs.
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0; see ../LICENSE-APACHE-2.0.

Binary-alphabet specialization of Mario Carneiro's Mathlib stack-machine source.
The alphabet compiler and its effectivity proof are additions of this project.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.BinaryStacks
import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.UniversalStackMachine

/-! # Unconditional halting source with binary stacks

The program, stack indices, and initial label are fixed. Input words are now
binary. Control still uses Mathlib's structured TM2 statements, not Rocq's BSM
instruction list. The separate `CounterMachines.TM2ToBSM` module eliminates
finite store and structured control; `BSMSource` composes it with this source.
Those target modules are deliberately not imported here.
-/
namespace DistributedSynthesis.CounterMachine.MathlibBridge.BinaryUniversal
open Turing Turing.PartrecToTM2

def codec : BinaryStacks.Codec Γ' where
  encode
    | .consₗ => (false,false)
    | .cons => (false,true)
    | .bit0 => (true,false)
    | .bit1 => (true,true)
  decode a b := bif a then (bif b then .bit1 else .bit0)
    else (bif b then .cons else .consₗ)
  decode_encode a := by cases a <;> rfl

def block (a : Fin 4) : List Bool :=
  let p := codec.encode (InputEncoding.symbol a)
  [p.1,p.2]

def encodeWord (w : List (Fin 4)) : List Bool := w.flatMap block

theorem encodeWord_correct (w : List (Fin 4)) :
    encodeWord w = codec.word (InputEncoding.decodeWord w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simpa [encodeWord,block,InputEncoding.decodeWord] using
      congrArg (fun l => (codec.encode (InputEncoding.symbol a)).1 ::
        (codec.encode (InputEncoding.symbol a)).2 :: l) ih

theorem encodeWord_primrec : Primrec encodeWord :=
  Primrec.list_flatMap Primrec.id ((Primrec.dom_finite block).comp Primrec.snd).to₂

def program (c : ToPartrec.Code) := BinaryStacks.machine codec (MathlibBridge.program c)

def initial (c : ToPartrec.Code) (w : List Bool) :
    TM2.Cfg (fun _ : K' => Bool) (support c) (BinaryStacks.Store (Option Γ')) :=
  ⟨some (initialLabel c),(none,none),fun k => match k with | .main => w | _ => []⟩

theorem initial_correct (c : ToPartrec.Code) (w : List (Fin 4)) :
    initial c (encodeWord w) =
      BinaryStacks.cfg codec (MathlibBridge.initial c (InputEncoding.decodeWord w)) := by
  rw [encodeWord_correct]
  unfold initial BinaryStacks.cfg MathlibBridge.initial
  congr 1
  funext k
  cases k <;> rfl

def WordHalts (c : ToPartrec.Code) (w : List Bool) : Prop :=
  (StateTransition.eval (TM2.step (program c)) (initial c w)).Dom

theorem wordHalts_correct (c : ToPartrec.Code) (w : List (Fin 4)) :
    WordHalts c (encodeWord w) ↔ MathlibBridge.WordHalts c w := by
  unfold WordHalts MathlibBridge.WordHalts
  rw [initial_correct]
  exact BinaryStacks.halts_iff codec _ _

theorem wordHalting_manyOneReducible :
    MathlibBridge.WordHalts universalCode ≤₀ WordHalts universalCode :=
  ⟨encodeWord,encodeWord_primrec.to_comp,fun w => (wordHalts_correct _ w).symm⟩

def inputWord (p : Nat.Partrec.Code) : List Bool := encodeWord (InputEncoding.inputWord p)

theorem inputWord_primrec : Primrec inputWord :=
  encodeWord_primrec.comp InputEncoding.inputWord_primrec

theorem inputWord_correct (p : Nat.Partrec.Code) :
    WordHalts universalCode (inputWord p) ↔ (p.eval 0).Dom :=
  (wordHalts_correct _ _).trans (MathlibBridge.inputWord_correct p)

theorem halting_manyOneReducible :
    (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀ WordHalts universalCode :=
  ⟨inputWord,inputWord_primrec.to_comp,fun p => (inputWord_correct p).symm⟩

theorem wordHalting_not_computable : ¬ ComputablePred (WordHalts universalCode) := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible h)

theorem fifteen_store_values : Fintype.card (BinaryStacks.Store (Option Γ')) = 15 := by decide

end DistributedSynthesis.CounterMachine.MathlibBridge.BinaryUniversal
