/-
Lean development: the paper authors listed in AUTHORS.md at the repository root.
The Mathlib credits below refer to reused upstream definitions and proofs.
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0; see ../LICENSE-APACHE-2.0.

Certifies the finite-word input encoding used by Mario Carneiro's Mathlib
partial-recursive-function-to-stack-machine construction (Apache-2.0).
-/
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.Primrec.List

/-! # Primitive-recursive input words for the Mathlib stack machine

The four symbol codes are 0 = list separator, 1 = number separator,
2 = bit zero, 3 = bit one. Numbers are little endian, without leading zeroes
at the most significant end. Primitive recursiveness is proved using binary
increment iterated `n` times; no efficiency bound is asserted.
-/
namespace DistributedSynthesis.CounterMachine.MathlibBridge.InputEncoding
open Turing.PartrecToTM2

def carry (l : List Bool) : List Bool :=
  l.rec [true] (fun b bs ih => bif b then false :: ih else true :: bs)

@[simp] theorem carry_nil : carry [] = [true] := rfl
@[simp] theorem carry_false (l : List Bool) : carry (false::l) = true::l := rfl
@[simp] theorem carry_true (l : List Bool) : carry (true::l) = false::carry l := rfl

theorem carry_primrec : Primrec carry :=
  Primrec.list_rec Primrec.id (Primrec.const [true])
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.const false) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).to₂

def bits (n : Nat) : List Bool := n.rec [] (fun _ l => carry l)

theorem bits_primrec : Primrec bits :=
  Primrec.nat_rec₁ [] (carry_primrec.comp Primrec.snd).to₂

def posBits : PosNum → List Bool
  | .one => [true]
  | .bit0 n => false :: posBits n
  | .bit1 n => true :: posBits n

def numBits : Num → List Bool
  | .zero => []
  | .pos n => posBits n

theorem posBits_succ (n : PosNum) : posBits n.succ = carry (posBits n) := by
  induction n <;> simp_all [PosNum.succ,posBits]

theorem numBits_succ (n : Num) : numBits n.succ = carry (numBits n) := by
  cases n <;> simp [Num.succ,Num.succ',numBits,posBits_succ,posBits]

theorem bits_eq (n : Nat) : bits n = numBits (n : Num) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change carry (bits n) = numBits ((n + 1 : Nat) : Num)
    simp only [ih,Nat.cast_add,Nat.cast_one,Num.add_one,numBits_succ]

def bitCode (b : Bool) : Fin 4 := if b then 3 else 2
def symbol (a : Fin 4) : Γ' :=
  match a.val with
  | 0 => Γ'.consₗ
  | 1 => Γ'.cons
  | 2 => Γ'.bit0
  | _ => Γ'.bit1
def decodeWord (w : List (Fin 4)) : List Γ' := w.map symbol
def numberWord (n : Nat) : List (Fin 4) := (bits n).map bitCode
def inputWord (c : Nat.Partrec.Code) : List (Fin 4) := numberWord (Encodable.encode c) ++ [1]

theorem posBits_tr (n : PosNum) : (posBits n).map (fun b => symbol (bitCode b)) = trPosNum n := by
  induction n <;> simp_all [posBits,trPosNum,bitCode,symbol]

theorem numberWord_correct (n : Nat) : decodeWord (numberWord n) = trNat n := by
  simp only [decodeWord,numberWord,List.map_map,bits_eq,trNat]
  generalize (n : Num) = m
  cases m <;> simp [numBits,trNum,posBits_tr,Function.comp_def]

theorem inputWord_correct (c : Nat.Partrec.Code) :
    decodeWord (inputWord c) = trList [Encodable.encode c] := by
  change (numberWord (Encodable.encode c) ++ [1]).map symbol = _
  rw [List.map_append]
  change decodeWord (numberWord (Encodable.encode c)) ++ [Γ'.cons] = _
  simp [numberWord_correct]

theorem numberWord_primrec : Primrec numberWord :=
  Primrec.list_map bits_primrec ((Primrec.dom_finite bitCode).comp Primrec.snd).to₂

theorem inputWord_primrec : Primrec inputWord :=
  Primrec.list_append.comp (numberWord_primrec.comp Primrec.encode) (Primrec.const [1])

end DistributedSynthesis.CounterMachine.MathlibBridge.InputEncoding
