/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Lean adaptation of Dominique Larchey-Wendling's stack_enc in MM/mm_utils.v,
Coq library of undecidability proofs, revision
11c41e0637f0c5219ad1c4c92d11609b7e072c31.
Explicit primitive-recursiveness proofs are additions of this port.
-/
import Mathlib.Computability.Primrec.List

namespace DistributedSynthesis.CounterMachine.MM.StackEncoding

def encode (s : List Bool) : Nat := s.rec 1 (fun b _ ih => 2*ih + (bif b then 1 else 0))

@[simp] theorem encode_nil : encode [] = 1 := rfl
@[simp] theorem encode_false (s : List Bool) : encode (false :: s) = 2*encode s := by simp [encode]
@[simp] theorem encode_true (s : List Bool) : encode (true :: s) = 2*encode s+1 := rfl

theorem positive (s : List Bool) : 0 < encode s := by
  induction s with
  | nil => decide
  | cons b s ih => cases b <;> simp only [encode_false,encode_true] <;> omega

theorem empty_iff (s : List Bool) : encode s = 1 ↔ s = [] := by
  cases s with
  | nil => simp
  | cons b s => have h := positive s; cases b <;> simp <;> omega

theorem tail_code (b : Bool) (s : List Bool) : encode (b :: s) / 2 = encode s := by
  cases b <;> simp only [encode_false,encode_true] <;> omega

theorem top_code (b : Bool) (s : List Bool) : encode (b :: s) % 2 = (bif b then 1 else 0) := by
  cases b <;> simp

theorem encode_primrec : Primrec encode :=
  Primrec.list_rec Primrec.id (Primrec.const 1)
    ((Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))).to₂)

end DistributedSynthesis.CounterMachine.MM.StackEncoding
