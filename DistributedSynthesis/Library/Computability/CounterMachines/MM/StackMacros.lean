/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of mm_push_Zero, mm_push_One, mm_pop and their correctness
proofs in MM/mm_utils.v, revision 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See ../README.md, ../upstream/mm_utils.v, and ../LICENSE-MPL-2.0.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MM.Arithmetic
import DistributedSynthesis.Library.Computability.CounterMachines.MM.StackEncoding

namespace DistributedSynthesis.CounterMachine.MM.StackMacros
variable {n : Nat} (F : Frame n)

def pushZero (i : Nat) : Program n := Arithmetic.transfer F i ++ Arithmetic.double F.swap (i+3)
def pushOne (i : Nat) : Program n := pushZero F i ++ [inc F.x]
def pop (i jf jt je : Nat) : Program n :=
  Arithmetic.transfer F i ++ (Arithmetic.divide F.swap (i+3) ++
    [dec F.x (i+13),inc F.x,dec F.z jf,dec F.y jt,dec F.z jt,inc F.x,dec F.z je])

theorem pushZero_correct (P : Program n) (base i : Nat) (h : Placed P base i (pushZero F i))
    (v : Registers n) (a : Nat) :
    Reaches₁ P base (i,F.regs v a 0 0) (i+7,F.regs v (2*a) 0 0) := by
  have hp : Placed P base i (Arithmetic.transfer F i ++ Arithmetic.double F.swap (i+3)) := h
  have ht := Arithmetic.transfer_correct F P base i hp.left v a 0
  have hd := Arithmetic.double_correct F.swap P base (i+3)
    (by simpa [Arithmetic.transfer] using hp.right) v a 0
  simp only [Nat.add_zero] at ht
  simp only [Frame.swap_regs,Nat.add_zero] at hd
  simpa [Nat.add_assoc] using ht.trans hd

theorem pushOne_correct (P : Program n) (base i : Nat) (h : Placed P base i (pushOne F i))
    (v : Registers n) (a : Nat) :
    Reaches₁ P base (i,F.regs v a 0 0) (i+8,F.regs v (2*a+1) 0 0) := by
  have hp : Placed P base i (pushZero F i ++ [inc F.x]) := h
  have ht := pushZero_correct F P base i hp.left v a
  have hh : lookup P base (i+7) = some (inc F.x) := by
    simpa [pushOne,pushZero,Arithmetic.transfer,Arithmetic.double] using h 7
      (by simp [pushOne,pushZero,Arithmetic.transfer,Arithmetic.double])
  have hr : runSteps P base 1 (i+7,F.regs v (2*a) 0 0) = some (i+8,F.regs v (2*a+1) 0 0) := by
    simp [runSteps,step,next,inc,hh,Nat.add_assoc]
  exact ht.trans (runSteps_reaches₁ P base 1 _ _ (by decide) hr)

theorem pop_divide (P : Program n) (base i jf jt je : Nat)
    (h : Placed P base i (pop F i jf jt je)) (v : Registers n) (a : Nat) (bit : Bool) :
    Reaches₁ P base (i,F.regs v (2*a+(bif bit then 1 else 0)) 0 0)
      (i+9,F.regs v a 0 (bif bit then 1 else 0)) := by
  have hp : Placed P base i (Arithmetic.transfer F i ++ (Arithmetic.divide F.swap (i+3) ++
      [dec F.x (i+13),inc F.x,dec F.z jf,dec F.y jt,dec F.z jt,inc F.x,dec F.z je])) := h
  have ht := Arithmetic.transfer_correct F P base i hp.left v (2*a+(bif bit then 1 else 0)) 0
  have hd := Arithmetic.divide_correct F.swap P base (i+3)
    (by simpa [Arithmetic.transfer] using hp.right.left) v a 0 bit
  simp only [Nat.add_zero] at ht
  simp only [Frame.swap_regs,Nat.add_zero] at hd
  simpa [Nat.add_assoc] using ht.trans hd

theorem pop_empty (P : Program n) (base i jf jt je : Nat)
    (h : Placed P base i (pop F i jf jt je)) (v : Registers n) :
    Reaches₁ P base (i,F.regs v 1 0 0) (je,F.regs v 1 0 0) := by
  have ht := pop_divide F P base i jf jt je h v 0 true
  simp only [Bool.cond_true,Nat.mul_zero,Nat.zero_add] at ht
  have h₉ : lookup P base (i+9) = some (dec F.x (i+13)) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 9 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₃ : lookup P base (i+13) = some (dec F.z jt) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 13 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₄ : lookup P base (i+14) = some (inc F.x) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 14 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₅ : lookup P base (i+15) = some (dec F.z je) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 15 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have hr : runSteps P base 4 (i+9,F.regs v 0 0 1) = some (je,F.regs v 1 0 0) := by
    simp [runSteps,step,next,inc,dec,h₉,h₁₃,h₁₄,h₁₅,Nat.add_assoc]
  exact ht.trans (runSteps_reaches₁ P base 4 _ _ (by decide) hr)

theorem pop_false (P : Program n) (base i jf jt je : Nat)
    (h : Placed P base i (pop F i jf jt je)) (v : Registers n) (a : Nat) (ha : 0 < a) :
    Reaches₁ P base (i,F.regs v (2*a) 0 0) (jf,F.regs v a 0 0) := by
  have ht := pop_divide F P base i jf jt je h v a false
  simp only [Bool.cond_false,Nat.add_zero] at ht
  have h₉ : lookup P base (i+9) = some (dec F.x (i+13)) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 9 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₀ : lookup P base (i+10) = some (inc F.x) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 10 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₁ : lookup P base (i+11) = some (dec F.z jf) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 11 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have hr : runSteps P base 3 (i+9,F.regs v a 0 0) = some (jf,F.regs v a 0 0) := by
    cases a with
    | zero => omega
    | succ a => simp [runSteps,step,next,inc,dec,h₉,h₁₀,h₁₁,Nat.add_assoc]
  exact ht.trans (runSteps_reaches₁ P base 3 _ _ (by decide) hr)

theorem pop_true (P : Program n) (base i jf jt je : Nat)
    (h : Placed P base i (pop F i jf jt je)) (v : Registers n) (a : Nat) (ha : 0 < a) :
    Reaches₁ P base (i,F.regs v (2*a+1) 0 0) (jt,F.regs v a 0 0) := by
  have ht := pop_divide F P base i jf jt je h v a true
  simp only [Bool.cond_true] at ht
  have h₉ : lookup P base (i+9) = some (dec F.x (i+13)) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 9 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₀ : lookup P base (i+10) = some (inc F.x) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 10 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₁ : lookup P base (i+11) = some (dec F.z jf) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 11 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have h₁₂ : lookup P base (i+12) = some (dec F.y jt) := by
    simpa [pop,Arithmetic.transfer,Arithmetic.divide] using h 12 (by simp [pop,Arithmetic.transfer,Arithmetic.divide])
  have hr : runSteps P base 4 (i+9,F.regs v a 0 1) = some (jt,F.regs v a 0 0) := by
    cases a with
    | zero => omega
    | succ a => simp [runSteps,step,next,inc,dec,h₉,h₁₀,h₁₁,h₁₂,Nat.add_assoc]
  exact ht.trans (runSteps_reaches₁ P base 4 _ _ (by decide) hr)

end DistributedSynthesis.CounterMachine.MM.StackMacros
