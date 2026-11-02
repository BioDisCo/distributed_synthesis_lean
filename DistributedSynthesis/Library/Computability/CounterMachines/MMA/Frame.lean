/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/- SPDX-License-Identifier: MPL-2.0 -/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA.Execution

namespace DistributedSynthesis.CounterMachine.MMA

/-- Two working registers; all other registers retain their original contents. -/
structure Frame (n : Nat) where
  x : Fin n
  y : Fin n
  ne : x ≠ y

namespace Frame
variable {n : Nat} (F : Frame n)
def regs (v : Registers n) (a b : Nat) : Registers n :=
  fun r => if r = F.x then a else if r = F.y then b else v r
@[simp] theorem regs_x (v : Registers n) (a b : Nat) : F.regs v a b F.x = a := by simp [regs]
@[simp] theorem regs_y (v : Registers n) (a b : Nat) : F.regs v a b F.y = b := by simp [regs,F.ne.symm]
@[simp] theorem update_x (v : Registers n) (a b c : Nat) :
    Function.update (F.regs v a b) F.x c = F.regs v c b := by
  funext r; by_cases h : r = F.x <;> simp [regs,Function.update,h]
@[simp] theorem update_y (v : Registers n) (a b c : Nat) :
    Function.update (F.regs v a b) F.y c = F.regs v a c := by
  funext r; by_cases h : r = F.y
  · subst r; simp [regs,Function.update,F.ne.symm]
  · by_cases hx : r = F.x <;> simp [regs,Function.update,h,hx,F.ne]
theorem regs_actual (v : Registers n) : F.regs v (v F.x) (v F.y) = v := by
  funext r; by_cases hx : r = F.x <;> by_cases hy : r = F.y <;> simp [regs,hx,hy,F.ne.symm]
def swap : Frame n := ⟨F.y,F.x,F.ne.symm⟩
@[simp] theorem swap_x : F.swap.x = F.y := rfl
@[simp] theorem swap_y : F.swap.y = F.x := rfl
@[simp] theorem swap_regs (v : Registers n) (a b : Nat) : F.swap.regs v a b = F.regs v b a := by
  funext r; by_cases hx : r = F.x <;> by_cases hy : r = F.y <;> simp_all [regs,swap,F.ne,F.ne.symm]
end Frame
end DistributedSynthesis.CounterMachine.MMA
