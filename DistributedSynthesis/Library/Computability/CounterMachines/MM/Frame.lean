/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Three-register frame lemmas for the Lean port of Dominique Larchey-Wendling's
MM/mm_utils.v. These frame lemmas are additions of the Lean adaptation.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MM

namespace DistributedSynthesis.CounterMachine.MM

structure Frame (n : Nat) where
  x : Fin n
  y : Fin n
  z : Fin n
  xy : x ≠ y
  xz : x ≠ z
  yz : y ≠ z

namespace Frame
variable {n : Nat} (F : Frame n) (v : Registers n)

def regs (a b c : Nat) : Registers n := fun r =>
  if r = F.x then a else if r = F.y then b else if r = F.z then c else v r

@[simp] theorem regs_x (a b c : Nat) : F.regs v a b c F.x = a := by simp [regs]
@[simp] theorem regs_y (a b c : Nat) : F.regs v a b c F.y = b := by simp [regs,F.xy.symm]
@[simp] theorem regs_z (a b c : Nat) : F.regs v a b c F.z = c := by simp [regs,F.xz.symm,F.yz.symm]

@[simp] theorem update_x (a b c d : Nat) :
    Function.update (F.regs v a b c) F.x d = F.regs v d b c := by
  funext r
  by_cases h : r = F.x
  · subst r; simp [regs]
  · simp [regs,h]

@[simp] theorem update_y (a b c d : Nat) :
    Function.update (F.regs v a b c) F.y d = F.regs v a d c := by
  funext r
  by_cases h : r = F.y
  · subst r; simp [regs,F.xy.symm]
  · simp [regs,h]

@[simp] theorem update_z (a b c d : Nat) :
    Function.update (F.regs v a b c) F.z d = F.regs v a b d := by
  funext r
  by_cases h : r = F.z
  · subst r; simp [regs,F.xz.symm,F.yz.symm]
  · simp [regs,h]

theorem regs_actual : F.regs v (v F.x) (v F.y) (v F.z) = v := by
  funext r
  simp only [regs]
  split_ifs <;> simp_all

theorem regs_updates (a b c : Nat) :
    F.regs v a b c = Function.update (Function.update (Function.update v F.x a) F.y b) F.z c := by
  calc
    F.regs v a b c = Function.update (Function.update
        (Function.update (F.regs v (v F.x) (v F.y) (v F.z)) F.x a) F.y b) F.z c := by simp
    _ = _ := by rw [F.regs_actual]

def swap : Frame n := ⟨F.y,F.x,F.z,F.xy.symm,F.yz,F.xz⟩

@[simp] theorem swap_x : F.swap.x = F.y := rfl
@[simp] theorem swap_y : F.swap.y = F.x := rfl
@[simp] theorem swap_z : F.swap.z = F.z := rfl

theorem swap_regs (a b c : Nat) : F.swap.regs v a b c = F.regs v b a c := by
  funext r
  by_cases hx : r = F.x
  · subst r; simp [regs,swap,F.xy]
  · by_cases hy : r = F.y
    · subst r; simp [regs,swap,F.xy.symm]
    · simp [regs,swap,hx,hy]

end Frame
end DistributedSynthesis.CounterMachine.MM
