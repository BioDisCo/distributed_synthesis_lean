/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of mma_isempty, mma_mod_cst and mma_div_cst in MMA/mma_utils.v.
All statements concern actual instruction lists with explicit ambient placement.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA.Subtract

namespace DistributedSynthesis.CounterMachine.MMA.Arithmetic
variable {n : Nat} (F : Frame n)

def empty (yes i : Nat) : Program n := [dec F.x (i+3)] ++ (jump F.x yes ++ [inc F.x])
def modulo (k i yes no : Nat) : Program n := empty F yes i ++ subtract F true i no k (i+4)
def divide (k i : Nat) : Program n :=
  subtract F false (i+2+3*k) (i+5+3*k) k i ++ ([inc F.y] ++ jump F.x i)

@[simp] theorem empty_length (yes i : Nat) : (empty F yes i).length = 4 := rfl
@[simp] theorem modulo_length (k i yes no : Nat) : (modulo F k i yes no).length = 6+4*k := by
  simp [modulo]; omega
@[simp] theorem divide_length (k i : Nat) : (divide F k i).length = 5+3*k := by
  simp [divide]; omega

theorem empty_correct (P : Program n) (yes i : Nat) (h : Placed P i (empty F yes i))
    (v : Registers n) (a b : Nat) :
    Progress P (i,F.regs v a b) (if a = 0 then yes else i+4,F.regs v a b) := by
  have h₀ : lookup P i = some (dec F.x (i+3)) := h.left.head
  have hj : Placed P (i+1) (jump F.x yes) := by simpa using h.right.left
  have h₃ : lookup P (i+3) = some (inc F.x) := by simpa [Nat.add_assoc] using h.right.right.head
  cases a with
  | zero =>
    have hs : runSteps P 1 (i,F.regs v 0 b) = some (i+1,F.regs v 0 b) := by
      simp [runSteps,step,next,dec,h₀]
    simpa using (runSteps_progress P 1 _ _ (by decide) hs).trans (jump_correct P F.x _ _ hj _)
  | succ a =>
    apply runSteps_progress P 2 _ _ (by decide)
    simp [runSteps,step,next,inc,dec,h₀,h₃,Nat.add_assoc]

theorem modulo_correct (P : Program n) (k i yes no : Nat)
    (h : Placed P i (modulo F k i yes no)) (v : Registers n) (u r b : Nat) (hr : r < k) :
    Progress P (i,F.regs v (u*k+r) b)
      (if r = 0 then yes else no,F.regs v 0 (b+(u*k+r))) := by
  have he : Placed P i (empty F yes i) := h.left
  have hs : Placed P (i+4) (subtract F true i no k (i+4)) := by simpa using h.right
  induction u generalizing b with
  | zero =>
    by_cases hz : r = 0
    · subst r; simpa using empty_correct F P yes i he v 0 b
    · have hp : Progress P (i,F.regs v r b) (i+4,F.regs v r b) := by
        simpa [hz] using empty_correct F P yes i he v r b
      simpa [hz] using hp.trans (subtract_lt F P true i no k (i+4) hs v r b hr)
  | succ u ih =>
    have hkpos : 0 < k := by omega
    have hn : (u+1)*k+r ≠ 0 := by positivity
    have hp : Progress P (i,F.regs v ((u+1)*k+r) b) (i+4,F.regs v ((u+1)*k+r) b) := by
      simpa only [if_neg hn] using empty_correct F P yes i he v ((u+1)*k+r) b
    have hk : k ≤ (u+1)*k+r := by nlinarith
    have hd : (u+1)*k+r-k = u*k+r := by simp [Nat.add_mul]; omega
    have ht := subtract_le F P true i no k (i+4) hs v ((u+1)*k+r) b hk
    simp only [hd,ite_true] at ht
    have hh := hp.trans (ht.trans (ih (b+k)))
    simpa [Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem divide_correct (P : Program n) (k i : Nat) (h : Placed P i (divide F k i))
    (v : Registers n) (u r b : Nat) (hr : r < k) :
    Progress P (i,F.regs v (u*k+r) b) (i+5+3*k,F.regs v 0 (b+u)) := by
  have hs : Placed P i (subtract F false (i+2+3*k) (i+5+3*k) k i) := h.left
  have hi : lookup P (i+2+3*k) = some (inc F.y) := by
    simpa [Nat.add_assoc] using h.right.left.head
  have hj : Placed P (i+3+3*k) (jump F.x i) := by
    convert h.right.right using 1
    simp
    omega
  induction u generalizing b with
  | zero => simpa using subtract_lt F P false _ _ k i hs v r b hr
  | succ u ih =>
    have hk : k ≤ (u+1)*k+r := by nlinarith
    have hd : (u+1)*k+r-k = u*k+r := by simp [Nat.add_mul]; omega
    have ht := subtract_le F P false _ _ k i hs v ((u+1)*k+r) b hk
    simp only [hd,Bool.false_eq_true,ite_false,Nat.add_zero] at ht
    have hi' : runSteps P 1 (i+2+3*k,F.regs v (u*k+r) b) =
        some (i+3+3*k,F.regs v (u*k+r) (b+1)) := by
      rw [runSteps,step,hi]
      simp [runSteps,next,inc]
      omega
    have hh := ht.trans ((runSteps_progress P 1 _ _ (by decide) hi').trans (jump_correct P F.x _ _ hj _))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh.trans (ih (b+1))

end DistributedSynthesis.CounterMachine.MMA.Arithmetic
