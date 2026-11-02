/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of mma_decs and mma_decs_copy in MMA/mma_utils.v.
The Boolean parameter unifies their otherwise identical induction. See ../README.md.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA.Arithmetic

namespace DistributedSynthesis.CounterMachine.MMA.Arithmetic
variable {n : Nat} (F : Frame n)

def copyOne (copy : Bool) : Program n := if copy then [inc F.y] else []
def subtract (copy : Bool) (yes no : Nat) : Nat → Nat → Program n
  | 0,_ => jump F.x yes
  | k+1,i => [dec F.x (i+3)] ++ (jump F.x no ++ (copyOne F copy ++
      subtract copy yes no k (i+3+(if copy then 1 else 0))))

@[simp] theorem copyOne_length (copy : Bool) : (copyOne F copy).length = if copy then 1 else 0 := by cases copy <;> rfl
@[simp] theorem subtract_length (copy : Bool) (yes no k i : Nat) :
    (subtract F copy yes no k i).length = 2+(3+(if copy then 1 else 0))*k := by
  induction k generalizing i with
  | zero => simp [subtract]
  | succ k ih => simp [subtract,ih,Nat.mul_add]; omega

theorem subtract_correct (P : Program n) (copy : Bool) (yes no k i : Nat)
    (h : Placed P i (subtract F copy yes no k i)) (v : Registers n) (a b : Nat) :
    Progress P (i,F.regs v a b)
      (if k ≤ a then yes else no,F.regs v (a-k) (b+(if copy then min k a else 0))) := by
  induction k generalizing i a b with
  | zero => simpa using jump_correct P F.x i yes h (F.regs v a b)
  | succ k ih =>
    have h₀ : lookup P i = some (dec F.x (i+3)) := h.left.head
    have hj : Placed P (i+1) (jump F.x no) := by simpa using h.right.left
    have hc : Placed P (i+3) (copyOne F copy) := by simpa [Nat.add_assoc] using h.right.right.left
    have hr : Placed P (i+3+(if copy then 1 else 0))
        (subtract F copy yes no k (i+3+(if copy then 1 else 0))) := by
      simpa [Nat.add_assoc] using h.right.right.right
    cases a with
    | zero =>
      have hs : runSteps P 1 (i,F.regs v 0 b) = some (i+1,F.regs v 0 b) := by
        simp [runSteps,step,next,dec,h₀]
      simpa using (runSteps_progress P 1 _ _ (by decide) hs).trans (jump_correct P F.x _ _ hj _)
    | succ a =>
      have hs : runSteps P 1 (i,F.regs v (a+1) b) = some (i+3,F.regs v a b) := by
        simp [runSteps,step,next,dec,h₀]
      have hc' : Compute P (i+3,F.regs v a b)
          (i+3+(if copy then 1 else 0),F.regs v a (b+(if copy then 1 else 0))) := by
        cases copy with
        | false => exact .refl
        | true =>
          have hh : lookup P (i+3) = some (inc F.y) := hc.head
          apply runSteps_compute P 1
          simp [runSteps,step,next,inc,hh,Nat.add_assoc]
      have hp := (runSteps_progress P 1 _ _ (by decide) hs).trans_left hc'
      have ht := hp.trans (ih _ hr a (b+(if copy then 1 else 0)))
      cases copy <;> simpa [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem subtract_le (P : Program n) (copy : Bool) (yes no k i : Nat)
    (h : Placed P i (subtract F copy yes no k i)) (v : Registers n) (a b : Nat) (hk : k ≤ a) :
    Progress P (i,F.regs v a b) (yes,F.regs v (a-k) (b+(if copy then k else 0))) := by
  simpa [hk,Nat.min_eq_left hk] using subtract_correct F P copy yes no k i h v a b

theorem subtract_lt (P : Program n) (copy : Bool) (yes no k i : Nat)
    (h : Placed P i (subtract F copy yes no k i)) (v : Registers n) (a b : Nat) (hk : a < k) :
    Progress P (i,F.regs v a b) (no,F.regs v 0 (b+(if copy then a else 0))) := by
  simpa [Nat.not_le.mpr hk,Nat.min_eq_right (Nat.le_of_lt hk),Nat.sub_eq_zero_of_le (Nat.le_of_lt hk)] using
    subtract_correct F P copy yes no k i h v a b

end DistributedSynthesis.CounterMachine.MMA.Arithmetic
