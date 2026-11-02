/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of mma_jump, mma_incs, mma_transfert, and mma_mult_cst in
MMA/mma_utils.v at revision 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See ../README.md for provenance and scope.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA.Frame

namespace DistributedSynthesis.CounterMachine.MMA.Arithmetic
variable {n : Nat}

def jump (r : Fin n) (j : Nat) : Program n := [inc r,dec r j]
def incs (r : Fin n) (k : Nat) : Program n := List.replicate k (inc r)
def transfer (F : Frame n) (i : Nat) : Program n := [inc F.y,dec F.x i,dec F.y (i+3)]
def mult (F : Frame n) (k i : Nat) : Program n :=
  [dec F.x (i+3)] ++ (jump F.x (i+5+k) ++ (incs F.y k ++ jump F.x i))

@[simp] theorem jump_length (r : Fin n) (j : Nat) : (jump r j).length = 2 := rfl
@[simp] theorem incs_length (r : Fin n) (k : Nat) : (incs r k).length = k := by simp [incs]
@[simp] theorem transfer_length (F : Frame n) (i : Nat) : (transfer F i).length = 3 := rfl
@[simp] theorem mult_length (F : Frame n) (k i : Nat) : (mult F k i).length = 5+k := by simp [mult]; omega

theorem jump_correct (P : Program n) (r : Fin n) (i j : Nat) (h : Placed P i (jump r j))
    (v : Registers n) : Progress P (i,v) (j,v) := by
  have h₀ := h 0 (by simp [jump])
  have h₁ := h 1 (by simp [jump])
  simp only [jump,List.getElem?_cons_zero,List.getElem?_cons_succ,Nat.add_zero] at h₀ h₁
  apply runSteps_progress P 2 _ _ (by decide)
  simp [runSteps,step,next,inc,dec,h₀,h₁,Function.update_idem]

theorem incs_correct (F : Frame n) (P : Program n) (k i : Nat) (h : Placed P i (incs F.y k))
    (v : Registers n) (a b : Nat) : Compute P (i,F.regs v a b) (i+k,F.regs v a (b+k)) := by
  induction k generalizing i b with
  | zero => simpa using (Relation.ReflTransGen.refl : Compute P (i,F.regs v a b) (i,F.regs v a b))
  | succ k ih =>
    have hc : Placed P i (inc F.y :: incs F.y k) := by simpa [incs,List.replicate_succ] using h
    have hs : step P (i,F.regs v a b) = some (i+1,F.regs v a (b+1)) := by
      simp [step,hc.head,next,inc]
    have hs' : Compute P (i,F.regs v a b) (i+1,F.regs v a (b+1)) := .single (by simp [hs])
    have hr := hs'.trans (ih (i+1) hc.tail (b+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr

theorem transfer_correct (F : Frame n) (P : Program n) (i : Nat) (h : Placed P i (transfer F i))
    (v : Registers n) (a b : Nat) : Progress P (i,F.regs v a b) (i+3,F.regs v 0 (a+b)) := by
  have h₀ : lookup P i = some (inc F.y) := by simpa [transfer] using h 0 (by simp [transfer])
  have h₁ : lookup P (i+1) = some (dec F.x i) := by simpa [transfer] using h 1 (by simp [transfer])
  have h₂ : lookup P (i+2) = some (dec F.y (i+3)) := by simpa [transfer] using h 2 (by simp [transfer])
  induction a generalizing b with
  | zero =>
    apply runSteps_progress P 3 _ _ (by decide)
    simp [runSteps,step,next,inc,dec,h₀,h₁,h₂,Nat.add_assoc]
  | succ a ih =>
    have hs : runSteps P 2 (i,F.regs v (a+1) b) = some (i,F.regs v a (b+1)) := by
      simp [runSteps,step,next,inc,dec,h₀,h₁,Nat.add_assoc]
    have hr := (runSteps_progress P 2 _ _ (by decide) hs).trans (ih (b+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr

theorem mult_correct (F : Frame n) (P : Program n) (k i : Nat) (h : Placed P i (mult F k i))
    (v : Registers n) (a b : Nat) : Progress P (i,F.regs v a b) (i+5+k,F.regs v 0 (k*a+b)) := by
  have h₀ : lookup P i = some (dec F.x (i+3)) := h.left.head
  have hj : Placed P (i+1) (jump F.x (i+5+k)) := by simpa using h.right.left
  have hi : Placed P (i+3) (incs F.y k) := by simpa [Nat.add_assoc] using h.right.right.left
  have hb : Placed P (i+3+k) (jump F.x i) := by simpa [Nat.add_assoc] using h.right.right.right
  induction a generalizing b with
  | zero =>
    have hs : runSteps P 1 (i,F.regs v 0 b) = some (i+1,F.regs v 0 b) := by
      simp [runSteps,step,next,dec,h₀]
    simpa using (runSteps_progress P 1 _ _ (by decide) hs).trans (jump_correct P F.x _ _ hj _)
  | succ a ih =>
    have hs : runSteps P 1 (i,F.regs v (a+1) b) = some (i+3,F.regs v a b) := by
      simp [runSteps,step,next,dec,h₀]
    have hr := (runSteps_progress P 1 _ _ (by decide) hs).trans_left (incs_correct F P k _ hi v a b)
    have hr' := hr.trans (jump_correct P F.x _ _ hb _)
    have hr'' := hr'.trans (ih (b+k))
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr''

end DistributedSynthesis.CounterMachine.MMA.Arithmetic
