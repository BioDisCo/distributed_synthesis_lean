/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of mm_transfert, mm_mul2, mm_div2 and their loop proofs in
MM/mm_utils.v, revision 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See ../README.md, ../upstream/mm_utils.v, and ../LICENSE-MPL-2.0.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MM.Frame

/-! # Register arithmetic used by the BSM simulation

Every statement below concerns actual INC/DEC instruction lists in an ambient
MM program. Register x is consumed; y accumulates its contents or quotient;
z is the zero/remainder register. Other registers are preserved by the frame.
All loop proofs establish strict progress, even for zero input.
-/
namespace DistributedSynthesis.CounterMachine.MM.Arithmetic
variable {n : Nat} (F : Frame n)

def transfer (i : Nat) : Program n := [dec F.x (i+3),inc F.y,dec F.z i]
def double (i : Nat) : Program n := [dec F.x (i+4),inc F.y,inc F.y,dec F.z i]
def divide (i : Nat) : Program n :=
  [dec F.x (i+6),inc F.z,dec F.x (i+6),dec F.z (i+4),inc F.y,dec F.z i]

theorem transfer_correct (P : Program n) (base i : Nat) (h : Placed P base i (transfer F i))
    (v : Registers n) (a b : Nat) :
    Reaches₁ P base (i,F.regs v a b 0) (i+3,F.regs v 0 (a+b) 0) := by
  have h₀ : lookup P base i = some (dec F.x (i+3)) := by
    simpa [transfer] using h 0 (by simp [transfer])
  have h₁ : lookup P base (i+1) = some (inc F.y) := by
    simpa [transfer] using h 1 (by simp [transfer])
  have h₂ : lookup P base (i+2) = some (dec F.z i) := by
    simpa [transfer] using h 2 (by simp [transfer])
  induction a generalizing b with
  | zero =>
    apply runSteps_reaches₁ P base 1 _ _ (by decide)
    simp [runSteps,step,next,dec,h₀]
  | succ a ih =>
    have hr : runSteps P base 3 (i,F.regs v (a+1) b 0) = some (i,F.regs v a (b+1) 0) := by
      simp [runSteps,step,next,inc,dec,h₀,h₁,h₂,Nat.add_assoc]
    have hh := (runSteps_reaches₁ P base 3 _ _ (by decide) hr).trans (ih (b+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem double_correct (P : Program n) (base i : Nat) (h : Placed P base i (double F i))
    (v : Registers n) (a b : Nat) :
    Reaches₁ P base (i,F.regs v a b 0) (i+4,F.regs v 0 (2*a+b) 0) := by
  have h₀ : lookup P base i = some (dec F.x (i+4)) := by
    simpa [double] using h 0 (by simp [double])
  have h₁ : lookup P base (i+1) = some (inc F.y) := by
    simpa [double] using h 1 (by simp [double])
  have h₂ : lookup P base (i+2) = some (inc F.y) := by
    simpa [double] using h 2 (by simp [double])
  have h₃ : lookup P base (i+3) = some (dec F.z i) := by
    simpa [double] using h 3 (by simp [double])
  induction a generalizing b with
  | zero =>
    apply runSteps_reaches₁ P base 1 _ _ (by decide)
    simp [runSteps,step,next,dec,h₀]
  | succ a ih =>
    have hr : runSteps P base 4 (i,F.regs v (a+1) b 0) = some (i,F.regs v a (b+2) 0) := by
      simp [runSteps,step,next,inc,dec,h₀,h₁,h₂,h₃,Nat.add_assoc]
    have hh := (runSteps_reaches₁ P base 4 _ _ (by decide) hr).trans (ih (b+2))
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem divide_correct (P : Program n) (base i : Nat) (h : Placed P base i (divide F i))
    (v : Registers n) (a b : Nat) (bit : Bool) :
    Reaches₁ P base (i,F.regs v (2*a+(bif bit then 1 else 0)) b 0)
      (i+6,F.regs v 0 (a+b) (bif bit then 1 else 0)) := by
  have h₀ : lookup P base i = some (dec F.x (i+6)) := by
    simpa [divide] using h 0 (by simp [divide])
  have h₁ : lookup P base (i+1) = some (inc F.z) := by
    simpa [divide] using h 1 (by simp [divide])
  have h₂ : lookup P base (i+2) = some (dec F.x (i+6)) := by
    simpa [divide] using h 2 (by simp [divide])
  have h₃ : lookup P base (i+3) = some (dec F.z (i+4)) := by
    simpa [divide] using h 3 (by simp [divide])
  have h₄ : lookup P base (i+4) = some (inc F.y) := by
    simpa [divide] using h 4 (by simp [divide])
  have h₅ : lookup P base (i+5) = some (dec F.z i) := by
    simpa [divide] using h 5 (by simp [divide])
  induction a generalizing b with
  | zero =>
    cases bit with
    | false =>
      apply runSteps_reaches₁ P base 1 _ _ (by decide)
      simp [runSteps,step,next,dec,h₀]
    | true =>
      apply runSteps_reaches₁ P base 3 _ _ (by decide)
      simp [runSteps,step,next,inc,dec,h₀,h₁,h₂,Nat.add_assoc]
  | succ a ih =>
    have hr : runSteps P base 6 (i,F.regs v (2*(a+1)+(bif bit then 1 else 0)) b 0) =
        some (i,F.regs v (2*a+(bif bit then 1 else 0)) (b+1) 0) := by
      cases bit <;> simp [runSteps,step,next,inc,dec,h₀,h₁,h₂,h₃,h₄,h₅,Nat.mul_add,Nat.add_assoc]
    have hh := (runSteps_reaches₁ P base 6 _ _ (by decide) hr).trans (ih (b+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

end DistributedSynthesis.CounterMachine.MM.Arithmetic
