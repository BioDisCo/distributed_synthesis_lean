/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of mma_fractran_one and its success/failure proofs in
MMA/fractran_mma.v, revision 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See ../README.md. No extra register or coprimality assumption is used.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMA.Division

namespace DistributedSynthesis.CounterMachine.FRACTRANToMMA
open MMA MMA.Arithmetic
variable {n : Nat} (F : MMA.Frame n)

def a1 (p i : Nat) := i+5+p
def a2 (p q i : Nat) := a1 p i+6+4*q
def a3 (p q i : Nat) := a2 p q i+5+3*q
def a4 (p q i : Nat) := a3 p q i+3
def a5 (p q i : Nat) := a4 p q i+2
def a6 (p q i : Nat) := a5 p q i+5+3*p

def one (p q ret i : Nat) : MMA.Program n :=
  mult F p i ++ (modulo F.swap q (a1 p i) (a2 p q i) (a5 p q i) ++
    (divide F q (a2 p q i) ++ (transfer F.swap (a3 p q i) ++
      (jump F.y ret ++ (divide F p (a5 p q i) ++ transfer F.swap (a6 p q i))))))

@[simp] theorem one_length (p q ret i : Nat) : (one F p q ret i).length = 29+4*p+7*q := by
  simp [one]; omega

theorem one_parts (P : MMA.Program n) (p q ret i : Nat) (h : MMA.Placed P i (one F p q ret i)) :
    MMA.Placed P i (mult F p i) ∧
    MMA.Placed P (a1 p i) (modulo F.swap q (a1 p i) (a2 p q i) (a5 p q i)) ∧
    MMA.Placed P (a2 p q i) (divide F q (a2 p q i)) ∧
    MMA.Placed P (a3 p q i) (transfer F.swap (a3 p q i)) ∧
    MMA.Placed P (a4 p q i) (jump F.y ret) ∧
    MMA.Placed P (a5 p q i) (divide F p (a5 p q i)) ∧
    MMA.Placed P (a6 p q i) (transfer F.swap (a6 p q i)) := by
  refine ⟨h.left,?_,?_,?_,?_,?_,?_⟩
  · simpa [a1,Nat.add_assoc] using h.right.left
  · simpa [a1,a2,Nat.add_assoc] using h.right.right.left
  · simpa [a1,a2,a3,Nat.add_assoc] using h.right.right.right.left
  · simpa [a1,a2,a3,a4,Nat.add_assoc] using h.right.right.right.right.left
  · simpa [a1,a2,a3,a4,a5,Nat.add_assoc] using h.right.right.right.right.right.left
  · convert h.right.right.right.right.right.right using 1
    simp [a1,a2,a3,a4,a5,a6]
    omega

theorem one_success (P : MMA.Program n) (p q ret i : Nat) (h : MMA.Placed P i (one F p q ret i))
    (hq : 0 < q) (v : MMA.Registers n) (x y : Nat) (hy : y*q = p*x) :
    MMA.Progress P (i,F.regs v x 0) (ret,F.regs v y 0) := by
  obtain ⟨h₀,h₁,h₂,h₃,h₄,_,_⟩ := one_parts F P p q ret i h
  have t₀ : MMA.Progress P (i,F.regs v x 0) (a1 p i,F.regs v 0 (y*q)) := by
    simpa [a1,hy] using mult_correct F P p i h₀ v x 0
  have t₁ : MMA.Progress P (a1 p i,F.regs v 0 (y*q)) (a2 p q i,F.regs v (y*q) 0) := by
    simpa using modulo_correct F.swap P q (a1 p i) (a2 p q i) (a5 p q i) h₁ v y 0 0 hq
  have t₂ : MMA.Progress P (a2 p q i,F.regs v (y*q) 0) (a3 p q i,F.regs v 0 y) := by
    simpa [a3] using divide_correct F P q (a2 p q i) h₂ v y 0 0 hq
  have t₃ : MMA.Progress P (a3 p q i,F.regs v 0 y) (a4 p q i,F.regs v y 0) := by
    simpa [a4] using transfer_correct F.swap P (a3 p q i) h₃ v y 0
  exact t₀.trans (t₁.trans (t₂.trans (t₃.trans (jump_correct P F.y _ _ h₄ _))))

theorem one_failure (P : MMA.Program n) (p q ret i : Nat) (h : MMA.Placed P i (one F p q ret i))
    (hq : 0 < q) (v : MMA.Registers n) (x : Nat) (hn : ¬ q ∣ p*x) :
    MMA.Progress P (i,F.regs v x 0) (i+(one F p q ret i).length,F.regs v x 0) := by
  obtain ⟨h₀,h₁,_,_,_,h₅,h₆⟩ := one_parts F P p q ret i h
  have hp : 0 < p := by
    by_contra hh
    have hz : p = 0 := by omega
    simp [hz] at hn
  have hr : (p*x)%q < q := Nat.mod_lt _ hq
  have hz : (p*x)%q ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hn
  have he : (p*x)/q*q+(p*x)%q = p*x := by simpa [Nat.mul_comm] using Nat.div_add_mod (p*x) q
  have t₀ : MMA.Progress P (i,F.regs v x 0) (a1 p i,F.regs v 0 (p*x)) := by
    simpa [a1] using mult_correct F P p i h₀ v x 0
  have t₁ : MMA.Progress P (a1 p i,F.regs v 0 (p*x)) (a5 p q i,F.regs v (p*x) 0) := by
    simpa [he,hz] using modulo_correct F.swap P q (a1 p i) (a2 p q i) (a5 p q i) h₁ v ((p*x)/q) ((p*x)%q) 0 hr
  have t₅ : MMA.Progress P (a5 p q i,F.regs v (p*x) 0) (a6 p q i,F.regs v 0 x) := by
    simpa [a6,Nat.mul_comm] using divide_correct F P p (a5 p q i) h₅ v x 0 0 hp
  have t₆ : MMA.Progress P (a6 p q i,F.regs v 0 x) (a6 p q i+3,F.regs v x 0) := by
    simpa using transfer_correct F.swap P (a6 p q i) h₆ v x 0
  have ht := t₀.trans (t₁.trans (t₅.trans t₆))
  have ha : a6 p q i+3 = i+(one F p q ret i).length := by simp [a6,a5,a4,a3,a2,a1]; omega
  simpa [ha] using ht

end DistributedSynthesis.CounterMachine.FRACTRANToMMA
