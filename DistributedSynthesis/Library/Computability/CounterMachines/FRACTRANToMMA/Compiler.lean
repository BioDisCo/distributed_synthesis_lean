/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of the ordered scan and halting proof in MMA/fractran_mma.v
and FRACTRAN_to_MMA2.v. Ordinary halting is the target; the final register-
zeroing postlude is omitted. See ../README.md.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRANToMMA.Fraction
import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRAN

namespace DistributedSynthesis.CounterMachine.FRACTRANToMMA
open MMA MMA.Arithmetic
variable {n : Nat}

def scan (F : MMA.Frame n) (ret : Nat) : FRACTRAN.Program → Nat → MMA.Program n
  | [],_ => []
  | (p,q) :: Q,i => one F p q ret i ++ scan F ret Q (i+(one F p q ret i).length)

theorem scan_success (F : MMA.Frame n) (P : MMA.Program n) (ret : Nat) (Q : FRACTRAN.Program)
    (hQ : FRACTRAN.Regular Q) (i : Nat) (h : MMA.Placed P i (scan F ret Q i))
    (v : MMA.Registers n) (x y : Nat) (hs : FRACTRAN.step Q x = some y) :
    MMA.Progress P (i,F.regs v x 0) (ret,F.regs v y 0) := by
  induction Q generalizing i with
  | nil => simp [FRACTRAN.step] at hs
  | cons f Q ih =>
    obtain ⟨p,q⟩ := f
    have hq : 0 < q := Nat.pos_of_ne_zero (hQ (p,q) (by simp))
    have ht : FRACTRAN.Regular Q := fun f hf => hQ f (by simp [hf])
    by_cases hd : q ∣ p*x
    · have he : q*(p*x/q) = p*x := Nat.mul_div_cancel' hd
      have ha := FRACTRAN.applyFraction_eq_some (f := (p,q)) (Nat.ne_of_gt hq) he
      have hy : p*x/q = y := by simpa [FRACTRAN.step,ha] using hs
      apply one_success F P p q ret i h.left hq v x y
      rw [hy] at he
      simpa [Nat.mul_comm] using he
    · have ha := FRACTRAN.applyFraction_eq_none (f := (p,q)) hd
      have hs' : FRACTRAN.step Q x = some y := by simpa [FRACTRAN.step,ha] using hs
      exact (one_failure F P p q ret i h.left hq v x hd).trans (ih ht _ h.right hs')

theorem scan_failure (F : MMA.Frame n) (P : MMA.Program n) (ret : Nat) (Q : FRACTRAN.Program)
    (hQ : FRACTRAN.Regular Q) (i : Nat) (h : MMA.Placed P i (scan F ret Q i))
    (v : MMA.Registers n) (x : Nat) (hs : FRACTRAN.step Q x = none) :
    MMA.Compute P (i,F.regs v x 0) (i+(scan F ret Q i).length,F.regs v x 0) := by
  induction Q generalizing i with
  | nil => simpa [scan] using (Relation.ReflTransGen.refl : MMA.Compute P (i,F.regs v x 0) (i,F.regs v x 0))
  | cons f Q ih =>
    obtain ⟨p,q⟩ := f
    have hq : 0 < q := Nat.pos_of_ne_zero (hQ (p,q) (by simp))
    have ht : FRACTRAN.Regular Q := fun f hf => hQ f (by simp [hf])
    have hd : ¬ q ∣ p*x := by
      intro hd
      have ha := FRACTRAN.applyFraction_eq_some (f := (p,q)) (Nat.ne_of_gt hq) (Nat.mul_div_cancel' hd)
      simp [FRACTRAN.step,ha] at hs
    have ha := FRACTRAN.applyFraction_eq_none (f := (p,q)) hd
    have hs' : FRACTRAN.step Q x = none := by simpa [FRACTRAN.step,ha] using hs
    have hr := (one_failure F P p q ret i h.left hq v x hd).to_reflTransGen.trans (ih ht _ h.right hs')
    simpa [scan,List.length_append,Nat.add_assoc] using hr

def frame : MMA.Frame 2 := ⟨0,1,by decide⟩
def initial (x : Nat) : MMA.Registers 2 := ![x,0]
@[simp] theorem frame_initial (x : Nat) : frame.regs (fun _ => 0) x 0 = initial x := by
  funext r; fin_cases r <;> rfl

def compile (Q : FRACTRAN.Program) : MMA.Program 2 :=
  scan frame 1 Q 1 ++ jump frame.y 0

theorem compile_success (Q : FRACTRAN.Program) (hQ : FRACTRAN.Regular Q) (x y : Nat)
    (hs : FRACTRAN.step Q x = some y) :
    MMA.Progress (compile Q) (1,initial x) (1,initial y) := by
  have h := (MMA.placed_self (compile Q)).left
  simpa using scan_success frame (compile Q) 1 Q hQ 1 h (fun _ => 0) x y hs

theorem compile_failure (Q : FRACTRAN.Program) (hQ : FRACTRAN.Regular Q) (x : Nat)
    (hs : FRACTRAN.step Q x = none) :
    MMA.Progress (compile Q) (1,initial x) (0,initial x) := by
  have h := MMA.placed_self (compile Q)
  have hr : MMA.Compute (compile Q) (1,initial x) (1+(scan frame 1 Q 1).length,initial x) := by
    simpa using scan_failure frame (compile Q) 1 Q hQ 1 h.left (fun _ => 0) x hs
  exact Relation.TransGen.trans_right hr (jump_correct (compile Q) frame.y _ 0 h.right _)

/-- An immediately stuck source state is related to the target after its final
failed scan. The test is a finite one-step computation, not an eventual-halting oracle. -/
def boundary (Q : FRACTRAN.Program) (x : Nat) : MMA.Cfg 2 :=
  (if FRACTRAN.step Q x = none then 0 else 1,initial x)

theorem initial_to_boundary (Q : FRACTRAN.Program) (hQ : FRACTRAN.Regular Q) (x : Nat) :
    MMA.Compute (compile Q) (1,initial x) (boundary Q x) := by
  by_cases hs : FRACTRAN.step Q x = none
  · simpa [boundary,hs] using (compile_failure Q hQ x hs).to_reflTransGen
  · simpa [boundary,hs] using (Relation.ReflTransGen.refl : MMA.Compute (compile Q) (1,initial x) (1,initial x))

theorem respects (Q : FRACTRAN.Program) (hQ : FRACTRAN.Regular Q) :
    StateTransition.Respects (FRACTRAN.step Q) (MMA.step (compile Q)) (fun x y => boundary Q x = y) := by
  apply StateTransition.fun_respects.mpr
  intro x
  cases hs : FRACTRAN.step Q x with
  | none => simp [StateTransition.FRespects,boundary,hs,MMA.step,MMA.lookup]
  | some y =>
    have hr := (compile_success Q hQ x y hs).trans_left (initial_to_boundary Q hQ y)
    simpa [StateTransition.FRespects,boundary,hs] using hr

theorem compile_correct (Q : FRACTRAN.Program) (hQ : FRACTRAN.Regular Q) (x : Nat) :
    MMA.Halts (compile Q,initial x) ↔ FRACTRAN.Halts (Q,x) := by
  change MMA.Terminates (compile Q) (1,initial x) ↔ _
  rw [MMA.terminates_iff_eval,StateTransition.reaches_eval (initial_to_boundary Q hQ x)]
  exact StateTransition.tr_eval_dom (respects Q hQ) rfl

theorem initial_primrec : Primrec initial := by
  apply Primrec.fin_curry.mpr
  have h : Primrec₂ (fun k : Fin 2 => fun x : Nat => initial x k) := by
    apply Primrec.fin_curry₁.mpr
    intro k
    fin_cases k
    · exact Primrec.id
    · exact Primrec.const 0
  exact (h.comp Primrec.snd Primrec.fst).to₂

end DistributedSynthesis.CounterMachine.FRACTRANToMMA
