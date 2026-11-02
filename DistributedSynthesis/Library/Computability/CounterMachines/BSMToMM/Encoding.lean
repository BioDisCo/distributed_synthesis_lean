/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of bsm_state_enc in MM/mm_comp.v, revision
11c41e0637f0c5219ad1c4c92d11609b7e072c31. See ../README.md.
The explicit primitive-recursiveness proof is added by this port.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.BSM
import DistributedSynthesis.Library.Computability.CounterMachines.MM.Frame
import DistributedSynthesis.Library.Computability.CounterMachines.MM.StackEncoding
import Mathlib.Tactic.FinCases

namespace DistributedSynthesis.CounterMachine.BSMToMM
variable {n : Nat}

def tmp₁ : Fin (2+n) := Fin.castAdd n (0 : Fin 2)
def tmp₂ : Fin (2+n) := Fin.castAdd n (1 : Fin 2)
def reg (k : Fin n) : Fin (2+n) := Fin.natAdd 2 k

theorem reg_ne_tmp₁ (k : Fin n) : reg k ≠ tmp₁ := by
  intro h; have hv := congrArg Fin.val h; simp [reg,tmp₁] at hv
theorem reg_ne_tmp₂ (k : Fin n) : reg k ≠ tmp₂ := by
  intro h; have hv := congrArg Fin.val h; simp [reg,tmp₂] at hv; omega

def frame (k : Fin n) : MM.Frame (2+n) :=
  ⟨reg k,tmp₁,tmp₂,reg_ne_tmp₁ k,reg_ne_tmp₂ k,by intro h; have hv := congrArg Fin.val h; simp [tmp₁,tmp₂] at hv⟩

def state (s : BSM.Stacks n) : MM.Registers (2+n) :=
  Fin.addCases (fun _ : Fin 2 => 0) (fun k => MM.StackEncoding.encode (s k))

@[simp] theorem state_tmp₁ (s : BSM.Stacks n) : state s tmp₁ = 0 := by simp [state,tmp₁]
@[simp] theorem state_tmp₂ (s : BSM.Stacks n) : state s tmp₂ = 0 := by simp [state,tmp₂]
@[simp] theorem state_reg (s : BSM.Stacks n) (k : Fin n) :
    state s (reg k) = MM.StackEncoding.encode (s k) := by simp [state,reg]

theorem state_update (s : BSM.Stacks n) (k : Fin n) (l : List Bool) :
    state (Function.update s k l) = Function.update (state s) (reg k) (MM.StackEncoding.encode l) := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · have hn : Fin.castAdd n a ≠ reg k := by
      intro h; have hv := congrArg Fin.val h; simp [reg] at hv; omega
    simp [state,hn]
  · by_cases h : b = k
    · subst b; simp [state,reg]
    · have hn : reg b ≠ reg k := by
        intro hh
        apply h
        apply Fin.ext
        have hv := congrArg Fin.val hh
        simpa [reg] using hv
      change state (Function.update s k l) (reg b) =
        Function.update (state s) (reg k) (MM.StackEncoding.encode l) (reg b)
      rw [state_reg,Function.update_of_ne h,Function.update_of_ne hn,state_reg]

theorem frame_start (s : BSM.Stacks n) (k : Fin n) :
    (frame k).regs (state s) (MM.StackEncoding.encode (s k)) 0 0 = state s := by
  simpa [frame] using (frame k).regs_actual (state s)

theorem frame_finish (s : BSM.Stacks n) (k : Fin n) (l : List Bool) :
    (frame k).regs (state s) (MM.StackEncoding.encode l) 0 0 = state (Function.update s k l) := by
  calc
    _ = Function.update ((frame k).regs (state s) (MM.StackEncoding.encode (s k)) 0 0)
        (reg k) (MM.StackEncoding.encode l) :=
      ((frame k).update_x (state s) (MM.StackEncoding.encode (s k)) 0 0 (MM.StackEncoding.encode l)).symm
    _ = Function.update (state s) (reg k) (MM.StackEncoding.encode l) := by rw [frame_start]
    _ = _ := (state_update s k l).symm

theorem state_primrec : Primrec (@state n) := by
  apply Primrec.fin_curry.mpr
  have hh : Primrec₂ (fun (j : Fin (2+n)) (s : BSM.Stacks n) => state s j) := by
    apply Primrec.fin_curry₁.mpr
    intro j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simpa [state] using (Primrec.const (0 : Nat) : Primrec (fun _ : BSM.Stacks n => 0))
    · simpa [state] using MM.StackEncoding.encode_primrec.comp
        (Primrec.fin_app.comp Primrec.id (Primrec.const b))
  exact (hh.comp Primrec.snd Primrec.fst).to₂

end DistributedSynthesis.CounterMachine.BSMToMM
