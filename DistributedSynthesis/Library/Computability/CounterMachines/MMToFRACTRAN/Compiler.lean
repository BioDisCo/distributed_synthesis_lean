/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Adapted from Dominique Larchey-Wendling and Yannick Forster's mm_fractran.v
and MM_FRACTRAN.v. See ../README.md for the two-phase layout variation.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMToFRACTRAN.Blocks

namespace DistributedSynthesis.CounterMachine.MMToFRACTRAN
variable {n : Nat}

noncomputable def code (base : Nat) : MM.Program n → FRACTRAN.Program
  | [] => []
  | ρ :: P => block base ρ ++ code (base+1) P

noncomputable def compile (P : MM.Program n) : FRACTRAN.Program := code 1 P

theorem lookup_cons (ρ : MM.Instr n) (P : MM.Program n) (base pc : Nat) :
    MM.lookup (ρ :: P) base pc = if pc = base then some ρ else MM.lookup P (base+1) pc := by
  by_cases he : pc = base
  · subst pc; simp [MM.lookup]
  · by_cases hl : base ≤ pc
    · have hp : base+1 ≤ pc := by omega
      have hd : pc-base = (pc-(base+1))+1 := by omega
      simp [MM.lookup,he,hl,hp,hd]
    · have hp : ¬ base+1 ≤ pc := by omega
      simp [MM.lookup,he,hl,hp]

theorem step_code_state (P : MM.Program n) (base : Nat) (x : MM.Cfg n) :
    FRACTRAN.step (code base P) (state x) =
      (MM.lookup P base x.1).map (fun _ => working x) := by
  induction P generalizing base with
  | nil => simp [code,FRACTRAN.step,MM.lookup]
  | cons ρ P ih =>
    rw [code,FRACTRAN.step_append,block_state,ih,lookup_cons]
    by_cases h : base = x.1
    · simp [h]
    · simp [h,Ne.symm h]

theorem step_code_working (P : MM.Program n) (base : Nat) (x : MM.Cfg n) :
    FRACTRAN.step (code base P) (working x) =
      (MM.lookup P base x.1).map (fun ρ => state (MM.next ρ x)) := by
  induction P generalizing base with
  | nil => simp [code,FRACTRAN.step,MM.lookup]
  | cons ρ P ih =>
    rw [code,FRACTRAN.step_append,block_working,ih,lookup_cons]
    by_cases h : base = x.1
    · simp [h]
    · simp [h,Ne.symm h]

theorem code_regular (P : MM.Program n) (base : Nat) : FRACTRAN.Regular (code base P) := by
  induction P generalizing base with
  | nil => simp [code,FRACTRAN.Regular]
  | cons ρ P ih => exact (FRACTRAN.regular_append _ _).mpr ⟨block_regular base ρ,ih (base+1)⟩

theorem compile_regular (P : MM.Program n) : FRACTRAN.Regular (compile P) := code_regular P 1

theorem instruction_progress (P : MM.Program n) (base : Nat) (x : MM.Cfg n) (ρ : MM.Instr n)
    (h : MM.lookup P base x.1 = some ρ) :
    StateTransition.Reaches₁ (FRACTRAN.step (code base P)) (state x) (state (MM.next ρ x)) := by
  have h₁ : FRACTRAN.step (code base P) (state x) = some (working x) := by rw [step_code_state,h]; rfl
  have h₂ : FRACTRAN.step (code base P) (working x) = some (state (MM.next ρ x)) := by
    rw [step_code_working,h]; rfl
  have r₁ : StateTransition.Reaches₁ (FRACTRAN.step (code base P)) (state x) (working x) :=
    Relation.TransGen.single (by simp [h₁])
  exact r₁.trans (Relation.TransGen.single (by simp [h₂]))

theorem instruction_two_steps (P : MM.Program n) (base : Nat) (x : MM.Cfg n) (ρ : MM.Instr n)
    (h : MM.lookup P base x.1 = some ρ) :
    FRACTRAN.runSteps (code base P) 2 (state x) = some (state (MM.next ρ x)) := by
  simp [FRACTRAN.runSteps,step_code_state,step_code_working,h]

theorem respects (P : MM.Program n) (base : Nat) :
    StateTransition.Respects (MM.step P base) (FRACTRAN.step (code base P)) (fun x y => state x = y) := by
  apply StateTransition.fun_respects.mpr
  intro x
  cases h : MM.lookup P base x.1 with
  | none => simp [MM.step,h,StateTransition.FRespects,step_code_state]
  | some ρ => simpa [MM.step,h,StateTransition.FRespects] using instruction_progress P base x ρ h

theorem halts_iff (P : MM.Program n) (base : Nat) (x : MM.Cfg n) :
    FRACTRAN.Halts (code base P,state x) ↔ MM.Terminates P base x :=
  StateTransition.tr_eval_dom (respects P base) rfl

theorem compile_correct (P : MM.Program n) (v : MM.Registers n) :
    FRACTRAN.Halts (compile P,state (1,v)) ↔ MM.Halts (P,v) := halts_iff P 1 (1,v)

theorem compile_regular_correct (P : MM.Program n) (v : MM.Registers n) :
    FRACTRAN.RegularHalts (compile P,state (1,v)) ↔ MM.Halts (P,v) := by
  simp only [FRACTRAN.RegularHalts,compile_regular,true_and,compile_correct]

end DistributedSynthesis.CounterMachine.MMToFRACTRAN
