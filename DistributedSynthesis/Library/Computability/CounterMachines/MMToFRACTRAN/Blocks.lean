/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Adapted from Dominique Larchey-Wendling and Yannick Forster's mm_fractran.v.
The private execution phase is an addition of this port. See ../README.md.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRAN
import DistributedSynthesis.Library.Computability.CounterMachines.MMToFRACTRAN.Encoding

namespace DistributedSynthesis.CounterMachine.MMToFRACTRAN
variable {n : Nat}

noncomputable def enter (i : Nat) : FRACTRAN.Fraction := (active i,entry i)
noncomputable def actions (i : Nat) (ρ : MM.Instr n) : FRACTRAN.Program :=
  match ρ.2 with
  | none => [(entry (i+1)*reg ρ.1,active i)]
  | some j => [(entry (i+1),active i*reg ρ.1),(entry j,active i)]
noncomputable def block (i : Nat) (ρ : MM.Instr n) : FRACTRAN.Program := enter i :: actions i ρ

theorem blocked_by_prime (p : Nat) (hp : Nat.Prime p) (f : FRACTRAN.Fraction) (x : Nat)
    (hd : p ∣ f.2) (hn : ¬ p ∣ f.1) (hx : ¬ p ∣ x) : FRACTRAN.applyFraction f x = none := by
  apply FRACTRAN.applyFraction_eq_none
  intro h
  exact (hp.dvd_mul.mp (hd.trans h)).elim hn hx

theorem entry_not_dvd_active (i j : Nat) : ¬ entry i ∣ active j := by
  simp [Nat.prime_dvd_prime_iff_eq (entry_prime i) (active_prime j),entry_ne_active]
theorem active_not_dvd_entry (i j : Nat) : ¬ active i ∣ entry j := by
  simpa [Nat.prime_dvd_prime_iff_eq (active_prime i) (entry_prime j)] using (entry_ne_active j i).symm
theorem active_not_dvd_reg (i : Nat) (k : Fin n) : ¬ active i ∣ reg k := by
  simp [Nat.prime_dvd_prime_iff_eq (active_prime i) (reg_prime k),active_ne_reg]

theorem actions_blocked (i : Nat) (ρ : MM.Instr n) (x : Nat) (hx : ¬ active i ∣ x) :
    FRACTRAN.step (actions i ρ) x = none := by
  have h (f : FRACTRAN.Fraction) (hd : active i ∣ f.2) (hn : ¬ active i ∣ f.1) :=
    blocked_by_prime (active i) (active_prime i) f x hd hn hx
  cases he : ρ.2 with
  | none =>
    have hh := h (entry (i+1)*reg ρ.1,active i) dvd_rfl (by
      simp [(active_prime i).dvd_mul,active_not_dvd_entry,active_not_dvd_reg])
    simp [actions,he,FRACTRAN.step,hh]
  | some j =>
    have h₁ := h (entry (i+1),active i*reg ρ.1) (dvd_mul_right _ _) (active_not_dvd_entry _ _)
    have h₂ := h (entry j,active i) dvd_rfl (active_not_dvd_entry _ _)
    simp [actions,he,FRACTRAN.step,h₁,h₂]

theorem enter_state (x : MM.Cfg n) : FRACTRAN.applyFraction (enter x.1) (state x) = some (working x) := by
  apply FRACTRAN.applyFraction_eq_some (entry_prime x.1).ne_zero
  simp [enter,state,working,Nat.mul_comm,Nat.mul_left_comm]

theorem enter_blocked (i : Nat) (x : Nat) (hx : ¬ entry i ∣ x) :
    FRACTRAN.applyFraction (enter i) x = none :=
  blocked_by_prime (entry i) (entry_prime i) (enter i) x dvd_rfl (entry_not_dvd_active i i) hx

theorem block_state (i : Nat) (ρ : MM.Instr n) (x : MM.Cfg n) :
    FRACTRAN.step (block i ρ) (state x) = if i = x.1 then some (working x) else none := by
  by_cases h : i = x.1
  · subst i; simp [block,FRACTRAN.step,enter_state]
  · have hh := enter_blocked i (state x) (by simpa [entry_dvd_state] using h)
    simp [block,FRACTRAN.step,hh,actions_blocked i ρ _ (active_not_dvd_state i x),h]

theorem actions_working (i : Nat) (ρ : MM.Instr n) (v : MM.Registers n) :
    FRACTRAN.step (actions i ρ) (working (i,v)) = some (state (MM.next ρ (i,v))) := by
  cases he : ρ.2 with
  | none =>
    have hh : FRACTRAN.applyFraction (entry (i+1)*reg ρ.1,active i) (working (i,v)) =
        some (state (i+1,Function.update v ρ.1 (v ρ.1+1))) := by
      apply FRACTRAN.applyFraction_eq_some (active_prime i).ne_zero
      simp [state,working,registers_inc,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    simpa [actions,he,FRACTRAN.step,MM.next] using hh
  | some j =>
    by_cases hz : v ρ.1 = 0
    · have h₁ : FRACTRAN.applyFraction (entry (i+1),active i*reg ρ.1) (working (i,v)) = none := by
        apply blocked_by_prime (reg ρ.1) (reg_prime ρ.1) _ _ (dvd_mul_left _ _)
        · simpa [Nat.prime_dvd_prime_iff_eq (reg_prime ρ.1) (entry_prime (i+1))] using
            (entry_ne_reg (i+1) ρ.1).symm
        · simp [reg_dvd_working,hz]
      have h₂ : FRACTRAN.applyFraction (entry j,active i) (working (i,v)) = some (state (j,v)) := by
        apply FRACTRAN.applyFraction_eq_some (active_prime i).ne_zero
        simp [state,working,Nat.mul_comm,Nat.mul_left_comm]
      simp [actions,he,FRACTRAN.step,h₁,h₂,MM.next,hz]
    · have hp : 0 < v ρ.1 := Nat.pos_of_ne_zero hz
      have hh : FRACTRAN.applyFraction (entry (i+1),active i*reg ρ.1) (working (i,v)) =
          some (state (i+1,Function.update v ρ.1 (v ρ.1-1))) := by
        apply FRACTRAN.applyFraction_eq_some (Nat.mul_ne_zero (active_prime i).ne_zero (reg_prime ρ.1).ne_zero)
        change active i * reg ρ.1 * (entry (i+1) * registers (Function.update v ρ.1 (v ρ.1-1))) =
          entry (i+1) * (active i * registers v)
        calc
          _ = entry (i+1) * (active i * (reg ρ.1 * registers (Function.update v ρ.1 (v ρ.1-1)))) := by ac_rfl
          _ = _ := by rw [registers_dec v ρ.1 hp]
      simp [actions,he,FRACTRAN.step,hh,MM.next,hz]

theorem block_working (i : Nat) (ρ : MM.Instr n) (x : MM.Cfg n) :
    FRACTRAN.step (block i ρ) (working x) =
      if i = x.1 then some (state (MM.next ρ x)) else none := by
  have hh := enter_blocked i (working x) (entry_not_dvd_working i x)
  simp only [block,FRACTRAN.step,hh,Option.none_or]
  by_cases h : i = x.1
  · subst i
    simpa [actions_working] using actions_working x.1 ρ x.2
  · simp [h,actions_blocked i ρ (working x) (by simpa [active_dvd_working] using h)]

theorem block_regular (i : Nat) (ρ : MM.Instr n) : FRACTRAN.Regular (block i ρ) := by
  cases he : ρ.2 with
  | none => simp [FRACTRAN.Regular,block,enter,actions,he,(entry_prime i).ne_zero,(active_prime i).ne_zero]
  | some j => simp [FRACTRAN.Regular,block,enter,actions,he,(entry_prime i).ne_zero,
      (active_prime i).ne_zero,(reg_prime ρ.1).ne_zero]

end DistributedSynthesis.CounterMachine.MMToFRACTRAN
