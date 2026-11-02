/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Adapted from the prime-power encoding of Dominique Larchey-Wendling and
Yannick Forster in FRACTRAN/mm_fractran.v, revision
11c41e0637f0c5219ad1c4c92d11609b7e072c31. See ../README.md.
This variant separates instruction entry and execution primes to support
self-jumps without a separate MM preprocessing pass.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MM
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace DistributedSynthesis.CounterMachine.MMToFRACTRAN
open scoped BigOperators

noncomputable def prime (i : Nat) : Nat := Nat.nth Nat.Prime i
theorem prime_prime (i : Nat) : Nat.Prime (prime i) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
theorem prime_injective : Function.Injective prime := Nat.nth_injective Nat.infinite_setOf_prime

noncomputable def entry (i : Nat) : Nat := prime (3*i)
noncomputable def active (i : Nat) : Nat := prime (3*i+1)
noncomputable def reg {n : Nat} (k : Fin n) : Nat := prime (3*k.val+2)

theorem entry_prime (i : Nat) : Nat.Prime (entry i) := prime_prime _
theorem active_prime (i : Nat) : Nat.Prime (active i) := prime_prime _
theorem reg_prime {n : Nat} (k : Fin n) : Nat.Prime (reg k) := prime_prime _
theorem entry_injective : Function.Injective entry := by
  intro i j h; have := prime_injective h; omega
theorem active_injective : Function.Injective active := by
  intro i j h; have := prime_injective h; omega
theorem reg_injective {n : Nat} : Function.Injective (@reg n) := by
  intro i j h; apply Fin.ext; have := prime_injective h; omega
theorem entry_ne_active (i j : Nat) : entry i ≠ active j := by
  intro h; have := prime_injective h; omega
theorem entry_ne_reg {n : Nat} (i : Nat) (k : Fin n) : entry i ≠ reg k := by
  intro h; have := prime_injective h; omega
theorem active_ne_reg {n : Nat} (i : Nat) (k : Fin n) : active i ≠ reg k := by
  intro h; have := prime_injective h; omega

noncomputable def registers {n : Nat} (v : MM.Registers n) : Nat := ∏ k, reg k ^ v k
noncomputable def state {n : Nat} (x : MM.Cfg n) : Nat := entry x.1 * registers x.2
noncomputable def working {n : Nat} (x : MM.Cfg n) : Nat := active x.1 * registers x.2

theorem registers_positive {n : Nat} (v : MM.Registers n) : 0 < registers v := by
  exact Finset.prod_pos (fun k _ => pow_pos (reg_prime k).pos _)

theorem prime_not_dvd_registers {n p : Nat} (hp : Nat.Prime p)
    (h : ∀ k : Fin n, p ≠ reg k) (v : MM.Registers n) : ¬ p ∣ registers v := by
  intro hd
  obtain ⟨k,_,hk⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  exact h k ((Nat.prime_dvd_prime_iff_eq hp (reg_prime k)).mp (hp.dvd_of_dvd_pow hk))

theorem entry_dvd_state {n : Nat} (i : Nat) (x : MM.Cfg n) :
    entry i ∣ state x ↔ i = x.1 := by
  rw [state,(entry_prime i).dvd_mul]
  simp [Nat.prime_dvd_prime_iff_eq (entry_prime i) (entry_prime x.1),
    prime_not_dvd_registers (entry_prime i) (entry_ne_reg i) x.2,entry_injective.eq_iff]

theorem active_not_dvd_state {n : Nat} (i : Nat) (x : MM.Cfg n) : ¬ active i ∣ state x := by
  rw [state,(active_prime i).dvd_mul]
  simp [Nat.prime_dvd_prime_iff_eq (active_prime i) (entry_prime x.1),
    (entry_ne_active x.1 i).symm,
    prime_not_dvd_registers (active_prime i) (active_ne_reg i) x.2]

theorem active_dvd_working {n : Nat} (i : Nat) (x : MM.Cfg n) :
    active i ∣ working x ↔ i = x.1 := by
  rw [working,(active_prime i).dvd_mul]
  simp [Nat.prime_dvd_prime_iff_eq (active_prime i) (active_prime x.1),
    prime_not_dvd_registers (active_prime i) (active_ne_reg i) x.2,active_injective.eq_iff]

theorem entry_not_dvd_working {n : Nat} (i : Nat) (x : MM.Cfg n) : ¬ entry i ∣ working x := by
  rw [working,(entry_prime i).dvd_mul]
  simp [Nat.prime_dvd_prime_iff_eq (entry_prime i) (active_prime x.1),entry_ne_active,
    prime_not_dvd_registers (entry_prime i) (entry_ne_reg i) x.2]

theorem registers_update {n : Nat} (v : MM.Registers n) (k : Fin n) (a : Nat) :
    registers (Function.update v k a) = reg k ^ a * ∏ j ∈ Finset.univ.erase k, reg j ^ v j := by
  rw [registers,Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ k)]
  simp only [Function.update_self,Finset.sdiff_singleton_eq_erase]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem registers_inc {n : Nat} (v : MM.Registers n) (k : Fin n) :
    registers (Function.update v k (v k+1)) = reg k * registers v := by
  rw [registers_update,registers,Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ k)]
  simp [pow_succ,Finset.sdiff_singleton_eq_erase,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

theorem registers_dec {n : Nat} (v : MM.Registers n) (k : Fin n) (h : 0 < v k) :
    reg k * registers (Function.update v k (v k-1)) = registers v := by
  have hh := registers_inc (Function.update v k (v k-1)) k
  simpa [Nat.sub_add_cancel h,Function.update_idem] using hh.symm

theorem reg_dvd_registers {n : Nat} (v : MM.Registers n) (k : Fin n) :
    reg k ∣ registers v ↔ 0 < v k := by
  constructor
  · intro hd
    obtain ⟨j,_,hj⟩ := ((reg_prime k).prime.dvd_finsetProd_iff _).mp hd
    have he : k = j := reg_injective ((Nat.prime_dvd_prime_iff_eq (reg_prime k) (reg_prime j)).mp
      ((reg_prime k).dvd_of_dvd_pow hj))
    subst j
    by_contra hn
    have hz : v k = 0 := by omega
    simpa [hz,(reg_prime k).not_dvd_one] using hj
  · intro h
    exact ⟨registers (Function.update v k (v k-1)),(registers_dec v k h).symm⟩

theorem reg_dvd_working {n : Nat} (x : MM.Cfg n) (k : Fin n) :
    reg k ∣ working x ↔ 0 < x.2 k := by
  rw [working,(reg_prime k).dvd_mul]
  simp [Nat.prime_dvd_prime_iff_eq (reg_prime k) (active_prime x.1),
    (active_ne_reg x.1 k).symm,reg_dvd_registers]

end DistributedSynthesis.CounterMachine.MMToFRACTRAN
