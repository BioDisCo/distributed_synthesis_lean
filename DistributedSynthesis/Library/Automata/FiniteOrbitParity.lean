/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Combinatorics.FiniteOrbits
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators
import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-! # Executable parity tests for a finite deterministic orbit

A state recurs infinitely often precisely when it is reachable and returns
to itself after a positive number of steps. Both searches have a finite bound.
-/

namespace DistributedSynthesis.FiniteOrbitParity

variable {Q : Type*} [Fintype Q]

def Recurring (f : Q → Q) (x q : Q) : Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ (f^[k]) x = q

theorem recurring_iff (f : Q → Q) (x q : Q) : Recurring f x q ↔
    (∃ i : Fin (Fintype.card Q), (f^[i.val]) x = q) ∧
    (∃ j : Fin (Fintype.card Q), (f^[j.val + 1]) q = q) := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := h 0
    obtain ⟨k, hk, heq⟩ := h (i + 1)
    refine ⟨(FiniteOrbits.reachable_iff_bounded f x q).mp ⟨i, hi⟩, ?_⟩
    have hr : (f^[k - i - 1]) (f q) = q := by
      rw [← Function.iterate_succ_apply, ← hi, ← Function.iterate_add_apply]
      rw [show k - i - 1 + 1 + i = k by omega]
      exact heq.trans hi.symm
    obtain ⟨j, hj⟩ := (FiniteOrbits.reachable_iff_bounded f (f q) q).mp ⟨_, hr⟩
    exact ⟨j, by simpa only [Function.iterate_succ_apply] using hj⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ n
    refine ⟨(j.val + 1) * n + i.val, by nlinarith, ?_⟩
    rw [Function.iterate_add_apply, hi, Function.iterate_mul]
    exact Function.iterate_fixed hj n

def recurringDecidable [DecidableEq Q] (f : Q → Q) (x q : Q) :
    Decidable (Recurring f x q) :=
  decidable_of_iff
    ((∃ i : Fin (Fintype.card Q), (f^[i.val]) x = q) ∧
     (∃ j : Fin (Fintype.card Q), (f^[j.val + 1]) q = q))
    (recurring_iff f x q).symm

theorem priority_recurring_iff (f : Q → Q) (x : Q) (priority : Q → Nat) (p : Nat) :
    NatSeqSeenInfinitelyOften (fun n => priority ((f^[n]) x)) p ↔
      ∃ q, Recurring f x q ∧ priority q = p := by
  classical
  constructor
  · intro h
    obtain ⟨q, hq, hr⟩ :=
      DetParityAutomaton.exists_seenInfinitelyOften_of_frequently_mem_finset
        (fun n => (f^[n]) x) (Finset.univ.filter fun q => priority q = p)
        (by
          intro n
          obtain ⟨k, hk, heq⟩ := h n
          exact ⟨k, hk, by simp [heq]⟩)
    exact ⟨q, hr, (Finset.mem_filter.mp hq).2⟩
  · rintro ⟨q, hr, rfl⟩ n
    obtain ⟨k, hk, heq⟩ := hr n
    exact ⟨k, hk, congrArg priority heq⟩

theorem parity_iff (f : Q → Q) (x : Q) (priority : Q → Nat) :
    NatSeqMinEvenParity (fun n => priority ((f^[n]) x)) ↔
      ∃ q, Recurring f x q ∧ priority q % 2 = 0 ∧
        ∀ r, Recurring f x r → priority q ≤ priority r := by
  have heven (p : Nat) : DetParityAutomaton.NatEven p ↔ p % 2 = 0 := by
    constructor
    · rintro ⟨k, rfl⟩; omega
    · intro hp; exact ⟨p / 2, by omega⟩
  constructor
  · rintro ⟨p, hp, hr, hmin⟩
    obtain ⟨q, hq, rfl⟩ := (priority_recurring_iff f x priority p).mp hr
    exact ⟨q, hq, (heven _).mp hp, fun r h =>
      hmin _ ((priority_recurring_iff f x priority _).mpr ⟨r, h, rfl⟩)⟩
  · rintro ⟨q, hq, hp, hmin⟩
    refine ⟨priority q, (heven _).mpr hp,
      (priority_recurring_iff f x priority _).mpr ⟨q, hq, rfl⟩, ?_⟩
    intro p hr
    obtain ⟨r, h, rfl⟩ := (priority_recurring_iff f x priority p).mp hr
    exact hmin r h

/-- All tests are over the supplied finite carrier; no infinite-run decider is used. -/
def parityDecidable [DecidableEq Q] (f : Q → Q) (x : Q) (priority : Q → Nat) :
    Decidable (NatSeqMinEvenParity (fun n => priority ((f^[n]) x))) := by
  letI := recurringDecidable f x
  exact decidable_of_iff
    (∃ q, Recurring f x q ∧ priority q % 2 = 0 ∧
      ∀ r, Recurring f x r → priority q ≤ priority r)
    (parity_iff f x priority).symm

end DistributedSynthesis.FiniteOrbitParity
