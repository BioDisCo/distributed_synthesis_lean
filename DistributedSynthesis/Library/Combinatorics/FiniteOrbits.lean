/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate

/-! # Bounded search along a finite deterministic orbit

Any reachable value first occurs before the cardinality of the state space.
This makes reachability executable without an acyclicity assumption.
-/
namespace DistributedSynthesis.FiniteOrbits

variable {α : Type*} [Fintype α]

theorem reachable_iff_bounded (f : α → α) (x y : α) :
    (∃ n : Nat, (f^[n]) x = y) ↔
      ∃ n : Fin (Fintype.card α), (f^[n.val]) x = y := by
  constructor
  · intro h
    classical
    let n := Nat.find h
    have hn : (f^[n]) x = y := Nat.find_spec h
    have hdistinct : ∀ i j : Nat, i < j → j ≤ n → (f^[i]) x ≠ (f^[j]) x := by
      intro i j hij hj heq
      have hshort : (f^[n - j + i]) x = y := by
        rw [Function.iterate_add_apply, heq, ← Function.iterate_add_apply,
          Nat.sub_add_cancel hj]
        exact hn
      have hmin := Nat.find_min' h hshort
      change n ≤ n - j + i at hmin
      omega
    have hinj : Function.Injective (fun i : Fin (n + 1) => (f^[i.val]) x) := by
      intro i j heq
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · exact False.elim (hdistinct i.val j.val hij (by omega) heq)
      · exact hij
      · exact False.elim (hdistinct j.val i.val hij (by omega) heq.symm)
    have hc := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hc
    exact ⟨⟨n, by omega⟩, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n.val, hn⟩

/-- Finite search, with no oracle for the unbounded existential. -/
def reachableDecidable [DecidableEq α] (f : α → α) (x y : α) :
    Decidable (∃ n : Nat, (f^[n]) x = y) :=
  decidable_of_iff (∃ n : Fin (Fintype.card α), (f^[n.val]) x = y)
    (reachable_iff_bounded f x y).symm

end DistributedSynthesis.FiniteOrbits
