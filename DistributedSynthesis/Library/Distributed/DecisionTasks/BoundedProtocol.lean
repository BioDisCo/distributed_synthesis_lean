/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib
import DistributedSynthesis.Library.Distributed.DecisionTasks.Model

/-! # Finite-round protocols and arbitrary-state solvability

At a fixed round, a total local output map can be implemented by retaining
the simulated state at that round. These constructions apply to arbitrary
graph adversaries. The IIS converse is in `IISBoundedProtocol`.
-/

namespace DistributedSynthesis.DecisionTasks

variable {P : Type} {I O : P → Type} {St : Type}

/-- Simulate exactly `k` rounds and retain the resulting local state. -/
def Protocol.stopAfter (A : Protocol P I St) (k : ℕ) : Protocol P I (ℕ × St) where
  init p x := (0, A.init p x)
  trans p s messages := if s.1 < k then
    (s.1 + 1, A.trans p s.2 ((fun z => (z.1, z.2.2)) '' messages)) else s

theorem Protocol.stopAfter_run (A : Protocol P I St) (k : ℕ)
    (σ : ℕ → Event P) (x : ∀ p, I p) (r : ℕ) (p : P) :
    (A.stopAfter k).run σ x r p = (min r k, A.run σ x (min r k) p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    simp only [Protocol.run, ih]
    change (if min r k < k then
      (min r k + 1, A.trans p (A.run σ x (min r k) p)
        ((fun z => (z.1, z.2.2)) ''
          ((fun q => (q, (min r k, A.run σ x (min r k) q))) '' (σ r).inN p)))
      else (min r k, A.run σ x (min r k) p)) = _
    by_cases hr : r < k
    · have hmin : min r k = r := Nat.min_eq_left (by omega)
      have hmin' : min (r + 1) k = r + 1 := Nat.min_eq_left (by omega)
      simp only [hmin, hr, if_pos, hmin', Set.image_image]
      rfl
    · have hmin : min r k = k := Nat.min_eq_right (by omega)
      have hmin' : min (r + 1) k = k := Nat.min_eq_right (by omega)
      simp only [hmin, hmin', lt_self_iff_false, if_false]

/-- A total local decision map at one depth. Its state space is unrestricted. -/
def Task.BoundedSolvable (T : Task P I O) (adv : Set (ℕ → Event P)) : Prop :=
  ∃ (k : ℕ) (St : Type) (A : Protocol P I St) (out : ∀ p, St → O p),
    ∀ σ ∈ adv, ∀ x, T.allows x (fun p => out p (A.run σ x k p))

theorem Task.BoundedSolvable.solvable {T : Task P I O}
    {adv : Set (ℕ → Event P)} (h : T.BoundedSolvable adv) : T.Solvable adv := by
  obtain ⟨k, St, A, out, h⟩ := h
  let decision : ∀ p, ℕ × St → Option (O p) :=
    fun p s => if k ≤ s.1 then some (out p s.2) else none
  refine ⟨ℕ × St, A.stopAfter k, decision, ?_⟩
  have at_round (σ : ℕ → Event P) (x : ∀ p, I p) (r : ℕ) (p : P) :
      decision p ((A.stopAfter k).run σ x r p) =
        if k ≤ r then some (out p (A.run σ x k p)) else none := by
    rw [Protocol.stopAfter_run]
    dsimp [decision]
    by_cases hr : k ≤ r
    · simp [hr]
    · have hm : min r k = r := Nat.min_eq_left (by omega)
      simp [hm, hr]
  constructor
  · intro σ _ x p
    exact ⟨k, out p (A.run σ x k p), by simp only [at_round, le_refl, if_true]⟩
  · intro σ _ x p r r' hrr o ho
    rw [at_round] at ho ⊢
    split_ifs at ho with hr
    · simpa only [if_pos (le_trans hr hrr)] using ho
  · intro σ hσ x o ho
    have heq : o = fun p => out p (A.run σ x k p) := by
      funext p
      obtain ⟨r, hr⟩ := ho p
      rw [at_round] at hr
      split_ifs at hr
      · exact (Option.some.inj hr).symm
    rw [heq]
    exact h σ hσ x


end DistributedSynthesis.DecisionTasks
