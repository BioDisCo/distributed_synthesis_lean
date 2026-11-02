/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.PrefixHoles
import DistributedSynthesis.Library.Combinatorics.FiniteRows
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryCoding

/-! Uniform prefix holes bound consecutive surviving reflected path indices.
This combines the finite-state bound with the actual reflected graph coding. -/

namespace Characterisation

open DistributedSynthesis

def LiveIndex (P : List Graph → Prop) (n j : Nat) : Prop :=
  ∃ h : List Graph, h.length = n ∧ pathIndex h = j ∧ P h

theorem aligned_holes_of_exact_prefix_holes (P : List Graph → Prop) (k n : Nat)
    (holes : ∀ h, ∃ u, u.length = k ∧ ¬ P (h ++ u)) :
    AlignedBlockHoles (LiveIndex P (n + k)) (3 ^ (n + k)) (3 ^ k) := by
  intro q fits
  have positive : 0 < 3 ^ k := by positivity
  have parentBound : q < 3 ^ n := by
    rw [pow_add] at fits
    nlinarith
  obtain ⟨h, hlen, hindex⟩ := pathIndex_surjective n q parentBound
  obtain ⟨u, ulen, missing⟩ := holes h
  have bounds := pathIndex_refinement h u
  refine ⟨pathIndex (h ++ u), ?_, ?_, ?_⟩
  · simpa [ulen, hindex, Nat.mul_comm] using bounds.1
  · simpa [ulen, hindex, Nat.mul_comm] using bounds.2
  · rintro ⟨v, vlen, vindex, live⟩
    have eqHistory : v = h ++ u := pathIndex_injective v (h ++ u)
      (by simp [vlen, hlen, ulen]) vindex
    exact missing (eqHistory ▸ live)

theorem uniform_prefix_holes_bound_rows (P : List Graph → Prop)
    (closed : PrefixClosed P) (holes : HasUniformPrefixHoles P) :
    ∃ K, ∀ t a b, a ≤ b → b ≤ 3 ^ t →
      (∀ j, a ≤ j → j < b → LiveIndex P t j) → b - a < K := by
  letI : Nonempty Graph := ⟨Graph.both⟩
  obtain ⟨k, hk⟩ := uniform_holes_exact_depth P closed holes
  refine ⟨2 * 3 ^ k, fun t a b hab hb allLive => ?_⟩
  by_cases shallow : t < k
  · have hpow : 3 ^ t ≤ 3 ^ k := by gcongr; omega
    have positive : 0 < 3 ^ k := by positivity
    omega
  · have depthEq : t = (t - k) + k := by omega
    rw [depthEq] at hb allLive
    exact live_interval_bound _ _ _ (by positivity)
      (aligned_holes_of_exact_prefix_holes P k (t - k) hk) a b hab hb allLive

theorem regular_prefix_holes_bound_rows {Q : Type*} [Fintype Q]
    (M : Recognizer Graph Q) (P : List Graph → Prop)
    (recognizes : ∀ w, P w ↔ M.eval w ∈ M.accept)
    (closed : PrefixClosed P) (holes : HasPrefixHoles P) :
    ∃ K, ∀ t a b, a ≤ b → b ≤ 3 ^ t →
      (∀ j, a ≤ j → j < b → LiveIndex P t j) → b - a < K :=
  uniform_prefix_holes_bound_rows P closed
    (uniformPrefixHoles_of_finite_dfa M P recognizes holes)

end Characterisation
