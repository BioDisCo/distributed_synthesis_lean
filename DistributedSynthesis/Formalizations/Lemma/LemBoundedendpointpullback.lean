/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Tactic

/-!
# Bounded endpoint-window pullbacks
-/

namespace DistributedSynthesis

/-- The endpoint-window pullback bound `β(c)=ceil(c/3)+1` on natural numbers. -/
def endpointPullbackBound (c : Nat) : Nat :=
  (c + 2) / 3 + 1

/-- Above radius two, one endpoint-window pullback never increases the radius. -/
theorem endpointPullbackBound_le_self_of_two_le
    {c : Nat} (h : 2 ≤ c) :
    endpointPullbackBound c ≤ c := by
  unfold endpointPullbackBound
  omega

/-- At radii at most two, one endpoint-window pullback remains within radius two. -/
theorem endpointPullbackBound_le_two_of_le_two
    {c : Nat} (h : c ≤ 2) :
    endpointPullbackBound c ≤ 2 := by
  unfold endpointPullbackBound
  omega

/-- A single endpoint-window pullback is bounded by `max c 2`. -/
theorem endpointPullbackBound_le_max (c : Nat) :
    endpointPullbackBound c ≤ max c 2 := by
  by_cases h : c ≤ 2
  · exact le_trans (endpointPullbackBound_le_two_of_le_two h) (le_max_right c 2)
  · have htwo : 2 ≤ c := by omega
    exact le_trans (endpointPullbackBound_le_self_of_two_le htwo) (le_max_left c 2)

/-- The invariant form needed for iterated endpoint-window pullbacks. -/
theorem endpointPullbackBound_iterate_max_le (c n : Nat) :
    max ((endpointPullbackBound^[n]) c) 2 ≤ max c 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact
        le_trans
          (max_le
            (endpointPullbackBound_le_max ((endpointPullbackBound^[n]) c))
            (le_max_right _ _))
          ih

/--
Lemma `lem:boundedendpointpullback`: iterating `β(c)=ceil(c/3)+1` never
requires a window larger than `max c 2`.
-/
theorem bounded_endpoint_pullback_radius (c n : Nat) :
    (endpointPullbackBound^[n]) c ≤ max c 2 := by
  exact le_trans (le_max_left _ 2) (endpointPullbackBound_iterate_max_le c n)

end DistributedSynthesis
