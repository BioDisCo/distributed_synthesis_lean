/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Tactic

/-! A quantitative finite-row lemma: a hole in every complete aligned block
of B edges bounds each consecutive surviving interval by fewer than 2B edges.
The application to the actual view-path enumeration is a separate obligation. -/

namespace Characterisation

def AlignedBlockHoles (live : Nat → Prop) (N B : Nat) : Prop :=
  ∀ q, (q + 1) * B ≤ N → ∃ j,
    q * B ≤ j ∧ j < (q + 1) * B ∧ ¬ live j

theorem live_interval_bound (live : Nat → Prop) (N B : Nat)
    (positive : 0 < B) (holes : AlignedBlockHoles live N B)
    (a b : Nat) (hab : a ≤ b) (hbN : b ≤ N)
    (allLive : ∀ j, a ≤ j → j < b → live j) :
    b - a < 2 * B := by
  by_contra hn
  have hlong : a + 2 * B ≤ b := by omega
  have lower : a / B * B ≤ a := Nat.div_mul_le_self a B
  have upper : a < (a / B + 1) * B := by
    have hmod := Nat.mod_lt a positive
    have heq := Nat.mod_add_div a B
    nlinarith
  have fits : (a / B + 1 + 1) * B ≤ N := by nlinarith
  obtain ⟨j, hjlo, hjhi, missing⟩ := holes (a / B + 1) fits
  apply missing
  apply allLive j
  · omega
  · nlinarith

end Characterisation
