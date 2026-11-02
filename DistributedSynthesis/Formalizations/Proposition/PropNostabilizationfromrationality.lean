/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.Set.Basic

/-!
# Functionality and regularity do not imply stabilization
-/

namespace DistributedSynthesis

/-- Unary languages represented by their accepted lengths. -/
abbrev UnaryLanguage := Set Nat

/-- The abstract deletion transduction on word lengths. -/
def deleteFirstLength : Nat -> Nat
  | 0 => 0
  | n + 1 => n

/-- Inverse image of a unary language under the delete-first transduction. -/
def deleteFirstPreimage (language : UnaryLanguage) : UnaryLanguage :=
  { n | deleteFirstLength n ∈ language }

/-- The finite prefix language `{0, ..., k}`. -/
def unaryPrefixLanguage (k : Nat) : UnaryLanguage :=
  { n | n ≤ k }

@[simp]
theorem deleteFirstPreimage_unaryPrefixLanguage (k : Nat) :
    deleteFirstPreimage (unaryPrefixLanguage k) = unaryPrefixLanguage (k + 1) := by
  ext n
  cases n with
  | zero =>
      simp [deleteFirstPreimage, unaryPrefixLanguage, deleteFirstLength]
  | succ n =>
      simp [deleteFirstPreimage, unaryPrefixLanguage, deleteFirstLength]

theorem unaryPrefixLanguage_strict (k : Nat) :
    unaryPrefixLanguage k ⊂ unaryPrefixLanguage (k + 1) := by
  constructor
  · intro n hn
    exact Nat.le_trans hn (Nat.le_succ k)
  · intro hsubset
    have hin : k + 1 ∈ unaryPrefixLanguage (k + 1) := by
      simp [unaryPrefixLanguage]
    have hle : k + 1 ≤ k := hsubset hin
    omega

/--
Proposition `prop:nostabilizationfromrationality`: even a total functional
regular deletion transduction and a regular seed can generate an infinite
strict inverse-image chain.
-/
theorem functionality_and_regularity_do_not_imply_stabilization :
    ∀ k : Nat,
      deleteFirstPreimage (unaryPrefixLanguage k) = unaryPrefixLanguage (k + 1) ∧
        unaryPrefixLanguage k ⊂ unaryPrefixLanguage (k + 1) := by
  intro k
  exact ⟨deleteFirstPreimage_unaryPrefixLanguage k, unaryPrefixLanguage_strict k⟩

end DistributedSynthesis
