/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefLTL
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! # Finite current-letter and consecutive-letter constraints in literal LTL -/

namespace DistributedSynthesis.FiniteLetterLTL

variable {Letter : Type*} [Fintype Letter]
noncomputable section
open Classical

def interp (a b : Letter) : Prop := b = a

def conjunction (xs : List (LTL Letter)) : LTL Letter := xs.foldr LTL.conj .verum
def disjunction (xs : List (LTL Letter)) : LTL Letter := xs.foldr LTL.disj .falsum

omit [Fintype Letter] in
theorem satisfies_conjunction (w : OmegaWord Letter) (xs : List (LTL Letter)) :
    LTL.Satisfies interp w (conjunction xs) ↔ ∀ φ ∈ xs, LTL.Satisfies interp w φ := by
  induction xs with
  | nil => simp [conjunction,LTL.Satisfies]
  | cons φ xs ih => simp [conjunction,LTL.Satisfies,← ih]

omit [Fintype Letter] in
theorem satisfies_disjunction (w : OmegaWord Letter) (xs : List (LTL Letter)) :
    LTL.Satisfies interp w (disjunction xs) ↔ ∃ φ ∈ xs, LTL.Satisfies interp w φ := by
  induction xs with
  | nil => simp [disjunction,LTL.Satisfies]
  | cons φ xs ih => simp [disjunction,LTL.Satisfies,← ih]

def test (P : Letter → Prop) : LTL Letter :=
  disjunction (((Finset.univ.filter P).toList).map LTL.atom)

theorem satisfies_test (w : OmegaWord Letter) (P : Letter → Prop) :
    LTL.Satisfies interp w (test P) ↔ P (w 0) := by
  simp [test,satisfies_disjunction,LTL.Satisfies,interp]

def relation (R : Letter → Letter → Prop) : LTL Letter :=
  conjunction (Finset.univ.toList.map fun a ↦
    LTL.disj (.neg (.atom a)) (.next (test (R a))))

theorem satisfies_relation (w : OmegaWord Letter) (R : Letter → Letter → Prop) :
    LTL.Satisfies interp w (relation R) ↔ R (w 0) (w 1) := by
  simp [relation,satisfies_conjunction,LTL.Satisfies,satisfies_test,
    interp,OmegaWord.drop,or_iff_not_imp_left]

/-- Zero carry is required until the first letter leaving a boundary,
including the case in which the boundary is never left. -/
def boundary (stays zero : Letter → Prop) : LTL Letter :=
  .release (test (fun a ↦ ¬ stays a)) (test (fun a ↦ ¬ stays a ∨ zero a))

theorem satisfies_boundary (w : OmegaWord Letter) (stays zero : Letter → Prop) :
    LTL.Satisfies interp w (boundary stays zero) ↔
      ∀ n, (∀ k, k ≤ n → stays (w k)) → zero (w n) := by
  simp only [boundary,LTL.Satisfies,satisfies_test,OmegaWord.drop_apply,Nat.add_zero]
  constructor
  · intro h n hn
    rcases h n with (hleave | hz) | ⟨k,hk,hleave⟩
    · exact False.elim (hleave (hn n le_rfl))
    · exact hz
    · exact False.elim (hleave (hn k (Nat.le_of_lt hk)))
  · intro h n
    by_cases hn : ∀ k, k ≤ n → stays (w k)
    · exact Or.inl (Or.inr (h n hn))
    · push Not at hn
      obtain ⟨k,hk,hleave⟩ := hn
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact Or.inr ⟨k,hk,hleave⟩
      · exact Or.inl (Or.inl hleave)

end
end DistributedSynthesis.FiniteLetterLTL
