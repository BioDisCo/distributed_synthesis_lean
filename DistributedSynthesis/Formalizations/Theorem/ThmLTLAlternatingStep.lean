/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefPositiveBoolean
import DistributedSynthesis.Formalizations.Theorem.ThmLTLTableau

/-!
# One-step alternating transition for positive LTL

This is the local transition map used by the standard alternating automaton
for an LTL formula.  The theorem in this file proves its one-step semantic
correctness.
-/

namespace DistributedSynthesis

universe u v

namespace PositiveLTL

/-- Literal satisfaction at the current letter. -/
def literalHolds {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (letter : Letter)
    (literal : LTLLiteral AP) :
    Prop :=
  if literal.positive then
    interp literal.atom letter
  else
    ¬ interp literal.atom letter

noncomputable instance literalHoldsDecidable {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter)
    (literal : LTLLiteral AP) :
    Decidable (literalHolds interp letter literal) := by
  rcases literal with ⟨positive, atom⟩
  cases positive
  · exact inferInstanceAs (Decidable (¬ interp atom letter))
  · exact inferInstanceAs (Decidable (interp atom letter))

/--
The one-step alternating transition formula for a positive LTL formula.

Atoms in the returned positive Boolean formula are successor-state formulas
that must be checked at the next input position.
-/
noncomputable def alternatingStep {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter) :
    PositiveLTL AP -> PosBool (PositiveLTL AP)
  | verum => PosBool.verum
  | falsum => PosBool.falsum
  | lit literal =>
      if literalHolds interp letter literal then
        PosBool.verum
      else
        PosBool.falsum
  | conj φ ψ =>
      PosBool.conj (alternatingStep interp letter φ) (alternatingStep interp letter ψ)
  | disj φ ψ =>
      PosBool.disj (alternatingStep interp letter φ) (alternatingStep interp letter ψ)
  | next φ => PosBool.atom φ
  | PositiveLTL.until φ ψ =>
      PosBool.disj
        (alternatingStep interp letter ψ)
        (PosBool.conj
          (alternatingStep interp letter φ)
          (PosBool.atom (PositiveLTL.until φ ψ)))
  | PositiveLTL.release φ ψ =>
      PosBool.conj
        (alternatingStep interp letter ψ)
        (PosBool.disj
          (alternatingStep interp letter φ)
          (PosBool.atom (PositiveLTL.release φ ψ)))

/--
The alternating transition is correct for one step: when successor-state atoms
are interpreted as satisfaction at the next input position, the transition
formula is true exactly when the original LTL formula is true now.
-/
theorem alternatingStep_correct {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (word : OmegaWord Letter)
    (φ : PositiveLTL AP) :
    PosBool.Eval
        (fun ψ => Satisfies interp (OmegaWord.drop word 1) ψ)
        (alternatingStep interp (word 0) φ) ↔
      Satisfies interp word φ := by
  induction φ generalizing word with
  | verum => simp [alternatingStep, Satisfies, PosBool.Eval]
  | falsum => simp [alternatingStep, Satisfies, PosBool.Eval]
  | lit literal =>
      rcases literal with ⟨positive, atom⟩
      cases positive
      · by_cases h : interp atom (word 0)
        · simp [alternatingStep, literalHolds, Satisfies, PosBool.Eval, h]
        · simp [alternatingStep, literalHolds, Satisfies, PosBool.Eval, h]
      · by_cases h : interp atom (word 0)
        · simp [alternatingStep, literalHolds, Satisfies, PosBool.Eval, h]
        · simp [alternatingStep, literalHolds, Satisfies, PosBool.Eval, h]
  | conj φ ψ ihφ ihψ =>
      simp [alternatingStep, Satisfies, PosBool.Eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp [alternatingStep, Satisfies, PosBool.Eval, ihφ, ihψ]
  | next φ =>
      simp [alternatingStep, Satisfies, PosBool.Eval]
  | «until» φ ψ ihφ ihψ =>
      rw [satisfies_until_unfold]
      simp [alternatingStep, PosBool.Eval, ihφ, ihψ]
  | «release» φ ψ ihφ ihψ =>
      rw [satisfies_release_unfold]
      simp [alternatingStep, PosBool.Eval, ihφ, ihψ]

/--
Fixed-point progress extraction for an `until` transition.

If the one-step tableau for `φ U ψ` is true but the `ψ` branch is not, then
the transition must have taken the continuation branch: `φ` is true at the
current step and the `φ U ψ` self-loop is selected for the suffix.
-/
theorem alternatingStep_until_progress_of_not_right
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter)
    (φ ψ : PositiveLTL AP)
    (valuation : PositiveLTL AP -> Prop)
    (hstep :
      PosBool.Eval valuation
        (alternatingStep interp letter (PositiveLTL.until φ ψ)))
    (hnotRight :
      ¬ PosBool.Eval valuation (alternatingStep interp letter ψ)) :
    PosBool.Eval valuation (alternatingStep interp letter φ) ∧
      valuation (PositiveLTL.until φ ψ) := by
  change
    PosBool.Eval valuation (alternatingStep interp letter ψ) ∨
      (PosBool.Eval valuation (alternatingStep interp letter φ) ∧
        valuation (PositiveLTL.until φ ψ)) at hstep
  rcases hstep with hψ | hcontinue
  · exact False.elim (hnotRight hψ)
  · exact hcontinue

/--
Fixed-point progress extraction for a `release` transition.

If the one-step tableau for `φ R ψ` is true, then the `ψ` branch is true now
and either the left branch `φ` is true now or the release obligation continues
as a self-loop on the suffix.
-/
theorem alternatingStep_release_progress
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter)
    (φ ψ : PositiveLTL AP)
    (valuation : PositiveLTL AP -> Prop)
    (hstep :
      PosBool.Eval valuation
        (alternatingStep interp letter (PositiveLTL.release φ ψ))) :
    PosBool.Eval valuation (alternatingStep interp letter ψ) ∧
      (PosBool.Eval valuation (alternatingStep interp letter φ) ∨
        valuation (PositiveLTL.release φ ψ)) := by
  change
    PosBool.Eval valuation (alternatingStep interp letter ψ) ∧
      (PosBool.Eval valuation (alternatingStep interp letter φ) ∨
        valuation (PositiveLTL.release φ ψ)) at hstep
  exact hstep

/--
Every successor formula mentioned by the one-step transition is a subformula
of the source formula.  This is the closure fact that makes the standard LTL
alternating automaton finite.
-/
theorem alternatingStep_atoms_subformulas {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter)
    (φ ψ : PositiveLTL AP)
    (h : ψ ∈ (alternatingStep interp letter φ).atoms) :
    ψ ∈ φ.subformulas := by
  induction φ with
  | verum =>
      simp [alternatingStep, PosBool.atoms] at h
  | falsum =>
      simp [alternatingStep, PosBool.atoms] at h
  | lit literal =>
      by_cases hlit : literalHolds interp letter literal
      · simp [alternatingStep, PosBool.atoms, hlit] at h
      · simp [alternatingStep, PosBool.atoms, hlit] at h
  | conj φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms, subformulas] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl (ih₁ h))
      · exact Or.inr (Or.inr (ih₂ h))
  | disj φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms, subformulas] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl (ih₁ h))
      · exact Or.inr (Or.inr (ih₂ h))
  | next φ =>
      simp [alternatingStep, PosBool.atoms, subformulas] at h ⊢
      subst ψ
      exact Or.inr (mem_subformulas_self φ)
  | «until» φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms, subformulas] at h ⊢
      rcases h with hψ | hφ | hself
      · exact Or.inr (Or.inr (ih₂ hψ))
      · exact Or.inr (Or.inl (ih₁ hφ))
      · exact Or.inl hself
  | «release» φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms, subformulas] at h ⊢
      rcases h with hψ | hφ | hself
      · exact Or.inr (Or.inr (ih₂ hψ))
      · exact Or.inr (Or.inl (ih₁ hφ))
      · exact Or.inl hself

/--
Every successor atom of the one-step LTL tableau is either the current formula
itself (the temporal self-loop case) or a strict proper subformula.
-/
theorem alternatingStep_atoms_self_or_size_lt {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter)
    (φ ψ : PositiveLTL AP)
    (h : ψ ∈ (alternatingStep interp letter φ).atoms) :
    ψ = φ ∨ ψ.size < φ.size := by
  induction φ with
  | verum =>
      simp [alternatingStep, PosBool.atoms] at h
  | falsum =>
      simp [alternatingStep, PosBool.atoms] at h
  | lit literal =>
      by_cases hlit : literalHolds interp letter literal
      · simp [alternatingStep, PosBool.atoms, hlit] at h
      · simp [alternatingStep, PosBool.atoms, hlit] at h
  | conj φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms] at h
      rcases h with h | h
      · rcases ih₁ h with hself | hlt
        · subst ψ
          right
          exact size_lt_conj_left φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_conj_left φ₁ φ₂)
      · rcases ih₂ h with hself | hlt
        · subst ψ
          right
          exact size_lt_conj_right φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_conj_right φ₁ φ₂)
  | disj φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms] at h
      rcases h with h | h
      · rcases ih₁ h with hself | hlt
        · subst ψ
          right
          exact size_lt_disj_left φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_disj_left φ₁ φ₂)
      · rcases ih₂ h with hself | hlt
        · subst ψ
          right
          exact size_lt_disj_right φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_disj_right φ₁ φ₂)
  | next φ =>
      simp [alternatingStep, PosBool.atoms] at h
      subst ψ
      right
      exact size_lt_next φ
  | «until» φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms] at h
      rcases h with hψ | hφ | hself
      · rcases ih₂ hψ with hself₂ | hlt
        · subst ψ
          right
          exact size_lt_until_right φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_until_right φ₁ φ₂)
      · rcases ih₁ hφ with hself₁ | hlt
        · subst ψ
          right
          exact size_lt_until_left φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_until_left φ₁ φ₂)
      · left
        exact hself
  | «release» φ₁ φ₂ ih₁ ih₂ =>
      simp [alternatingStep, PosBool.atoms] at h
      rcases h with hψ | hφ | hself
      · rcases ih₂ hψ with hself₂ | hlt
        · subst ψ
          right
          exact size_lt_release_right φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_release_right φ₁ φ₂)
      · rcases ih₁ hφ with hself₁ | hlt
        · subst ψ
          right
          exact size_lt_release_left φ₁ φ₂
        · right
          exact Nat.lt_trans hlt (size_lt_release_left φ₁ φ₂)
      · left
        exact hself

/--
The only one-step tableau atoms that can be the source formula itself are the
temporal fixed-point states, `until` and `release`.
-/
theorem alternatingStep_self_atom_is_until_or_release
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (letter : Letter)
    (φ : PositiveLTL AP)
    (hself : φ ∈ (alternatingStep interp letter φ).atoms) :
    (∃ φ₁ φ₂ : PositiveLTL AP, φ = PositiveLTL.until φ₁ φ₂) ∨
      ∃ φ₁ φ₂ : PositiveLTL AP, φ = PositiveLTL.release φ₁ φ₂ := by
  induction φ with
  | verum =>
      simp [alternatingStep, PosBool.atoms] at hself
  | falsum =>
      simp [alternatingStep, PosBool.atoms] at hself
  | lit literal =>
      by_cases hlit : literalHolds interp letter literal
      · simp [alternatingStep, PosBool.atoms, hlit] at hself
      · simp [alternatingStep, PosBool.atoms, hlit] at hself
  | conj φ ψ ihφ ihψ =>
      simp [alternatingStep, PosBool.atoms] at hself
      rcases hself with hself | hself
      · have hmove := alternatingStep_atoms_self_or_size_lt interp letter φ (PositiveLTL.conj φ ψ) hself
        rcases hmove with hbad | hlt
        · have hsize : (PositiveLTL.conj φ ψ).size = φ.size := by rw [hbad]
          have hφlt := size_lt_conj_left φ ψ
          omega
        · have hφlt := size_lt_conj_left φ ψ
          omega
      · have hmove := alternatingStep_atoms_self_or_size_lt interp letter ψ (PositiveLTL.conj φ ψ) hself
        rcases hmove with hbad | hlt
        · have hsize : (PositiveLTL.conj φ ψ).size = ψ.size := by rw [hbad]
          have hψlt := size_lt_conj_right φ ψ
          omega
        · have hψlt := size_lt_conj_right φ ψ
          omega
  | disj φ ψ ihφ ihψ =>
      simp [alternatingStep, PosBool.atoms] at hself
      rcases hself with hself | hself
      · have hmove := alternatingStep_atoms_self_or_size_lt interp letter φ (PositiveLTL.disj φ ψ) hself
        rcases hmove with hbad | hlt
        · have hsize : (PositiveLTL.disj φ ψ).size = φ.size := by rw [hbad]
          have hφlt := size_lt_disj_left φ ψ
          omega
        · have hφlt := size_lt_disj_left φ ψ
          omega
      · have hmove := alternatingStep_atoms_self_or_size_lt interp letter ψ (PositiveLTL.disj φ ψ) hself
        rcases hmove with hbad | hlt
        · have hsize : (PositiveLTL.disj φ ψ).size = ψ.size := by rw [hbad]
          have hψlt := size_lt_disj_right φ ψ
          omega
        · have hψlt := size_lt_disj_right φ ψ
          omega
  | next φ =>
      simp [alternatingStep, PosBool.atoms] at hself
      have hsize : (PositiveLTL.next φ).size = φ.size := by
        rw [hself]
      have hlt := size_lt_next φ
      omega
  | «until» φ ψ =>
      exact Or.inl ⟨φ, ψ, rfl⟩
  | «release» φ ψ =>
      exact Or.inr ⟨φ, ψ, rfl⟩

end PositiveLTL

end DistributedSynthesis
