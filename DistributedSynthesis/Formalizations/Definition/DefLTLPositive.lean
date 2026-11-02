/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import DistributedSynthesis.Formalizations.Definition.DefLTL

/-!
# Positive-normal-form LTL

This module provides an LTL syntax with negation only at atoms and proves that
ordinary LTL formulas translate into it without changing their semantics.
-/

namespace DistributedSynthesis

universe u v

/-- Atomic literals.  `positive = true` means the atom itself; `false` means negated. -/
structure LTLLiteral (AP : Type u) where
  positive : Bool
  atom : AP
deriving Repr, DecidableEq

/-- LTL in positive normal form: negation appears only in literals. -/
inductive PositiveLTL (AP : Type u) : Type u where
  | verum : PositiveLTL AP
  | falsum : PositiveLTL AP
  | lit : LTLLiteral AP -> PositiveLTL AP
  | conj : PositiveLTL AP -> PositiveLTL AP -> PositiveLTL AP
  | disj : PositiveLTL AP -> PositiveLTL AP -> PositiveLTL AP
  | next : PositiveLTL AP -> PositiveLTL AP
  | until : PositiveLTL AP -> PositiveLTL AP -> PositiveLTL AP
  | release : PositiveLTL AP -> PositiveLTL AP -> PositiveLTL AP
deriving Repr, DecidableEq

namespace PositiveLTL

/-- Number of constructors in a positive-normal-form LTL formula. -/
def size {AP : Type u} : PositiveLTL AP -> Nat
  | verum => 1
  | falsum => 1
  | lit _ => 1
  | conj φ ψ => φ.size + ψ.size + 1
  | disj φ ψ => φ.size + ψ.size + 1
  | next φ => φ.size + 1
  | PositiveLTL.until φ ψ => φ.size + ψ.size + 1
  | PositiveLTL.release φ ψ => φ.size + ψ.size + 1

@[simp]
theorem size_pos {AP : Type u} (φ : PositiveLTL AP) :
    0 < φ.size := by
  induction φ <;> simp [size]

theorem size_lt_conj_left {AP : Type u} (φ ψ : PositiveLTL AP) :
    φ.size < (PositiveLTL.conj φ ψ).size := by
  simp [size]

theorem size_lt_conj_right {AP : Type u} (φ ψ : PositiveLTL AP) :
    ψ.size < (PositiveLTL.conj φ ψ).size := by
  simp [size]

theorem size_lt_disj_left {AP : Type u} (φ ψ : PositiveLTL AP) :
    φ.size < (PositiveLTL.disj φ ψ).size := by
  simp [size]

theorem size_lt_disj_right {AP : Type u} (φ ψ : PositiveLTL AP) :
    ψ.size < (PositiveLTL.disj φ ψ).size := by
  simp [size]

theorem size_lt_next {AP : Type u} (φ : PositiveLTL AP) :
    φ.size < (PositiveLTL.next φ).size := by
  simp [size]

theorem size_lt_until_left {AP : Type u} (φ ψ : PositiveLTL AP) :
    φ.size < (PositiveLTL.until φ ψ).size := by
  simp [size]

theorem size_lt_until_right {AP : Type u} (φ ψ : PositiveLTL AP) :
    ψ.size < (PositiveLTL.until φ ψ).size := by
  simp [size]

theorem size_lt_release_left {AP : Type u} (φ ψ : PositiveLTL AP) :
    φ.size < (PositiveLTL.release φ ψ).size := by
  simp [size]

theorem size_lt_release_right {AP : Type u} (φ ψ : PositiveLTL AP) :
    ψ.size < (PositiveLTL.release φ ψ).size := by
  simp [size]

/-- Immediate and nested subformulas, including the formula itself. -/
def subformulas {AP : Type u} : PositiveLTL AP -> List (PositiveLTL AP)
  | verum => [verum]
  | falsum => [falsum]
  | lit literal => [lit literal]
  | conj φ ψ => conj φ ψ :: (φ.subformulas ++ ψ.subformulas)
  | disj φ ψ => disj φ ψ :: (φ.subformulas ++ ψ.subformulas)
  | next φ => next φ :: φ.subformulas
  | PositiveLTL.until φ ψ => PositiveLTL.until φ ψ :: (φ.subformulas ++ ψ.subformulas)
  | PositiveLTL.release φ ψ => PositiveLTL.release φ ψ :: (φ.subformulas ++ ψ.subformulas)

@[simp]
theorem mem_subformulas_self {AP : Type u} (φ : PositiveLTL AP) :
    φ ∈ φ.subformulas := by
  cases φ <;> simp [subformulas]

/-- Every listed subformula is no larger than the formula that contains it. -/
theorem size_le_of_mem_subformulas {AP : Type u} {χ φ : PositiveLTL AP}
    (hχφ : χ ∈ φ.subformulas) :
    χ.size ≤ φ.size := by
  induction φ with
  | verum =>
      simp [subformulas] at hχφ
      simp [hχφ]
  | falsum =>
      simp [subformulas] at hχφ
      simp [hχφ]
  | lit literal =>
      simp [subformulas] at hχφ
      simp [hχφ]
  | conj φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hχφ
      rcases hχφ with hroot | hleft | hright
      · subst χ
        simp
      · have hle := ih₁ hleft
        simp [size]
        omega
      · have hle := ih₂ hright
        simp [size]
        omega
  | disj φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hχφ
      rcases hχφ with hroot | hleft | hright
      · subst χ
        simp
      · have hle := ih₁ hleft
        simp [size]
        omega
      · have hle := ih₂ hright
        simp [size]
        omega
  | next φ ih =>
      simp [subformulas] at hχφ
      rcases hχφ with hroot | hsub
      · subst χ
        simp
      · have hle := ih hsub
        simp [size]
        omega
  | «until» φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hχφ
      rcases hχφ with hroot | hleft | hright
      · subst χ
        simp
      · have hle := ih₁ hleft
        simp [size]
        omega
      · have hle := ih₂ hright
        simp [size]
        omega
  | «release» φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hχφ
      rcases hχφ with hroot | hleft | hright
      · subst χ
        simp
      · have hle := ih₁ hleft
        simp [size]
        omega
      · have hle := ih₂ hright
        simp [size]
        omega

/-- Subformula membership is transitive. -/
theorem subformulas_trans {AP : Type u} {χ ψ φ : PositiveLTL AP}
    (hχψ : χ ∈ ψ.subformulas)
    (hψφ : ψ ∈ φ.subformulas) :
    χ ∈ φ.subformulas := by
  induction φ with
  | verum =>
      simp [subformulas] at hψφ
      simpa [hψφ] using hχψ
  | falsum =>
      simp [subformulas] at hψφ
      simpa [hψφ] using hχψ
  | lit literal =>
      simp [subformulas] at hψφ
      simpa [hψφ] using hχψ
  | conj φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hψφ ⊢
      rcases hψφ with hroot | hleft | hright
      · subst ψ
        simpa [subformulas] using hχψ
      · exact Or.inr (Or.inl (ih₁ hleft))
      · exact Or.inr (Or.inr (ih₂ hright))
  | disj φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hψφ ⊢
      rcases hψφ with hroot | hleft | hright
      · subst ψ
        simpa [subformulas] using hχψ
      · exact Or.inr (Or.inl (ih₁ hleft))
      · exact Or.inr (Or.inr (ih₂ hright))
  | next φ ih =>
      simp [subformulas] at hψφ ⊢
      rcases hψφ with hroot | hsub
      · subst ψ
        simpa [subformulas] using hχψ
      · exact Or.inr (ih hsub)
  | «until» φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hψφ ⊢
      rcases hψφ with hroot | hleft | hright
      · subst ψ
        simpa [subformulas] using hχψ
      · exact Or.inr (Or.inl (ih₁ hleft))
      · exact Or.inr (Or.inr (ih₂ hright))
  | «release» φ₁ φ₂ ih₁ ih₂ =>
      simp [subformulas] at hψφ ⊢
      rcases hψφ with hroot | hleft | hright
      · subst ψ
        simpa [subformulas] using hχψ
      · exact Or.inr (Or.inl (ih₁ hleft))
      · exact Or.inr (Or.inr (ih₂ hright))

/-- The finite carrier of subformulas of a positive LTL formula. -/
abbrev Subformula {AP : Type u} (φ : PositiveLTL AP) :=
  { ψ : PositiveLTL AP // ψ ∈ φ.subformulas }

noncomputable instance subformulaFintype {AP : Type u}
    [DecidableEq AP]
    (φ : PositiveLTL AP) :
    Fintype φ.Subformula :=
  Fintype.subtype (φ.subformulas.toFinset) (by
    intro ψ
    exact List.mem_toFinset)

/-- The formula itself as an element of its finite subformula carrier. -/
def rootSubformula {AP : Type u} (φ : PositiveLTL AP) : φ.Subformula :=
  ⟨φ, mem_subformulas_self φ⟩

/-- Satisfaction for positive-normal-form LTL. -/
def Satisfies {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter) :
    PositiveLTL AP -> Prop
  | verum => True
  | falsum => False
  | lit literal =>
      if literal.positive then
        interp literal.atom (word 0)
      else
        ¬ interp literal.atom (word 0)
  | conj φ ψ => Satisfies interp word φ ∧ Satisfies interp word ψ
  | disj φ ψ => Satisfies interp word φ ∨ Satisfies interp word ψ
  | next φ => Satisfies interp (OmegaWord.drop word 1) φ
  | PositiveLTL.until φ ψ =>
      ∃ n : Nat,
        Satisfies interp (OmegaWord.drop word n) ψ ∧
          ∀ k : Nat, k < n -> Satisfies interp (OmegaWord.drop word k) φ
  | PositiveLTL.release φ ψ =>
      ∀ n : Nat,
        Satisfies interp (OmegaWord.drop word n) ψ ∨
          ∃ k : Nat, k < n ∧ Satisfies interp (OmegaWord.drop word k) φ

/-- Flip every literal and dualize the Boolean/temporal connectives. -/
def negate {AP : Type u} : PositiveLTL AP -> PositiveLTL AP
  | verum => falsum
  | falsum => verum
  | lit literal => lit { literal with positive := !literal.positive }
  | conj φ ψ => disj φ.negate ψ.negate
  | disj φ ψ => conj φ.negate ψ.negate
  | next φ => next φ.negate
  | PositiveLTL.until φ ψ => PositiveLTL.release φ.negate ψ.negate
  | PositiveLTL.release φ ψ => PositiveLTL.until φ.negate ψ.negate

private theorem not_until_iff_release_not {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hφ : ∀ word : OmegaWord Letter,
      Satisfies interp word φ.negate ↔ ¬ Satisfies interp word φ)
    (hψ : ∀ word : OmegaWord Letter,
      Satisfies interp word ψ.negate ↔ ¬ Satisfies interp word ψ) :
    (∀ n : Nat,
        Satisfies interp (OmegaWord.drop word n) ψ.negate ∨
          ∃ k : Nat,
            k < n ∧ Satisfies interp (OmegaWord.drop word k) φ.negate) ↔
      ¬ (∃ n : Nat,
        Satisfies interp (OmegaWord.drop word n) ψ ∧
          ∀ k : Nat, k < n -> Satisfies interp (OmegaWord.drop word k) φ) := by
  classical
  constructor
  · intro h hUntil
    rcases hUntil with ⟨n, hψn, hbefore⟩
    rcases h n with hnotψ | hnotφ
    · exact (hψ (OmegaWord.drop word n)).mp hnotψ hψn
    · rcases hnotφ with ⟨k, hk, hnegφ⟩
      exact (hφ (OmegaWord.drop word k)).mp hnegφ (hbefore k hk)
  · intro h n
    by_cases hψn : Satisfies interp (OmegaWord.drop word n) ψ
    · right
      by_contra hno
      apply h
      refine ⟨n, hψn, ?_⟩
      intro k hk
      by_contra hbad
      exact hno ⟨k, hk, (hφ (OmegaWord.drop word k)).mpr hbad⟩
    · left
      exact (hψ (OmegaWord.drop word n)).mpr hψn

/-- Semantics of syntactic negation in positive normal form. -/
theorem satisfies_negate {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ : PositiveLTL AP) :
    Satisfies interp word φ.negate ↔ ¬ Satisfies interp word φ := by
  classical
  induction φ generalizing word with
  | verum => simp [negate, Satisfies]
  | falsum => simp [negate, Satisfies]
  | lit literal =>
      rcases literal with ⟨positive, atom⟩
      cases positive <;> simp [negate, Satisfies]
  | conj φ ψ ihφ ihψ =>
      simp [negate, Satisfies, ihφ, ihψ]
      tauto
  | disj φ ψ ihφ ihψ =>
      simp [negate, Satisfies, ihφ, ihψ]
  | next φ ih =>
      simp [negate, Satisfies, ih]
  | «until» φ ψ ihφ ihψ =>
      exact not_until_iff_release_not interp word φ ψ ihφ ihψ
  | «release» φ ψ ihφ ihψ =>
      constructor
      · intro h hrel
        rcases h with ⟨n, hnotψ, hbefore⟩
        rcases hrel n with hψn | hφbefore
        · exact (ihψ (OmegaWord.drop word n)).mp hnotψ hψn
        · rcases hφbefore with ⟨k, hk, hφk⟩
          exact (ihφ (OmegaWord.drop word k)).mp (hbefore k hk) hφk
      · intro h
        by_contra hno
        apply h
        intro n
        by_cases hψn : Satisfies interp (OmegaWord.drop word n) ψ
        · exact Or.inl hψn
        · right
          by_contra hnone
          exact hno ⟨n, (ihψ (OmegaWord.drop word n)).mpr hψn, fun k hk =>
            by
              by_contra hnotneg
              apply hnone
              refine ⟨k, hk, ?_⟩
              by_contra hnotφ
              exact hnotneg ((ihφ (OmegaWord.drop word k)).mpr hnotφ)⟩

/-- Translate an arbitrary LTL formula to positive normal form. -/
def ofLTL {AP : Type u} : LTL AP -> PositiveLTL AP
  | LTL.verum => verum
  | LTL.falsum => falsum
  | LTL.atom ap => lit ⟨true, ap⟩
  | LTL.neg φ => (ofLTL φ).negate
  | LTL.conj φ ψ => conj (ofLTL φ) (ofLTL ψ)
  | LTL.disj φ ψ => disj (ofLTL φ) (ofLTL ψ)
  | LTL.next φ => next (ofLTL φ)
  | LTL.until φ ψ => PositiveLTL.until (ofLTL φ) (ofLTL ψ)
  | LTL.release φ ψ => PositiveLTL.release (ofLTL φ) (ofLTL ψ)

/-- Positive-normal-form translation preserves LTL semantics. -/
theorem satisfies_ofLTL {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ : LTL AP) :
    Satisfies interp word (ofLTL φ) ↔ LTL.Satisfies interp word φ := by
  induction φ generalizing word with
  | verum => simp [ofLTL, Satisfies, LTL.Satisfies]
  | falsum => simp [ofLTL, Satisfies, LTL.Satisfies]
  | atom ap => simp [ofLTL, Satisfies, LTL.Satisfies]
  | neg φ ih =>
      simp [ofLTL, LTL.Satisfies, satisfies_negate, ih]
  | conj φ ψ ihφ ihψ =>
      simp [ofLTL, Satisfies, LTL.Satisfies, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp [ofLTL, Satisfies, LTL.Satisfies, ihφ, ihψ]
  | next φ ih =>
      simp [ofLTL, Satisfies, LTL.Satisfies, ih]
  | «until» φ ψ ihφ ihψ =>
      simp [ofLTL, Satisfies, LTL.Satisfies, ihφ, ihψ]
  | «release» φ ψ ihφ ihψ =>
      simp [ofLTL, Satisfies, LTL.Satisfies, ihφ, ihψ]

end PositiveLTL

end DistributedSynthesis
