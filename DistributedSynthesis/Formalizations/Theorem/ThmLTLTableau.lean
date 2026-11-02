/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefLTLPositive

/-!
# Tableau/unfolding laws for LTL

These are the semantic equations used by the standard LTL-to-alternating-
automaton construction.  They are stated for positive-normal-form LTL.
-/

namespace DistributedSynthesis

universe u v

namespace PositiveLTL

/-- Until unfolds into current satisfaction or current left side plus next until. -/
theorem satisfies_until_unfold {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP) :
    Satisfies interp word (PositiveLTL.until φ ψ) ↔
      Satisfies interp word ψ ∨
        (Satisfies interp word φ ∧
          Satisfies interp (OmegaWord.drop word 1) (PositiveLTL.until φ ψ)) := by
  constructor
  · intro h
    rcases h with ⟨n, hψn, hbefore⟩
    cases n with
    | zero =>
        left
        simpa using hψn
    | succ n =>
        right
        constructor
        · simpa using hbefore 0 (Nat.zero_lt_succ n)
        · refine ⟨n, ?_, ?_⟩
          · simpa [OmegaWord.drop_drop, Nat.add_comm] using hψn
          · intro k hk
            simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using
              hbefore (k + 1) (Nat.succ_lt_succ hk)
  · intro h
    rcases h with hψ | hstep
    · exact ⟨0, by simpa using hψ, by intro k hk; cases hk⟩
    · rcases hstep with ⟨hφ, hnext⟩
      rcases hnext with ⟨n, hψn, hbefore⟩
      refine ⟨n + 1, ?_, ?_⟩
      · simpa [OmegaWord.drop_drop, Nat.add_comm] using hψn
      · intro k hk
        cases k with
        | zero => simpa using hφ
        | succ k =>
            have hk' : k < n := Nat.succ_lt_succ_iff.mp hk
            simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hbefore k hk'

/--
Least-fixed-point induction for `until`.

To prove an invariant `P` from `φ U ψ`, it is enough to show that `P` holds at
the exit condition `ψ`, and that it is preserved by one unfolding step through
`φ`.
-/
theorem satisfies_until_induction
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (P : OmegaWord Letter -> Prop)
    (hψ : ∀ word, Satisfies interp word ψ -> P word)
    (hstep :
      ∀ word,
        Satisfies interp word φ ->
        P (OmegaWord.drop word 1) ->
        P word) :
    ∀ word,
      Satisfies interp word (PositiveLTL.until φ ψ) ->
        P word := by
  intro word hsat
  rcases hsat with ⟨n, hψn, hbefore⟩
  induction n generalizing word with
  | zero =>
      exact hψ word (by simpa using hψn)
  | succ n ih =>
      apply hstep
      · simpa using hbefore 0 (Nat.zero_lt_succ n)
      · apply ih
        · simpa [OmegaWord.drop_drop, Nat.add_comm] using hψn
        · intro k hk
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using
            hbefore (k + 1) (Nat.succ_lt_succ hk)

/-- The one-step semantic operator whose least fixed point is `φ U ψ`. -/
def untilStepSet
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (X : Set (OmegaWord Letter)) : Set (OmegaWord Letter) :=
  {word |
    Satisfies interp word ψ ∨
      (Satisfies interp word φ ∧ OmegaWord.drop word 1 ∈ X)}

theorem untilStepSet_mono
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    {X Y : Set (OmegaWord Letter)}
    (hXY : X ⊆ Y) :
    untilStepSet interp φ ψ X ⊆ untilStepSet interp φ ψ Y := by
  intro word hword
  rcases hword with hψ | ⟨hφ, hnext⟩
  · exact Or.inl hψ
  · exact Or.inr ⟨hφ, hXY hnext⟩

/-- `φ U ψ` is a fixed point of the until one-step operator. -/
theorem satisfies_until_fixedPoint
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP) :
    {word | Satisfies interp word (PositiveLTL.until φ ψ)} =
      untilStepSet interp φ ψ
        {word | Satisfies interp word (PositiveLTL.until φ ψ)} := by
  ext word
  exact satisfies_until_unfold interp word φ ψ

/-- `φ U ψ` is below every pre-fixed point of the until operator. -/
theorem satisfies_until_least_prefixed
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (X : Set (OmegaWord Letter))
    (hpre : untilStepSet interp φ ψ X ⊆ X) :
    {word | Satisfies interp word (PositiveLTL.until φ ψ)} ⊆ X := by
  intro word hsat
  exact satisfies_until_induction interp φ ψ (fun word => word ∈ X)
    (fun word hψ => hpre (Or.inl hψ))
    (fun word hφ hnext => hpre (Or.inr ⟨hφ, hnext⟩))
    word hsat

/-- `φ U ψ` is the least fixed point of the until one-step operator. -/
theorem satisfies_until_least_fixedPoint
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (X : Set (OmegaWord Letter))
    (hfix : untilStepSet interp φ ψ X = X) :
    {word | Satisfies interp word (PositiveLTL.until φ ψ)} ⊆ X := by
  apply satisfies_until_least_prefixed interp φ ψ X
  intro word hword
  simpa [hfix] using hword

/-- Release unfolds dually into current right side and either current left side or next release. -/
theorem satisfies_release_unfold {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP) :
    Satisfies interp word (PositiveLTL.release φ ψ) ↔
      Satisfies interp word ψ ∧
        (Satisfies interp word φ ∨
          Satisfies interp (OmegaWord.drop word 1) (PositiveLTL.release φ ψ)) := by
  constructor
  · intro h
    constructor
    · rcases h 0 with hψ | hbad
      · simpa using hψ
      · rcases hbad with ⟨k, hk, _⟩
        cases hk
    · by_cases hφ : Satisfies interp word φ
      · exact Or.inl hφ
      · right
        intro n
        rcases h (n + 1) with hψ | hbefore
        · left
          simpa [OmegaWord.drop_drop, Nat.add_comm] using hψ
        · rcases hbefore with ⟨k, hk, hφk⟩
          cases k with
          | zero =>
              exact False.elim (hφ (by simpa using hφk))
          | succ k =>
              right
              refine ⟨k, Nat.succ_lt_succ_iff.mp hk, ?_⟩
              simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hφk
  · intro h n
    rcases h with ⟨hψ, hφ_or_next⟩
    cases n with
    | zero =>
        left
        simpa using hψ
    | succ n =>
        rcases hφ_or_next with hφ | hnext
        · right
          exact ⟨0, Nat.zero_lt_succ n, by simpa using hφ⟩
        · rcases hnext n with hψn | hbefore
          · left
            simpa [OmegaWord.drop_drop, Nat.add_comm] using hψn
          · rcases hbefore with ⟨k, hk, hφk⟩
            right
            refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
            simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hφk

/-- The one-step semantic operator whose greatest fixed point is `φ R ψ`. -/
def releaseStepSet
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (X : Set (OmegaWord Letter)) : Set (OmegaWord Letter) :=
  {word |
    Satisfies interp word ψ ∧
      (Satisfies interp word φ ∨ OmegaWord.drop word 1 ∈ X)}

theorem releaseStepSet_mono
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    {X Y : Set (OmegaWord Letter)}
    (hXY : X ⊆ Y) :
    releaseStepSet interp φ ψ X ⊆ releaseStepSet interp φ ψ Y := by
  intro word hword
  rcases hword with ⟨hψ, hφ_or_next⟩
  refine ⟨hψ, ?_⟩
  rcases hφ_or_next with hφ | hnext
  · exact Or.inl hφ
  · exact Or.inr (hXY hnext)

/-- `φ R ψ` is a fixed point of the release one-step operator. -/
theorem satisfies_release_fixedPoint
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP) :
    {word | Satisfies interp word (PositiveLTL.release φ ψ)} =
      releaseStepSet interp φ ψ
        {word | Satisfies interp word (PositiveLTL.release φ ψ)} := by
  ext word
  exact satisfies_release_unfold interp word φ ψ

/--
Greatest-fixed-point coinduction for `release`.

Any predicate `P` whose states satisfy the one-step release body is contained
in `φ R ψ`.
-/
theorem satisfies_release_coinduction
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (P : OmegaWord Letter -> Prop)
    (hstep :
      ∀ word,
        P word ->
          Satisfies interp word ψ ∧
            (Satisfies interp word φ ∨ P (OmegaWord.drop word 1))) :
    ∀ word,
      P word ->
        Satisfies interp word (PositiveLTL.release φ ψ) := by
  intro word hP n
  induction n generalizing word with
  | zero =>
      left
      simpa using (hstep word hP).1
  | succ n ih =>
      rcases hstep word hP with ⟨_hψ, hφ_or_next⟩
      rcases hφ_or_next with hφ | hnext
      · right
        exact ⟨0, Nat.zero_lt_succ n, by simpa using hφ⟩
      · rcases ih (OmegaWord.drop word 1) hnext with hψn | hbefore
        · left
          simpa [OmegaWord.drop_drop, Nat.add_comm] using hψn
        · rcases hbefore with ⟨k, hk, hφk⟩
          right
          refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hφk

/--
Suffix-indexed form of release coinduction.

This is the convenient form for automata/backend arguments: a predicate on
time positions of one fixed word is enough to prove a release formula on every
suffix satisfying the predicate.
-/
theorem satisfies_release_coinduction_on_suffixes
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (P : Nat -> Prop)
    (hstep :
      ∀ n,
        P n ->
          Satisfies interp (OmegaWord.drop word n) ψ ∧
            (Satisfies interp (OmegaWord.drop word n) φ ∨ P (n + 1))) :
    ∀ n,
      P n ->
        Satisfies interp (OmegaWord.drop word n) (PositiveLTL.release φ ψ) := by
  let Q : OmegaWord Letter -> Prop :=
    fun suffix => ∃ n, P n ∧ suffix = OmegaWord.drop word n
  have hcoind :
      ∀ suffix,
        Q suffix ->
          Satisfies interp suffix ψ ∧
            (Satisfies interp suffix φ ∨ Q (OmegaWord.drop suffix 1)) := by
    intro suffix hsuffix
    rcases hsuffix with ⟨n, hn, rfl⟩
    rcases hstep n hn with ⟨hψ, hφ_or_next⟩
    refine ⟨hψ, ?_⟩
    rcases hφ_or_next with hφ | hnext
    · exact Or.inl hφ
    · refine Or.inr ⟨n + 1, hnext, ?_⟩
      simp [OmegaWord.drop_drop, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
  intro n hn
  exact
    satisfies_release_coinduction interp φ ψ Q hcoind
      (OmegaWord.drop word n) ⟨n, hn, rfl⟩

/-- Every post-fixed point of the release operator is below `φ R ψ`. -/
theorem satisfies_release_greatest_postfixed
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (X : Set (OmegaWord Letter))
    (hpost : X ⊆ releaseStepSet interp φ ψ X) :
    X ⊆ {word | Satisfies interp word (PositiveLTL.release φ ψ)} := by
  intro word hword
  exact satisfies_release_coinduction interp φ ψ (fun word => word ∈ X)
    (fun word hX => hpost hX)
    word hword

/-- `φ R ψ` is the greatest fixed point of the release one-step operator. -/
theorem satisfies_release_greatest_fixedPoint
    {AP : Type u} {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ ψ : PositiveLTL AP)
    (X : Set (OmegaWord Letter))
    (hfix : releaseStepSet interp φ ψ X = X) :
    X ⊆ {word | Satisfies interp word (PositiveLTL.release φ ψ)} := by
  apply satisfies_release_greatest_postfixed interp φ ψ X
  intro word hword
  simpa [hfix] using hword

end PositiveLTL

end DistributedSynthesis
