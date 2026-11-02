/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Library.Logic.LTL
import Mathlib.Tactic

/-! # Eliminating next using an alternating proposition

This word-level translation does not enforce a clock. Its correctness assumes
that the distinguished proposition changes truth value at every position.
The distributed clock construction discharges that assumption separately.
-/
namespace DistributedSynthesis.LTL

def NextFree {A : Type*} : LTL A → Prop
  | .verum | .falsum | .atom _ => True
  | .neg p => NextFree p
  | .next _ => False
  | .conj p q | .disj p q | .until p q | .release p q => NextFree p ∧ NextFree q

namespace NextFreeTranslation
variable {A B L : Type*}

def step (c p : LTL B) : LTL B :=
  .disj (.conj c (.until c (.conj (.neg c) p)))
    (.conj (.neg c) (.until (.neg c) (.conj c p)))

def translate (clock : B) (atom : A → B) : LTL A → LTL B
  | .verum => .verum
  | .falsum => .falsum
  | .atom a => .atom (atom a)
  | .neg p => .neg (translate clock atom p)
  | .conj p q => .conj (translate clock atom p) (translate clock atom q)
  | .disj p q => .disj (translate clock atom p) (translate clock atom q)
  | .next p => step (.atom clock) (translate clock atom p)
  | .until p q => .until (translate clock atom p) (translate clock atom q)
  | .release p q => .release (translate clock atom p) (translate clock atom q)

theorem nextFree (clock : B) (atom : A → B) (p : LTL A) :
    NextFree (translate clock atom p) := by
  induction p <;> simp_all [translate, step, NextFree]

theorem until_switch (I : B → L → Prop) (w : OmegaWord L) (c p : LTL B)
    (h₀ : Satisfies I w c) (h₁ : ¬ Satisfies I (w.drop 1) c) :
    Satisfies I w (.until c (.conj (.neg c) p)) ↔ Satisfies I (w.drop 1) p := by
  constructor
  · rintro ⟨n, ⟨hn, hp⟩, hall⟩
    have : n = 1 := by
      by_contra h
      by_cases hz : n = 0
      · subst n; exact hn (by simpa using h₀)
      · exact h₁ (hall 1 (by omega))
    simpa [this] using hp
  · intro hp
    refine ⟨1, ⟨h₁, hp⟩, ?_⟩
    intro k hk
    have : k = 0 := by omega
    simpa [this] using h₀

theorem step_correct (I : B → L → Prop) (w : OmegaWord L) (c p : LTL B)
    (h : Satisfies I (w.drop 1) c ↔ ¬ Satisfies I w c) :
    Satisfies I w (step c p) ↔ Satisfies I (w.drop 1) p := by
  classical
  by_cases hc : Satisfies I w c
  · have hn : ¬ Satisfies I (w.drop 1) c := fun h' ↦ (h.mp h') hc
    simpa only [step, Satisfies, hc, true_and, not_true_eq_false, false_and,
      or_false] using until_switch I w c p hc hn
  · have hn := h.mpr hc
    have hs := until_switch I w (.neg c) p hc (by simpa [Satisfies] using hn)
    simpa only [step, Satisfies, hc, false_and, not_false_eq_true, true_and,
      false_or, not_not] using hs

/-- Truth is preserved at every suffix. No stuttering or resampling occurs. -/
theorem correct (clock : B) (atom : A → B) (I : B → L → Prop) (w : OmegaWord L)
    (alternates : ∀ t, I clock (w (t+1)) ↔ ¬ I clock (w t)) (p : LTL A) (t : Nat) :
    Satisfies I (w.drop t) (translate clock atom p) ↔
      Satisfies (fun a l ↦ I (atom a) l) (w.drop t) p := by
  induction p generalizing t with
  | verum => rfl
  | falsum => rfl
  | atom a => rfl
  | neg p ih => simp only [translate, Satisfies, ih]
  | conj p q ihp ihq => simp only [translate, Satisfies, ihp, ihq]
  | disj p q ihp ihq => simp only [translate, Satisfies, ihp, ihq]
  | next p ih =>
    rw [translate, step_correct I (w.drop t) (.atom clock) _ (by
      simpa [Satisfies, OmegaWord.drop] using alternates t)]
    simpa only [Satisfies, OmegaWord.drop_drop] using ih (t+1)
  | «until» p q ihp ihq => simp only [translate, Satisfies, OmegaWord.drop_drop, ihp, ihq]
  | «release» p q ihp ihq => simp only [translate, Satisfies, OmegaWord.drop_drop, ihp, ihq]

end NextFreeTranslation
end DistributedSynthesis.LTL
