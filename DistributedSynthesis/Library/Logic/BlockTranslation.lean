/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.LTL
import Mathlib.Tactic

/-! # LTL interpretation on fixed-length blocks

The marker and atomic tests are ordinary target LTL formulas. The correctness
theorem explicitly requires that the marker holds exactly at block starts,
and that atomic tests decode the source word there. In particular this module
does not postulate an extra clock proposition or a realizability reduction.
-/

namespace DistributedSynthesis.LTL.BlockTranslation

def nextN {AP : Type*} : Nat → LTL AP → LTL AP
  | 0, φ => φ
  | n+1, φ => .next (nextN n φ)

theorem satisfies_nextN {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (n : Nat) (φ : LTL AP) :
    Satisfies I w (nextN n φ) ↔ Satisfies I (w.drop n) φ := by
  induction n generalizing w with
  | zero => simp [nextN]
  | succ n ih => simp [nextN, Satisfies, ih, Nat.add_comm]

/-- Replace source atoms by block tests, guard until by the block marker,
and translate release through its Boolean dual. -/
def translate {AP BP : Type*} (L : Nat) (marker : LTL BP)
    (atom : AP → LTL BP) : LTL AP → LTL BP
  | .verum => .verum
  | .falsum => .falsum
  | .atom a => atom a
  | .neg φ => .neg (translate L marker atom φ)
  | .conj φ ψ => .conj (translate L marker atom φ) (translate L marker atom ψ)
  | .disj φ ψ => .disj (translate L marker atom φ) (translate L marker atom ψ)
  | .next φ => nextN L (translate L marker atom φ)
  | .until φ ψ => .until (.disj (.neg marker) (translate L marker atom φ))
      (.conj marker (translate L marker atom ψ))
  | .release φ ψ => .neg (.until
      (.disj (.neg marker) (.neg (translate L marker atom φ)))
      (.conj marker (.neg (translate L marker atom ψ))))

private theorem marked_until (L : Nat) (hL : 0 < L)
    (P Q : Nat → Prop) (n : Nat) :
    (∃ d, (∃ m, L*n+d = L*m) ∧ Q (L*n+d) ∧
      ∀ e, e < d → (∃ m, L*n+e = L*m) → P (L*n+e)) ↔
    ∃ k, Q (L*(n+k)) ∧ ∀ j, j < k → P (L*(n+j)) := by
  constructor
  · rintro ⟨d, ⟨m, hm⟩, hq, hp⟩
    have hnm : n ≤ m := by nlinarith
    have hm' : n + (m-n) = m := by omega
    refine ⟨m-n, ?_, ?_⟩
    · simpa only [hm', ← hm] using hq
    · intro j hj
      have hj' : L*j < d := by nlinarith
      have he : L*n+L*j = L*(n+j) := by ring
      simpa only [he] using hp (L*j) hj' ⟨n+j, he⟩
  · rintro ⟨k, hq, hp⟩
    have he : L*n+L*k = L*(n+k) := by ring
    refine ⟨L*k, ⟨n+k, he⟩, ?_, ?_⟩
    · simpa only [he] using hq
    · rintro e he' ⟨m, hm⟩
      have hnm : n ≤ m := by nlinarith
      have hm' : n+(m-n) = m := by omega
      have hj : m-n < k := by nlinarith
      simpa only [hm', ← hm] using hp (m-n) hj

private theorem release_dual {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (φ ψ : LTL AP) :
    Satisfies I w (.release φ ψ) ↔
      ¬ Satisfies I w (.until (.neg φ) (.neg ψ)) := by
  classical
  simp only [Satisfies]
  push Not
  simp only [or_iff_not_imp_left]

/-- Semantic correctness on all source formulas and at every block start.
The atomic compiler and marker obligations are precisely the hypotheses. -/
theorem correct {AP BP A B : Type*} (L : Nat) (hL : 0 < L)
    (marker : LTL BP) (atom : AP → LTL BP)
    (I : AP → A → Prop) (J : BP → B → Prop)
    (source : OmegaWord A) (target : OmegaWord B)
    (clock : ∀ t, Satisfies J (target.drop t) marker ↔ ∃ n, t = L*n)
    (atoms : ∀ a n, Satisfies J (target.drop (L*n)) (atom a) ↔ I a (source n))
    (φ : LTL AP) (n : Nat) :
    Satisfies J (target.drop (L*n)) (translate L marker atom φ) ↔
      Satisfies I (source.drop n) φ := by
  induction φ generalizing n with
  | verum => rfl
  | falsum => rfl
  | atom a => simpa only [translate, Satisfies, OmegaWord.drop_apply, Nat.add_zero] using atoms a n
  | neg φ ih => exact not_congr (ih n)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ n) (ihψ n)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ n) (ihψ n)
  | next φ ih =>
    simp only [translate, satisfies_nextN, OmegaWord.drop_drop, Satisfies]
    simpa only [Nat.mul_add, Nat.mul_one] using ih (n+1)
  | «until» φ ψ ihφ ihψ =>
    classical
    simp only [translate, Satisfies, OmegaWord.drop_drop]
    simp only [clock, or_iff_not_imp_left, not_not, and_assoc]
    rw [marked_until L hL (fun t ↦ Satisfies J (target.drop t) (translate L marker atom φ))
      (fun t ↦ Satisfies J (target.drop t) (translate L marker atom ψ)) n]
    simp only [ihφ, ihψ, OmegaWord.drop_drop]
  | «release» φ ψ ihφ ihψ =>
    classical
    rw [release_dual]
    apply not_congr
    simp only [translate, Satisfies, OmegaWord.drop_drop]
    simp only [clock, or_iff_not_imp_left, not_not, and_assoc]
    rw [marked_until L hL (fun t ↦ ¬ Satisfies J (target.drop t) (translate L marker atom φ))
      (fun t ↦ ¬ Satisfies J (target.drop t) (translate L marker atom ψ)) n]
    simp only [ihφ, ihψ, OmegaWord.drop_drop]

end DistributedSynthesis.LTL.BlockTranslation
