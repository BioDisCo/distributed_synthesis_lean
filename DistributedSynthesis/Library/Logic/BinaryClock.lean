/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.BlockTranslation

/-! # A clock encoded in the two binary outputs

Each block has shape `11 0 b₁ 0 ... b_K 0` in each output. Its length
`2*K+3` is odd; the `K` data bits occupy odd offsets. The formula uses only
the two supplied output propositions, never a fresh clock proposition.
-/

namespace DistributedSynthesis.LTL.BinaryClock
open BlockTranslation

def length (K : Nat) : Nat := 2*K+3

def marker {AP : Type*} (one : AP) : LTL AP := .conj (.atom one) (.next (.atom one))

def zeros {AP : Type*} (one two : AP) (K : Nat) : LTL AP :=
  ((List.range (K+1)).map fun j ↦ nextN (2*j+2)
    (.conj (.neg (.atom one)) (.neg (.atom two)))).foldr LTL.conj .verum

def frame {AP : Type*} (one two : AP) (K : Nat) : LTL AP :=
  .conj (marker one) (.always (.disj (.neg (marker one))
    (.conj (.atom two) (.conj (.next (.atom two))
      (.conj (zeros one two K) (nextN (length K) (marker one)))))))

private theorem satisfies_all {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (xs : List (LTL AP)) :
    Satisfies I w (xs.foldr LTL.conj .verum) ↔ ∀ φ ∈ xs, Satisfies I w φ := by
  induction xs with
  | nil => simp [Satisfies]
  | cons φ xs ih => simp [Satisfies, ih]

theorem marker_iff {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (one : AP) (t : Nat) :
    Satisfies I (w.drop t) (marker one) ↔ I one (w t) ∧ I one (w (t+1)) := by
  simp [marker, Satisfies, OmegaWord.drop]

theorem zeros_iff {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (one two : AP) (K t : Nat) :
    Satisfies I (w.drop t) (zeros one two K) ↔
      ∀ j, j ≤ K → ¬ I one (w (t+(2*j+2))) ∧ ¬ I two (w (t+(2*j+2))) := by
  simp [zeros, satisfies_all, satisfies_nextN, Satisfies, OmegaWord.drop,
    Nat.lt_succ_iff]

theorem frame_iff {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (one two : AP) (K : Nat) :
    Satisfies I w (frame one two K) ↔
      Satisfies I w (marker one) ∧
      ∀ t, Satisfies I (w.drop t) (marker one) →
        I two (w t) ∧ I two (w (t+1)) ∧
          (∀ j, j ≤ K → ¬ I one (w (t+(2*j+2))) ∧ ¬ I two (w (t+(2*j+2)))) ∧
          Satisfies I (w.drop (t+length K)) (marker one) := by
  classical
  simp only [frame, Satisfies, satisfies_always, or_iff_not_imp_left, not_not,
    zeros_iff, satisfies_nextN, OmegaWord.drop_drop, OmegaWord.drop_apply, Nat.add_zero]

/-- The finite frame formula forces a marker at every block boundary. -/
theorem marker_at_block {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (one two : AP) (K : Nat)
    (hf : Satisfies I w (frame one two K)) (n : Nat) :
    Satisfies I (w.drop (length K*n)) (marker one) := by
  have h := (frame_iff I w one two K).mp hf
  induction n with
  | zero => simpa using h.1
  | succ n ih => simpa only [Nat.mul_succ] using (h.2 _ ih).2.2.2

/-- Separator zeros alone exclude accidental markers. -/
theorem marker_only_at_blocks {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (one : AP) (K : Nat)
    (hz : ∀ n j, j ≤ K → ¬ I one (w (length K*n+(2*j+2)))) (t : Nat)
    (hm : Satisfies I (w.drop t) (marker one)) : ∃ n, t = length K*n := by
    have hbits := (marker_iff I w one t).mp hm
    have hdecomp := Nat.mod_add_div t (length K)
    have hrem := Nat.mod_lt t (show 0 < length K by unfold length; omega)
    let r := t % length K
    have ht : t = length K*(t / length K) + r := by
      dsimp [r]
      omega
    have hr : r < 2*K+3 := hrem
    by_cases he : r = 0
    · exact ⟨t / length K, by omega⟩
    · exfalso
      by_cases hodd : r % 2 = 1
      · let j := (r-1)/2
        have hj : j ≤ K := by dsimp [j]; omega
        have hjr : 2*j+2 = r+1 := by dsimp [j]; omega
        have hz := hz (t / length K) j hj
        have ht' : length K*(t / length K)+(2*j+2) = t+1 := by omega
        rw [ht'] at hz
        exact hz hbits.2
      · let j := (r-2)/2
        have hj : j ≤ K := by dsimp [j]; omega
        have hjr : 2*j+2 = r := by dsimp [j]; omega
        have hz := hz (t / length K) j hj
        have ht' : length K*(t / length K)+(2*j+2) = t := by omega
        rw [ht'] at hz
        exact hz hbits.1

/-- No accidental `11` marker occurs in a header tail, a data position, or
across a block boundary. This discharges the clock premise of block translation. -/
theorem clock_exact {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (one two : AP) (K : Nat)
    (hf : Satisfies I w (frame one two K)) (t : Nat) :
    Satisfies I (w.drop t) (marker one) ↔ ∃ n, t = length K*n := by
  constructor
  · exact marker_only_at_blocks I w one K (fun n j hj ↦
      (((frame_iff I w one two K).mp hf).2 _
        (marker_at_block I w one two K hf n)).2.2.1 j hj |>.1) t
  · rintro ⟨n, rfl⟩
    exact marker_at_block I w one two K hf n

/-- Constructing the fixed headers and separators suffices for the whole
frame formula; data positions are completely unrestricted. -/
theorem frame_of_pattern {AP Letter : Type*} (I : AP → Letter → Prop)
    (w : OmegaWord Letter) (one two : AP) (K : Nat)
    (hh : ∀ n, I one (w (length K*n)) ∧ I one (w (length K*n+1)) ∧
      I two (w (length K*n)) ∧ I two (w (length K*n+1)))
    (hz : ∀ n j, j ≤ K → ¬ I one (w (length K*n+(2*j+2))) ∧
      ¬ I two (w (length K*n+(2*j+2)))) : Satisfies I w (frame one two K) := by
  have hm : ∀ n, Satisfies I (w.drop (length K*n)) (marker one) :=
    fun n ↦ (marker_iff I w one _).mpr ⟨(hh n).1, (hh n).2.1⟩
  apply (frame_iff I w one two K).mpr
  refine ⟨by simpa using hm 0, ?_⟩
  intro t ht
  obtain ⟨n, rfl⟩ := marker_only_at_blocks I w one K (fun n j hj ↦ (hz n j hj).1) t ht
  refine ⟨(hh n).2.2.1, (hh n).2.2.2, hz n, ?_⟩
  simpa only [Nat.mul_succ] using hm (n+1)

end DistributedSynthesis.LTL.BinaryClock
