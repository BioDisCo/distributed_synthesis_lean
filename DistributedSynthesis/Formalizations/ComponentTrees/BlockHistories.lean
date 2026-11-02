/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockReadback

/-! Reindex actual histories by the existing complete-block alphabet.
No alternative history or finite-word representation is introduced.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I₁ I₂ : Type} {D : Nat}

theorem blockHistory_injective (positive : 0 < D) :
    Function.Injective (@blockHistory I₁ I₂ D) := by
  intro words
  induction words with
  | nil =>
    intro other eq
    have len := congrArg List.length eq
    rw [blockHistory_length, blockHistory_length] at len
    have zero : other.length = 0 := Nat.eq_of_mul_eq_mul_right positive len.symm
    exact (List.length_eq_zero_iff.mp zero).symm
  | cons u words ih =>
    intro other eq
    cases other with
    | nil =>
      have len := congrArg List.length eq
      rw [blockHistory_length, blockHistory_length] at len
      simp only [List.length_cons, List.length_nil, Nat.zero_mul] at len
      nlinarith
    | cons v other =>
      change u.val ++ blockHistory words = v.val ++ blockHistory other at eq
      have heads := List.append_inj_left eq (u.property.trans v.property.symm)
      have uv : u = v := Subtype.ext heads
      subst v
      exact congrArg (List.cons u) (ih (List.append_cancel_left eq))

theorem exists_blockHistory (n : Nat) (h : EnvHistory I₁ I₂)
    (length : List.length h = n*D) :
    ∃ words : List (BlockInput I₁ I₂ D), blockHistory words = h ∧ words.length = n := by
  induction n generalizing h with
  | zero =>
    have empty : h = [] := List.length_eq_zero_iff.mp (by simpa using length)
    exact ⟨[], empty.symm, rfl⟩
  | succ n ih =>
    have atLeast : D ≤ List.length h := by rw [length, Nat.succ_mul]; omega
    let first : BlockInput I₁ I₂ D := ⟨h.take D, by rw [List.length_take, Nat.min_eq_left atLeast]⟩
    obtain ⟨words, exactTail, count⟩ := ih (h.drop D) (by rw [List.length_drop, length, Nat.succ_mul]; omega)
    refine ⟨first :: words, ?_, by simp [count]⟩
    change h.take D ++ blockHistory words = h
    rw [exactTail, List.take_append_drop]

/-- Inverse of `blockHistory` on histories whose length is divisible by D.
The fallback for other lengths is irrelevant to all position histories. -/
def historyBlocks (D : Nat) (h : EnvHistory I₁ I₂) : List (BlockInput I₁ I₂ D) :=
  if ex : ∃ words : List (BlockInput I₁ I₂ D), blockHistory words = h then ex.choose else []

theorem historyBlocks_blockHistory (positive : 0 < D) (words : List (BlockInput I₁ I₂ D)) :
    historyBlocks D (blockHistory words) = words := by
  have ex : ∃ w : List (BlockInput I₁ I₂ D), blockHistory w = blockHistory words := ⟨words, rfl⟩
  unfold historyBlocks
  rw [dif_pos ex]
  exact blockHistory_injective positive ex.choose_spec

theorem blockHistory_historyBlocks (n : Nat) (h : EnvHistory I₁ I₂)
    (length : List.length h = n*D) : blockHistory (historyBlocks D h) = h := by
  obtain ⟨words, eq, _⟩ := exists_blockHistory n h length
  have ex : ∃ w : List (BlockInput I₁ I₂ D), blockHistory w = h := ⟨words, eq⟩
  unfold historyBlocks
  rw [dif_pos ex]
  exact ex.choose_spec

theorem historyBlocks_length (positive : 0 < D) (n : Nat) (h : EnvHistory I₁ I₂)
    (length : List.length h = n*D) : (historyBlocks D h).length = n := by
  have eq := congrArg List.length (blockHistory_historyBlocks n h length)
  rw [blockHistory_length, length] at eq
  exact Nat.eq_of_mul_eq_mul_right positive eq

theorem historyBlocks_append (positive : 0 < D) (n : Nat) (h : EnvHistory I₁ I₂)
    (length : List.length h = n*D) (u : BlockInput I₁ I₂ D) :
    historyBlocks D (h ++ u.val) = historyBlocks D h ++ [u] := by
  have eq : h ++ u.val = blockHistory (historyBlocks D h ++ [u]) := by
    rw [blockHistory_append, blockHistory_historyBlocks n h length]
  rw [eq, historyBlocks_blockHistory positive]

end
end Characterisation.ComponentTrees
