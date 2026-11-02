/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.BoundedWinning

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [Nonempty I₁] [Nonempty I₂] [Nonempty O₁] [Nonempty O₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)

/-- Exact equality with N |Sigma|^D, not a larger convenient bound. -/
theorem compressionBound_exact : compressionBound I₁ I₂ O₁ O₂ G Q D =
    (Nat.card G * Nat.card Q *
      Nat.card (O₁ × O₂) ^ (∑ t : Fin D, Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ (t.val+1)) *
      2 ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D)) *
      Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  simp only [compressionBound,StrategyBlockType,blockType_card_exact,blockWord_card]

include M q₀ in
theorem compressionBound_positive : 0 < compressionBound I₁ I₂ O₁ O₂ G Q D := by
  letI : Nonempty G := ⟨M.start⟩
  letI : Nonempty Q := ⟨q₀⟩
  rw [compressionBound_exact]
  letI : Nonempty (RoundRecord I₁ I₂ Graph Unit Unit) :=
    ⟨⟨Classical.choice inferInstance,Classical.choice inferInstance,.both,(),()⟩⟩
  have eventPositive : 0 < Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) := Nat.card_pos
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos)
      (Nat.pow_pos (Nat.card_pos (α:=O₁ × O₂)))) (Nat.pow_pos (by omega)))
    (Nat.pow_pos eventPositive)

/-- The full bounded-game strategy equivalence after the exact-D hole
conclusion of the common-view prerequisite. The prefix recognizer, guarded
objective, positive D and exact width are kept unchanged. -/
theorem bounded_game_equivalence_of_holes (χ : Q → Nat)
    (closed : PrefixClosed (fun g => M.eval g ∈ M.accept))
    (escape : ∀ (σ : StrategyPair I₁ I₂ O₁ O₂) (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit),
      (∃ n, M.eval (History.graphSequence (branchNode word n)) ∉ M.accept) →
      NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
    (positive : 0 < D)
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept) :
    (∃ tree, Winning (D:=D) M step (.bounded (compressionBound I₁ I₂ O₁ O₂ G Q D)) q₀ χ tree) ↔
      ∃ tree, Winning (D:=D) M step .replacement q₀ χ tree := by
  constructor
  · rintro ⟨tree,winning⟩
    exact ⟨tree,bounded_winning_replacement M step _ q₀ χ tree winning⟩
  · intro winning
    have component := (replacement_game_equivalence M step q₀ χ).mp winning
    obtain ⟨σ,realizes⟩ := (component_game_history_iff M step q₀ χ closed escape positive).mp component
    let K := Finset.univ.sup χ
    have bounded : ∀ q, χ q ≤ K := fun q => Finset.le_sup (Finset.mem_univ q)
    exact ⟨_,algorithm_winning_bounded M step q₀ σ χ realizes K bounded holes
      (compressionBound_positive M q₀) positive⟩
end
end Characterisation.ComponentGames.HistoryGame
