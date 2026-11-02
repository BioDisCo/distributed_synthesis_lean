/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteToHistoryRuns
import DistributedSynthesis.Formalizations.ComponentGames.HistoryToFiniteRuns
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusConsequences
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusBound

namespace Characterisation.ComponentGames.Representation
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B L : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Fintype G] [Fintype Q] [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (χ : Q → Nat) (priorityBound : ∀ q, χ q ≤ L)
variable (W : Nat) (q₀ : Q) (positive : 0 < B)
variable (capacity : W * Nat.card (FiniteArena.Word I₁ I₂ D) ≤ B)

include capacity in
/-- Lemma bounded-finite-game-equivalence: both complete strategy transfers
for the literal bounded history game, including all runs and finite plays. -/
theorem bounded_finite_game_equivalence :
    (∃ tree, HistoryGame.Winning (D:=D) M step (.bounded W) q₀ χ tree) ↔
    ∃ tree, (FiniteArena.product (D:=D) M step χ priorityBound W q₀ positive).WinningTree tree := by
  constructor
  · rintro ⟨tree,win⟩
    exact ⟨_,(FiniteArena.product_winning_iff M step χ priorityBound W q₀ positive _).mpr
      (HistoryToFinite.winning M step χ priorityBound W q₀ positive tree win)⟩
  · rintro ⟨tree,win⟩
    exact ⟨_,FiniteToHistory.winning M step χ priorityBound W q₀ positive capacity tree
      ((FiniteArena.product_winning_iff M step χ priorityBound W q₀ positive tree).mp win)⟩

include capacity in
theorem solve_bounded_history : FiniteArena.solve (D:=D) M step χ priorityBound W q₀ positive = true ↔
    ∃ tree, HistoryGame.Winning (D:=D) M step (.bounded W) q₀ χ tree := by
  rw [FiniteArena.solve_correct]
  constructor
  · rintro ⟨tree,win⟩
    exact ⟨_,FiniteToHistory.winning M step χ priorityBound W q₀ positive capacity tree win⟩
  · rintro ⟨tree,win⟩
    exact ⟨_,HistoryToFinite.winning M step χ priorityBound W q₀ positive tree win⟩

/-- The carrier capacity is exactly the paper's N |Sigma|^(2D).
The spare ambient label used by TransitionAlphabet never becomes a root,
as relation_no_unused_slots proves. -/
theorem exact_paper_capacity (N : Nat) :
    (N * Nat.card (I₁ × I₂ × Graph)^D) * Nat.card (FiniteArena.Word I₁ I₂ D) =
      N * Nat.card (I₁ × I₂ × Graph)^(2*D) := by
  rw [blockWord_card,Nat.card_congr (envRecordEquiv I₁ I₂).symm]
  rw [Nat.mul_assoc,← Nat.pow_add]
  congr 2
  omega

/-- No priority bound is supplied by the user: the finite state table
computes it. The block width W and resulting B remain the given exact ones. -/
def decideBounded [Nonempty I₁] [Nonempty I₂] (width : 0 < W) : Bool :=
  let B := W * Fintype.card (FiniteArena.Word I₁ I₂ D)
  let bound := Finset.univ.sup χ
  have positive : 0 < B := by
    letI : Nonempty Graph := ⟨.both⟩
    letI : Nonempty (RoundRecord I₁ I₂ Graph Unit Unit) :=
      ⟨⟨Classical.choice inferInstance,Classical.choice inferInstance,.both,(),()⟩⟩
    change 0 < W * Fintype.card (FiniteArena.Word I₁ I₂ D)
    rw [← Nat.card_eq_fintype_card,blockWord_card]
    exact Nat.mul_pos width (Nat.pow_pos Nat.card_pos)
  FiniteArena.solve (D:=D) (L:=bound) M step χ (fun q => Finset.le_sup (Finset.mem_univ q)) W q₀ positive

theorem decideBounded_correct [Nonempty I₁] [Nonempty I₂] (width : 0 < W) :
    decideBounded (D:=D) M step χ W q₀ width = true ↔
      ∃ tree, HistoryGame.Winning (D:=D) M step (.bounded W) q₀ χ tree := by
  unfold decideBounded
  exact solve_bounded_history M step χ _ W q₀ _ (by rw [Nat.card_eq_fintype_card])

end Characterisation.ComponentGames.Representation
