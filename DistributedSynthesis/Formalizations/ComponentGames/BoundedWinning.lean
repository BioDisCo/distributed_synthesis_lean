/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.BoundedStrategy

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (σ : StrategyPair I₁ I₂ O₁ O₂) (χ : Q → Nat)
variable (winning : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
  NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
variable (K : Nat) (bounded : ∀ q, χ q ≤ K)
variable (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
variable (wide : 0 < compressionBound I₁ I₂ O₁ O₂ G Q D)

include bounded in
/-- The paper's entire bounded completeness construction, including every
supported play and every compatible run. Ranks are minimized at previous
roots, and the old partition key transfers the preceding block's priorities. -/
theorem algorithm_winning_bounded (positive : 0 < D) :
    Winning M step (.bounded (compressionBound I₁ I₂ O₁ O₂ G Q D)) q₀ χ
      (boundedTree M step q₀ σ (treeRank (fun h => χ (strategyHistoryLabel σ step q₀ h)) winning K) holes wide) := by
  let score h := χ (strategyHistoryLabel σ step q₀ h)
  let rank := treeRank score winning K
  let tree := boundedTree M step q₀ σ rank holes wide
  have legal := boundedTree_legal M step q₀ σ rank holes wide
  have faithful := boundedTree_faithful M step q₀ σ rank holes wide
  refine ⟨legal,fun branch supported run => ?_⟩
  have next (n : Nat) : Next M step (tree (branchNode branch n)) (branch n) := by
    have h := supported (n+1)
    change publicSupport (offers M step) tree (branchNode branch n ++ [branch n]) = true at h
    have both : publicSupport (offers M step) tree (branchNode branch n) = true ∧
        offers M step (tree (branchNode branch n)) (branch n) = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using h
    exact of_decide_eq_true both.2
  have progress n := boundedTree_progress M step q₀ σ rank holes wide (branchNode branch n) (branch n) (next n)
  have witnesses n := progress n (run.history (n+1))
    ((tree (branchNode branch n)).replacement (run.history n)) (run.word n) (run.next n)
  choose chosen extension decreases replay using witnesses
  let root n := ((tree (branchNode branch n)).replacement (run.history n)).val
  let colorNat n := rangeMin
    (fun t => χ (stateAt step (tree (branchNode branch n)) (run.history n) (run.word n) t)) 0 (D-1)
  have colorBound n : colorNat n ≤ K := by
    exact (rangeMin_le _ 0 (D-1) 0 (by omega)).trans (bounded _)
  let color n : Fin (K+1) := ⟨colorNat n,Nat.lt_succ_of_le (colorBound n)⟩
  apply folded_suffixes_parity score winning K root (fun n => (chosen n).val)
    (fun n => (run.word n).val) color decreases extension
  · intro n; rw [(run.word n).property]; exact positive
  · intro n
    change colorNat n = blockMinimum score (chosen n).val (run.word n).val
    unfold colorNat blockMinimum
    rw [(run.word n).property]
    apply rangeMin_congr
    intro t within
    simp only [Nat.zero_add]
    rw [faithful_stateAt M step q₀ σ _ (faithful _) (run.history n) (run.word n) t]
    exact congrArg χ (replay n ((run.word n).val.take t)
      (by simp only [List.length_take,(run.word n).property]; exact Nat.min_le_right _ _))
end
end Characterisation.ComponentGames.HistoryGame
