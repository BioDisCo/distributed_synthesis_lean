/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableReadback
namespace Characterisation.ComponentGames.ExecutableReadback
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks HistoryGame
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq Q]
variable [LinearOrder O₁] [LinearOrder O₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
variable (closed : PrefixClosed (fun g => M.eval g ∈ M.accept))
variable (fallback : O₁ × O₂)

include closed in
theorem strategy_wins (positive : 0 < D) (χ : Q → Nat)
    (winning : Winning M step .component q₀ χ tree)
    (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (live : ∀ n, M.eval (History.graphSequence (branchNode word n)) ∈ M.accept) :
    NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel (strategy M step tree fallback) step q₀ (branchNode word n))) := by
  let σ := strategy M step tree fallback
  have implements := strategy_implements M step tree q₀ winning.1 fallback
  obtain ⟨branch,supported,run,histories,words⟩ := component_word_run M step tree q₀ winning.1 word live
  have parity := winning.2 branch supported run
  let score n := χ (strategyHistoryLabel σ step q₀ (branchNode word n))
  have minima : ∀ n, rangeMin
      (fun t => χ (stateAt step (tree (branchNode branch n)) (run.history n) (run.word n) t))
      0 (D-1) = cutBlockMin score (fun k => k*D) n := by
    intro n
    have full : (run.history n).val ++ (run.word n).val = branchNode word ((n+1)*D) := by
      rw [histories n,words n,Nat.add_mul,Nat.one_mul]
      exact prefix_append_segment word (n*D) D
    have alive : M.eval (History.graphSequence ((run.history n).val ++ (run.word n).val)) ∈ M.accept := by
      rw [full]; exact live _
    unfold cutBlockMin
    have span : (n+1)*D - n*D - 1 = D-1 := by simp [Nat.add_mul]
    rw [span]
    apply rangeMin_congr
    intro t within
    simp only [Nat.zero_add]
    rw [controller_stateAt M step q₀ tree winning.1 closed σ implements _ (supported n) _ _ alive,
      histories n,words n,eventBlock_take word D n t (by omega),prefix_append_segment]
  rw [funext minima] at parity
  exact (natSeqMinEvenParity_cutBlockMin score
    (fun _ _ h => Nat.mul_lt_mul_of_pos_right h positive) (by simp)).mp parity
end Characterisation.ComponentGames.ExecutableReadback
