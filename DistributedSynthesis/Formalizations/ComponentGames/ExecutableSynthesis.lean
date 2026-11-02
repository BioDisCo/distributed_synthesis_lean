/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableReadbackWinning
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableFiniteToHistory

namespace Characterisation.ComponentGames.ExecutableSynthesis
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Representation
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B L : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [LinearOrder O₁] [LinearOrder O₂]
variable [Fintype G] [Fintype Q] [LinearOrder G] [LinearOrder Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (χ : Q → Nat) (priorityBound : ∀ q, χ q ≤ L)
variable (W : Nat) (q₀ : Q) (positive : 0 < B)
variable (capacity : W * Nat.card (FiniteArena.Word I₁ I₂ D) ≤ B)
variable (target : LabeledTree (FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B) (FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B))
variable (win : FiniteArena.Winning M step χ priorityBound W q₀ positive target)

def historyTree := ExecutableFiniteToHistory.tree M step W q₀ positive capacity target win.1

theorem historyTree_wins : HistoryGame.Winning M step .replacement q₀ χ
    (historyTree M step χ priorityBound W q₀ positive capacity target win) := by
  apply HistoryGame.bounded_winning_replacement M step W
  unfold historyTree
  rw [ExecutableFiniteToHistory.tree_eq]
  exact FiniteToHistory.winning M step χ priorityBound W q₀ positive capacity target win

def componentTree := ExecutableSimulation.tree M step
  (historyTree M step χ priorityBound W q₀ positive capacity target win) q₀
  (historyTree_wins M step χ priorityBound W q₀ positive capacity target win).1

theorem componentTree_wins : HistoryGame.Winning M step .component q₀ χ
    (componentTree M step χ priorityBound W q₀ positive capacity target win) := by
  unfold componentTree
  rw [ExecutableSimulation.tree_eq]
  exact HistoryGame.replacement_winning_component M step _ q₀ χ
    (historyTree_wins M step χ priorityBound W q₀ positive capacity target win)

variable (fallback : O₁ × O₂)

def strategy : StrategyPair I₁ I₂ O₁ O₂ := ExecutableReadback.strategy M step
  (componentTree M step χ priorityBound W q₀ positive capacity target win) fallback

theorem strategy_wins (closed : PrefixClosed (fun g => M.eval g ∈ M.accept)) (phasePositive : 0 < D)
    (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (live : ∀ n, M.eval (History.graphSequence (branchNode word n)) ∈ M.accept) :
    NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel
      (strategy M step χ priorityBound W q₀ positive capacity target win fallback) step q₀ (branchNode word n))) :=
  ExecutableReadback.strategy_wins M step q₀ _ closed fallback phasePositive χ
    (componentTree_wins M step χ priorityBound W q₀ positive capacity target win) word live

def synthesize : Option (StrategyPair I₁ I₂ O₁ O₂) :=
  match found : FiniteArena.extractController (D:=D) M step χ priorityBound W q₀ positive with
  | none => none
  | some policy => some (strategy M step χ priorityBound W q₀ positive capacity
      (FiniteController.tree (FiniteArena.product M step χ priorityBound W q₀ positive) policy)
      (FiniteArena.extractedController_wins M step χ priorityBound W q₀ positive policy found) fallback)

theorem synthesize_complete : (∃ σ, synthesize (D:=D) M step χ priorityBound W q₀ positive capacity fallback = some σ) ↔
    ∃ tree, HistoryGame.Winning (D:=D) M step (.bounded W) q₀ χ tree := by
  have finite : (∃ σ, synthesize (D:=D) M step χ priorityBound W q₀ positive capacity fallback = some σ) ↔
      ∃ policy, FiniteArena.extractController (D:=D) M step χ priorityBound W q₀ positive = some policy := by
    unfold synthesize
    split <;> simp_all
  rw [finite,FiniteArena.extractController_correct]
  exact (exists_congr (FiniteArena.product_winning_iff M step χ priorityBound W q₀ positive)).symm.trans
    (bounded_finite_game_equivalence M step χ priorityBound W q₀ positive capacity).symm

theorem synthesize_sound (σ : StrategyPair I₁ I₂ O₁ O₂)
    (found : synthesize (D:=D) M step χ priorityBound W q₀ positive capacity fallback = some σ)
    (closed : PrefixClosed (fun g => M.eval g ∈ M.accept)) (phasePositive : 0 < D)
    (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (live : ∀ n, M.eval (History.graphSequence (branchNode word n)) ∈ M.accept) :
    NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))) := by
  unfold synthesize at found
  split at found
  · contradiction
  · cases Option.some.inj found
    exact strategy_wins M step χ priorityBound W q₀ positive capacity _ _ fallback closed phasePositive word live

end Characterisation.ComponentGames.ExecutableSynthesis
