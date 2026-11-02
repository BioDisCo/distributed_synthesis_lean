/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableSynthesis
namespace Characterisation.ComponentGames.ExecutableSynthesis
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Representation
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Nonempty I₁] [Nonempty I₂]
variable [Fintype O₁] [Fintype O₂] [LinearOrder O₁] [LinearOrder O₂]
variable [Fintype G] [Fintype Q] [LinearOrder G] [LinearOrder Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (χ : Q → Nat) (W : Nat) (q₀ : Q) (width : 0 < W) (fallback : O₁ × O₂)

def synthesizeBounded : Option (StrategyPair I₁ I₂ O₁ O₂) :=
  let B := W * Fintype.card (FiniteArena.Word I₁ I₂ D)
  let bound := Finset.univ.sup χ
  have positive : 0 < B := by
    letI : Nonempty Graph := ⟨.both⟩
    letI : Nonempty (RoundRecord I₁ I₂ Graph Unit Unit) :=
      ⟨⟨Classical.choice inferInstance,Classical.choice inferInstance,.both,(),()⟩⟩
    change 0 < W * Fintype.card (FiniteArena.Word I₁ I₂ D)
    rw [← Nat.card_eq_fintype_card,blockWord_card]
    exact Nat.mul_pos width (Nat.pow_pos Nat.card_pos)
  synthesize (D:=D) (L:=bound) M step χ (fun q => Finset.le_sup (Finset.mem_univ q)) W q₀ positive
    (by rw [Nat.card_eq_fintype_card]) fallback

theorem synthesizeBounded_complete :
    (∃ σ, synthesizeBounded (D:=D) M step χ W q₀ width fallback = some σ) ↔
      decideBounded (D:=D) M step χ W q₀ width = true := by
  rw [decideBounded_correct]
  unfold synthesizeBounded
  exact synthesize_complete M step χ _ W q₀ _ _ fallback

theorem synthesizeBounded_sound (σ : StrategyPair I₁ I₂ O₁ O₂)
    (found : synthesizeBounded (D:=D) M step χ W q₀ width fallback = some σ)
    (closed : PrefixClosed (fun g => M.eval g ∈ M.accept)) (phasePositive : 0 < D)
    (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (live : ∀ n, M.eval (History.graphSequence (branchNode word n)) ∈ M.accept) :
    NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))) := by
  unfold synthesizeBounded at found
  exact synthesize_sound M step χ _ W q₀ _ _ fallback σ found closed phasePositive word live
end Characterisation.ComponentGames.ExecutableSynthesis
