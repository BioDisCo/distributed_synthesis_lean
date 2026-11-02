/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockSoundness
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockCompleteness

/-! Exact reduction to the newly constructed finite periodic-block game.
The guarded objective accepts executions leaving the live prefix language.
No old synthesis or phase-game equivalence is used. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
set_option maxSynthPendingDepth 16

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D K : Nat}
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q] [Inhabited I₁] [Inhabited I₂]
variable [Nonempty O₁] [Nonempty O₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (escape : ∀ (σ : StrategyPair I₁ I₂ O₁ O₂) (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit),
  (∃ n, ¬ P (History.graphSequence (branchNode word n))) →
    NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))

include closed recognizes escape in
theorem periodic_block_game_iff (positive : 0 < D) (bounded : ∀ q, χ q ≤ K)
    (commonRoots : CommonBlockRoots (I₁:=I₁) (I₂:=I₂) P D)
    (bound : compressionBound I₁ I₂ O₁ O₂ G Q D ≤ B+1) :
    (∃ tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D),
      (blockGame M step χ (initialBlockOutcome M q₀ B D) ((0,0) : HandoverCode B K)).WinningTree tree) ↔
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
        NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))) := by
  classical
  constructor
  · rintro ⟨tree,winning⟩
    obtain ⟨σ,correct⟩ := blockGame_sound M step q₀ χ bounded tree P closed recognizes positive winning
    refine ⟨σ,fun word => ?_⟩
    by_cases live : ∀ n, P (History.graphSequence (branchNode word n))
    · exact correct word live
    · exact escape σ word (not_forall.mp live)
  · rintro ⟨σ,winning⟩
    exact blockGame_complete M step q₀ χ P recognizes commonRoots bound positive σ winning

include escape in
/-- Nowhere denseness and omega-regularity supply a fixed positive block
length and a uniform finite width. Realizability is equivalent to winning
the concrete block game with those bounds. -/
theorem holes_periodic_block_game (A : Set (Nat → Graph))
    (regular : OmegaRegular A) (holes : GeometricHoles A)
    (prefixes : P = LivePrefix A) (bounded : ∀ q, χ q ≤ K)
    (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) :
    ∃ D B : Nat, 0 < D ∧
      ((∃ tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D),
        (blockGame M step χ (initialBlockOutcome M q₀ B D) ((0,0) : HandoverCode B K)).WinningTree tree) ↔
      ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
        ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
          NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n)))) := by
  classical
  subst P
  obtain ⟨D,positive,common⟩ := holes_commonBlockRoots (I₁:=I₁) (I₂:=I₂) A regular holes
  let B := compressionBound I₁ I₂ O₁ O₂ G Q D
  refine ⟨D,B,positive,?_⟩
  exact periodic_block_game_iff M step q₀ χ (LivePrefix A) (livePrefix_closed A) recognizes escape
    positive bounded common (Nat.le_succ B)

end
end Characterisation.PeriodicBlocks
