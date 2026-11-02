/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockMoveCompleteness

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxSynthPendingDepth 16

section Target
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

omit [DecidableEq I₁] [DecidableEq I₂] in
theorem strategyBoundary_initial :
    strategyBoundary M step q₀ σ (fun _ : BlockSlots B => []) = initialBlockBoundary M q₀ B := by
  classical
  simp [strategyBoundary,initialBlockBoundary,extractInputShape,Recognizer.eval,Recognizer.evalFrom,
    History.graphSequence,strategyHistoryLabel]
  funext p i j
  exact (extractInputShape_exact (fun _ : BlockSlots B => ([] : EnvHistory I₁ I₂)) p i j).mpr rfl

theorem strategyBoundary_target (past : BlockSlots B → EnvHistory I₁ I₂)
    (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (source : move.source = strategyBoundary M step q₀ σ past)
    (outputs : ∀ t s, move.policy t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (mask : ComponentMask I₁ I₂ B D) :
    strategyBoundary M step q₀ σ (closingLayerHistory past D ∘ (move.response mask).keep) =
      blockTarget M step move mask := by
  have rep : RepresentsInputShape past move.source.shape := by
    rw [source]
    exact extractInputShape_exact past
  have graphs : ∀ i, move.source.graph i = M.eval (History.graphSequence (past i)) :=
    fun i => congrArg (fun b => b.graph i) source
  have states : ∀ i, move.source.objective i = strategyHistoryLabel σ step q₀ (past i) :=
    fun i => congrArg (fun b => b.objective i) source
  change BlockBoundary.mk _ _ _ = BlockBoundary.mk _ _ _
  rw [BlockBoundary.mk.injEq]
  refine ⟨?_,?_,?_⟩
  · funext p i j
    apply Bool.eq_iff_iff.mpr
    exact (extractInputShape_exact _ p i j).trans (blockTarget_shape M step move past rep mask p i j).symm
  · funext i
    exact (blockTarget_graph M step move past mask graphs i).symm
  · funext i
    exact (closingLayerLabels_strategyHistory σ past step q₀ move.source.objective states move.policy outputs
      D (Nat.le_refl _) ((move.response mask).keep i)).symm

end Target

section Complete
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D K : Nat}
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q] [Inhabited I₁] [Inhabited I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
variable (P : List Graph → Prop) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (commonRoots : CommonBlockRoots (I₁:=I₁) (I₂:=I₂) P D)
variable (bound : compressionBound I₁ I₂ O₁ O₂ G Q D ≤ B+1)

include recognizes commonRoots bound in
/-- Every winning distributed strategy yields a winning strategy in the
finite block game. Rank-minimal replacements are chosen at source roots.
Every hidden thread is checked, including threads that are not one original
execution of the distributed strategy. -/
theorem blockGame_complete (positive : 0 < D)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
      NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n)))) :
    ∃ tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D),
      (blockGame M step χ (initialBlockOutcome M q₀ B D) ((0,0) : HandoverCode B K)).WinningTree tree := by
  classical
  letI : Inhabited (BlockOutcome I₁ I₂ G Q B D) := ⟨initialBlockOutcome M q₀ B D⟩
  let score h := χ (strategyHistoryLabel σ step q₀ h)
  let rank := treeRank score winning K
  have moves := strategy_move_exists M step q₀ P recognizes commonRoots bound σ rank
  choose select spec using moves
  let family (node : List (BlockOutcome I₁ I₂ G Q B D)) : BlockSlots B → EnvHistory I₁ I₂ :=
    node.reverseRecOn (fun _ => []) (fun _ outcome past =>
      closingLayerHistory past D ∘ ((select past).response outcome.component).keep)
  let tree node := select (family node)
  have familyStep (node : List (BlockOutcome I₁ I₂ G Q B D)) (outcome : BlockOutcome I₁ I₂ G Q B D) :
      family (node++[outcome]) = closingLayerHistory (family node) D ∘ ((tree node).response outcome.component).keep := by
    simp only [family,List.reverseRecOn_concat,tree]
  have familyZero : family [] = fun _ => [] := by simp [family]
  have source node : (tree node).source = strategyBoundary M step q₀ σ (family node) := (spec _).1
  have outputs node := (spec (family node)).2.1
  have valid node : BlockMoveValid M step (tree node).source (tree node) := (spec _).2.2.1
  refine ⟨tree,(blockGame_winning_iff M step χ _ _ tree).mpr ⟨?_,?_⟩⟩
  · intro node supported
    have own := valid node
    refine ⟨?_,own.2⟩
    cases node using List.reverseRecOn with
    | nil =>
      change (tree []).source = initialBlockBoundary M q₀ B
      rw [source,familyZero,strategyBoundary_initial]
    | append_singleton node outcome =>
      have offered : blockOffers M step (tree node) outcome = true := by
        have parts : publicSupport (blockOffers M step) tree node = true ∧
            blockOffers M step (tree node) outcome = true := by
          simpa only [publicSupport_append,Bool.and_eq_true] using supported
        exact parts.2
      have target : outcome.target = blockTarget M step (tree node) outcome.component :=
        ((of_decide_eq_true offered) : _ ∧ _).1
      have last : (observableAt (initialBlockOutcome M q₀ B D) (node++[outcome])).target = outcome.target := by
        simp [observableAt]
      rw [last,source,familyStep,strategyBoundary_target M step q₀ σ (family node) (tree node)
        (source node) (outputs node),← target]
  · intro branch thread
    have witnesses n := (thread.edge n).2
    choose endpoint inside roots folds colors using witnesses
    dsimp only [observableThreadWord] at inside folds colors
    have progress n := (spec (family (branchNode branch n))).2.2.2 (branch n).component
      (((of_decide_eq_true (thread.edge n).1) : _ ∧ _).2)
      (endpoint n) (inside n)
    choose chosen kept decreases replay using progress
    let actual n := family (branchNode branch n) (thread.code n).1
    let replacement n := family (branchNode branch n) (chosen n)
    let suffix n := (scenarioWord D (endpoint n)).val
    apply folded_suffixes_parity score winning K actual replacement suffix (fun n => (thread.code (n+1)).2)
    · intro n
      have result := decreases n
      rw [roots n] at result
      exact result
    · intro n
      change family (branchNode branch n++[branch n]) (thread.code (n+1)).1 = _
      rw [familyStep]
      change closingLayerHistory (family (branchNode branch n)) D
        (((tree (branchNode branch n)).response (branch n).component).keep (thread.code (n+1)).1) = _
      rw [← folds n]
      change closingLayerHistory (family (branchNode branch n)) D
        (((select (family (branchNode branch n))).response (branch n).component).keep
          (((select (family (branchNode branch n))).response (branch n).component).fold (endpoint n))) = _
      rw [kept n,wordScenario_history]
    · intro n
      change 0 < (scenarioWord D (endpoint n)).val.length
      rw [(scenarioWord D (endpoint n)).property]
      exact positive
    · intro n
      rw [← colors n]
      have states : ∀ i, (tree (branchNode branch n)).source.objective i =
          strategyHistoryLabel σ step q₀ (family (branchNode branch n) i) :=
        fun i => congrArg (fun b => b.objective i) (source _)
      rw [blockColor_strategy step (tree (branchNode branch n)) (family (branchNode branch n)) σ q₀ states (outputs _) χ]
      unfold blockMinimum
      apply rangeMin_congr
      intro k _
      apply congrArg χ
      exact (replay n ((scenarioWord D (endpoint n)).val.take (0+k))
        (by simp only [List.length_take,(scenarioWord D (endpoint n)).property]; exact Nat.min_le_right _ _)).symm

end Complete
end
end Characterisation.PeriodicBlocks
