/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.FiniteChoices
import DistributedSynthesis.Formalizations.PeriodicBlocks.FiniteInterfaces
import DistributedSynthesis.Formalizations.PeriodicBlocks.RelationalHandovers

/-! Alternative fixed-block compression argument.

`periodic_block_compression` gives uniform positive block length and retained
width directly from the old common-view theorem. It proves local implementability
of the fold and exact objective replay. `strategy_compressed_threads_accept`
proves global parity under repeated folds. `compressed_handover_monitor_accepts`
connects these chains to the existing finite universal-thread monitor.

The complete game equivalence is proved in `Reduction.lean` and specialized
to the original LTL model in `LTL.lean`. The old synthesis proof and its entry
points are unchanged.
-/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

/-- Uniform fixed-block compression of a live ending component. The source
family can have arbitrary cardinality. The finite bound applies to retained
endpoints, not to the original component. The witness suffix for each source
only establishes that its root participates in the same ending component. -/
theorem periodic_block_compression {I₁ I₂ O₁ O₂ G Q : Type}
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂] [Finite G] [Finite Q]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ D B : Nat, 0 < D ∧
      ∀ (R : Type) (σ : StrategyPair I₁ I₂ O₁ O₂)
        (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
        (winning : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
          NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
        (K : Nat) (root : R → EnvHistory I₁ I₂), Function.Injective root →
        ∀ (graphState : R → G)
          (member : R → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Bool)
          (anchor : EnvHistory I₁ I₂), LivePrefix A (History.graphSequence anchor) →
          ∀ witness : R → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D,
            (∀ i, InputConnected (LivePrefix A) anchor (root i ++ (witness i).val)) →
            let key := strategyBlockType σ D root graphState
              (fun i => strategyHistoryLabel σ step q₀ (root i)) member
            let rank := fun i => treeRank (fun h => χ (strategyHistoryLabel σ step q₀ h)) winning K (root i)
            let replace := representative key rank
            ValidFold key replace ∧
            Finite (RetainedEndpoints key rank) ∧ Nat.card (RetainedEndpoints key rank) ≤ B ∧
            (∃ localMap : (p : Proc) → View I₁ I₂ p → View I₁ I₂ p,
              ∀ p i (z : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D),
                localMap p (currentView p (root i ++ z.val)) =
                  currentView p (root (replace i) ++ z.val)) ∧
            (∀ i (u : EnvHistory I₁ I₂), List.length u ≤ D →
              strategyHistoryLabel σ step q₀ (root (replace i) ++ u) =
                strategyHistoryLabel σ step q₀ (root i ++ u)) ∧
            ∀ i, rank (replace i) ≤ rank i := by
  obtain ⟨D, positive, commonRoots⟩ := holes_block_common_root (I₁ := I₁) (I₂ := I₂) A regular holes
  refine ⟨D, compressionBound I₁ I₂ O₁ O₂ G Q D, positive, ?_⟩
  intro R σ step q₀ χ winning K root injective graphState member anchor live witness connected
  obtain ⟨leader, common⟩ := commonRoots R anchor live root (fun i => (witness i).val)
    (fun i => (witness i).property) connected
  dsimp only
  let key := strategyBlockType σ D root graphState (fun i => strategyHistoryLabel σ step q₀ (root i)) member
  let rank i := treeRank (fun h => χ (strategyHistoryLabel σ step q₀ h)) winning K (root i)
  obtain ⟨finite, bound⟩ := retained_endpoint_bound key rank
  refine ⟨⟨representative_key key rank, fun _ _ eq => representative_eq key rank eq⟩,
    finite, bound, ?_, ?_, representative_rank key rank⟩
  · exact representative_local_maps key rank root injective leader common D
      (fun z : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D => z.val) (fun z => z.property)
  · intro i u within
    exact strategyRepresentative_replay σ step q₀ χ winning K D root graphState member i u within

end
end Characterisation.PeriodicBlocks
