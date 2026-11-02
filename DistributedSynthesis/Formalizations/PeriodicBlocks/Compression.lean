/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockReplay
import DistributedSynthesis.Formalizations.PeriodicBlocks.LexicographicProgress

/-! Concrete rank-minimal compression of one fixed-length block. The bound
depends on the alphabets, automaton states and block length, not on the round,
the strategy, or the size of the input-dependent component. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

abbrev StrategyBlockType (I₁ I₂ O₁ O₂ G Q : Type) (D : Nat) :=
  BlockType G Q (BlockPrefix (RoundRecord I₁ I₂ Graph Unit Unit) D) (O₁ × O₂)
    (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)

def compressionBound (I₁ I₂ O₁ O₂ G Q : Type) (D : Nat) : Nat :=
  Nat.card (StrategyBlockType I₁ I₂ O₁ O₂ G Q D) *
    Nat.card (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)

section Strategy
variable {I₁ I₂ O₁ O₂ G Q R : Type}
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
variable (winning : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
  NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
variable (K D : Nat) (root : R → EnvHistory I₁ I₂) (graphState : R → G)
variable (member : R → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Bool)

def strategyRepresentative : R → R :=
  representative
    (strategyBlockType σ D root graphState (fun i => strategyHistoryLabel σ step q₀ (root i)) member)
    (fun i => treeRank (fun h => χ (strategyHistoryLabel σ step q₀ h)) winning K (root i))

theorem strategyRepresentative_type (i : R) :
    strategyBlockType σ D root graphState (fun i => strategyHistoryLabel σ step q₀ (root i)) member
      (strategyRepresentative σ step q₀ χ winning K D root graphState member i) =
    strategyBlockType σ D root graphState (fun i => strategyHistoryLabel σ step q₀ (root i)) member i :=
  representative_key _ _ i

theorem strategyRepresentative_replay (i : R) (u : EnvHistory I₁ I₂)
    (bound : List.length u ≤ D) :
    strategyHistoryLabel σ step q₀
      (root (strategyRepresentative σ step q₀ χ winning K D root graphState member i) ++ u) =
    strategyHistoryLabel σ step q₀ (root i ++ u) := by
  have same := strategyRepresentative_type σ step q₀ χ winning K D root graphState member i
  apply strategy_block_replay σ step q₀ D _ _
    (congrArg BlockType.objectiveState same) (congrArg BlockType.rule same) u bound

/-- All obligations for a single component fold are conclusions: type and
suffix-set preservation, retraction, a uniform size bound, rank nonincrease,
and preservation of local-view equality. Monitor replay is proved above. -/
theorem strategy_block_compression
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂] [Finite G] [Finite Q]
    (injective : Function.Injective root) (leader : Proc)
    (common : ∀ i j, currentView leader (root i) = currentView leader (root j)) :
    ∃ replace : R → R,
      (∀ i, strategyBlockType σ D root graphState
          (fun i => strategyHistoryLabel σ step q₀ (root i)) member (replace i) =
        strategyBlockType σ D root graphState
          (fun i => strategyHistoryLabel σ step q₀ (root i)) member i) ∧
      (∀ i, replace (replace i) = replace i) ∧
      (Finite {x : R × BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D // replace x.1 = x.1}) ∧
      (Nat.card {x : R × BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D // replace x.1 = x.1} ≤
        compressionBound I₁ I₂ O₁ O₂ G Q D) ∧
      (∀ i, treeRank (fun h => χ (strategyHistoryLabel σ step q₀ h)) winning K (root (replace i)) ≤
        treeRank (fun h => χ (strategyHistoryLabel σ step q₀ h)) winning K (root i)) ∧
      (∀ i j (u v : EnvHistory I₁ I₂), List.length u = List.length v → ∀ p,
        currentView p (root i ++ u) = currentView p (root j ++ v) →
        currentView p (root (replace i) ++ u) = currentView p (root (replace j) ++ v)) := by
  let key := strategyBlockType σ D root graphState
    (fun i => strategyHistoryLabel σ step q₀ (root i)) member
  let rank i := treeRank (fun h => χ (strategyHistoryLabel σ step q₀ h)) winning K (root i)
  obtain ⟨finite, bound⟩ := endpoint_bound (Z := BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) key rank
  refine ⟨representative key rank, representative_key key rank,
    representative_idempotent key rank, finite, bound, representative_rank key rank, ?_⟩
  intro i j u v lengths p same
  exact representative_views key rank root injective leader common i j u v lengths p same

end Strategy

/-- Source-inclusive minimum of a nonempty block. The source is included
and the endpoint excluded, so successive blocks partition all priorities. -/
def blockMinimum {E : Type} (priority : List E → Nat) (h u : List E) : Nat :=
  rangeMin (fun k => priority (h ++ u.take k)) 0 (u.length-1)

theorem blockMinimum_le {E : Type} (priority : List E → Nat) (h u : List E)
    (k : Nat) (inside : k < u.length) :
    blockMinimum priority h u ≤ priority (h ++ u.take k) := by
  simpa only [Nat.zero_add] using
    rangeMin_le (fun k => priority (h ++ u.take k)) 0 (u.length-1) k (by omega)

theorem blockMinimum_attained {E : Type} (priority : List E → Nat) (h u : List E)
    (positive : 0 < u.length) :
    ∃ k, k < u.length ∧ blockMinimum priority h u = priority (h ++ u.take k) := by
  obtain ⟨k, bound, eq⟩ := rangeMin_attained (fun k => priority (h ++ u.take k)) 0 (u.length-1)
  exact ⟨k, by omega, by simpa only [Nat.zero_add] using eq⟩

/-- Exact replay implies equality of the complete block minima. -/
theorem strategyRepresentative_minimum {I₁ I₂ O₁ O₂ G Q R : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
    (winning : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
      NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
    (K D : Nat) (root : R → EnvHistory I₁ I₂) (graphState : R → G)
    (member : R → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Bool)
    (i : R) (u : EnvHistory I₁ I₂) (bound : List.length u ≤ D) :
    blockMinimum (fun h => χ (strategyHistoryLabel σ step q₀ h))
      (root (strategyRepresentative σ step q₀ χ winning K D root graphState member i)) u =
    blockMinimum (fun h => χ (strategyHistoryLabel σ step q₀ h)) (root i) u := by
  apply rangeMin_congr
  intro k _
  apply congrArg χ
  apply strategyRepresentative_replay σ step q₀ χ winning K D root graphState member
  simp only [List.length_take]
  exact le_trans (Nat.min_le_right _ _) bound

end
end Characterisation.PeriodicBlocks
