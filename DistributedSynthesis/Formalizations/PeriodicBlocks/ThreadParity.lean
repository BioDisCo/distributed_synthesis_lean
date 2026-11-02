/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.Compression

/-! Every compatible thread through rank-minimal block compressions accepts.
The source families may change at every block. A thread need not lift to one
branch of the original strategy, which is why the rank argument is needed. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

theorem folded_suffixes_parity {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E, NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (K : Nat) (root chosen suffix : Nat → List E) (color : Nat → Fin (K+1))
    (replace : ∀ n, treeRank priority winning K (chosen n) ≤ treeRank priority winning K (root n))
    (next : ∀ n, root (n+1) = chosen n ++ suffix n)
    (positive : ∀ n, 0 < (suffix n).length)
    (minima : ∀ n, (color n).val = blockMinimum priority (chosen n) (suffix n)) :
    NatSeqMinEvenParity (fun n => (color n).val) := by
  apply folded_blocks_parity priority winning K root chosen color replace
  · intro n
    exact ⟨suffix n, (next n).symm⟩
  · intro n
    rw [next, List.length_append]
    have := positive n
    omega
  · intro n t lo hi
    have length : (root (n+1)).length = (chosen n).length + (suffix n).length := by
      rw [next, List.length_append]
    rw [next, List.take_append, List.take_of_length_le lo, minima]
    exact blockMinimum_le priority _ _ _ (by omega)
  · intro n
    obtain ⟨k, inside, eq⟩ := blockMinimum_attained priority (chosen n) (suffix n) (positive n)
    refine ⟨(chosen n).length+k, by omega, ?_, ?_⟩
    · rw [next, List.length_append]
      omega
    · rw [next, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
        minima, eq]

/-- Acceptance is preserved along every chain of representatives. The
representatives are those constructed from the original strategy, including
its full finite block rule. No parity-preservation premise is required. -/
theorem strategy_compressed_threads_accept {I₁ I₂ O₁ O₂ G Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
    (winning : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
      NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
    (K D : Nat) (positive : 0 < D) (bounded : ∀ q, χ q ≤ K)
    (R : Nat → Type) (family : (n : Nat) → R n → EnvHistory I₁ I₂)
    (graphState : (n : Nat) → R n → G)
    (member : (n : Nat) → R n → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Bool)
    (thread : (n : Nat) → R n)
    (suffix : Nat → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (next : ∀ n, family (n+1) (thread (n+1)) =
      family n (strategyRepresentative σ step q₀ χ winning K D (family n) (graphState n)
        (member n) (thread n)) ++ (suffix n).val) :
    NatSeqMinEvenParity (fun n =>
      blockMinimum (fun h => χ (strategyHistoryLabel σ step q₀ h))
        (family n (thread n)) (suffix n).val) := by
  let priority h := χ (strategyHistoryLabel σ step q₀ h)
  let root n := family n (thread n)
  let chosen n := family n (strategyRepresentative σ step q₀ χ winning K D
    (family n) (graphState n) (member n) (thread n))
  have pos : ∀ n, 0 < (suffix n).val.length := fun n => by rw [(suffix n).property]; exact positive
  have bound : ∀ n, blockMinimum priority (root n) (suffix n).val ≤ K := by
    intro n
    have le := blockMinimum_le priority (root n) (suffix n).val 0 (pos n)
    simpa only [List.take_zero, List.append_nil] using le_trans le (bounded _)
  let color n : Fin (K+1) := ⟨blockMinimum priority (root n) (suffix n).val, Nat.lt_succ_of_le (bound n)⟩
  apply folded_suffixes_parity priority winning K root chosen (fun n => (suffix n).val) color
  · intro n
    exact representative_rank
      (strategyBlockType σ D (family n) (graphState n)
        (fun i => strategyHistoryLabel σ step q₀ (family n i)) (member n))
      (fun i => treeRank priority winning K (family n i)) (thread n)
  · exact next
  · exact pos
  · intro n
    exact (strategyRepresentative_minimum σ step q₀ χ winning K D (family n)
      (graphState n) (member n) (thread n) (suffix n).val (Nat.le_of_eq (suffix n).property)).symm

end
end Characterisation.PeriodicBlocks
