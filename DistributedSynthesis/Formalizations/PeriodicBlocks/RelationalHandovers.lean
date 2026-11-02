/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.ThreadParity

/-! Finite handovers for compressed blocks. A retained endpoint can have
several source roots, so the predecessor data is a relation. The existing
universal-thread monitor works for this relation without modification. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

/-- A finite relation of source and target slots, with a block minimum for
each possible link. Slots not used in a component have no incident links. -/
structure RelationalHandover (B K : Nat) where
  parent : Fin (B+1) → Fin (B+1) → Bool
  minimum : Fin (B+1) → Fin (B+1) → Fin (K+1)
  deriving Fintype, DecidableEq

def RelationalHandover.edge {B K : Nat} (old : HandoverCode B K)
    (move : RelationalHandover B K) (_ : Unit) (next : HandoverCode B K) : Prop :=
  move.parent old.1 next.1 = true ∧ next.2 = move.minimum old.1 next.1

noncomputable def relationalProgressSystem {B K : Nat} (initial : HandoverCode B K) :
    FiniteThreadSystem.{0,0,0} (RelationalHandover B K × Unit) :=
  hiddenCodeContinuitySystem (handoverPriorityDPA B K) initial RelationalHandover.edge

/-- The finite monitor accepts exactly when every compatible predecessor
chain has even least recurrent block minimum. Parent uniqueness is not used. -/
theorem relationalProgress_accepts_iff {B K : Nat} (initial : HandoverCode B K)
    (word : Nat → RelationalHandover B K × Unit) :
    (relationalProgressSystem initial).universalRunDPA.Accepts word ↔
      ∀ thread : HiddenCodeContinuityThread initial RelationalHandover.edge word,
        NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  rw [relationalProgressSystem, hiddenCodeContinuitySystem_universalRunDPA_accepts_iff]
  simp only [handoverPriorityDPA_accepts_iff, HiddenCodeContinuityThread.childCodeWord]

/-- The new compressed-block parity theorem discharges the monitor's
universal-thread condition for a concrete sequence of representative families. -/
theorem compressed_handover_monitor_accepts {I₁ I₂ O₁ O₂ G Q : Type} {B K D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
    (winning : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
      NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
    (positive : 0 < D) (bounded : ∀ q, χ q ≤ K)
    (family : Nat → Fin (B+1) → EnvHistory I₁ I₂)
    (graphState : Nat → Fin (B+1) → G)
    (member : Nat → Fin (B+1) → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Bool)
    (word : Nat → RelationalHandover B K × Unit)
    (links : ∀ n i j, (word n).1.parent i j = true →
      ∃ u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D,
        family (n+1) j = family n (strategyRepresentative σ step q₀ χ winning K D
          (family n) (graphState n) (member n) i) ++ u.val ∧
        ((word n).1.minimum i j).val =
          blockMinimum (fun h => χ (strategyHistoryLabel σ step q₀ h)) (family n i) u.val)
    (initial : HandoverCode B K) :
    (relationalProgressSystem initial).universalRunDPA.Accepts word := by
  classical
  rw [relationalProgress_accepts_iff]
  intro thread
  have witnesses := fun n => links n (thread.code n).1 (thread.code (n+1)).1 (thread.edge n).1
  choose suffix next minima using witnesses
  have parity := strategy_compressed_threads_accept σ step q₀ χ winning K D positive bounded
    (fun _ => Fin (B+1)) family graphState member (fun n => (thread.code n).1) suffix next
  have eq : (fun n => (thread.code (n+1)).2.val) =
      (fun n => blockMinimum (fun h => χ (strategyHistoryLabel σ step q₀ h))
        (family n (thread.code n).1) (suffix n).val) := by
    funext n
    exact (congrArg Fin.val (thread.edge n).2).trans (minima n)
  rwa [eq]

end Characterisation.PeriodicBlocks
