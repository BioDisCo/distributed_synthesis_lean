/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.EdgeProgress
import DistributedSynthesis.Formalizations.ComponentTrees.Compression

/-! Rank-minimal endpoint-table representatives. This is the compatible-run
part of the forward bounded-representation proof, with the source families
allowed to vary at every step. No full-rule equality, finite-memory bound,
or acceptance-preservation hypothesis is imposed on the representatives.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1500000

variable {E Q : Type}
variable (live : List E → Prop) (priority : List E → Nat)
variable (closed : ∀ h k, h.IsPrefix k → live k → live h)
variable (winning : ∀ word : Nat → E, (∀ n, live (branchNode word n)) →
  NatSeqMinEvenParity (fun n => priority (branchNode word n)))

/-- Every compatible run formed by the draft's table-minimization accepts.

`E` is the complete-block alphabet; `family n` names participating prefixes
of the selected component. `table n h u = some q` says that `hu` belongs to
that component and has block successor state `q`. `sound` is exactly the
subset/label invariant maintained against the original uncompressed tree.
It does not assume that folded runs already accept. -/
theorem rank_minimal_tables_accept
    (χ : Q → Nat) (K : Nat) (bounded : ∀ q, χ q ≤ K)
    (R : Nat → Type) (family : (n : Nat) → R n → List E)
    (table : (n : Nat) → R n → E → Option Q)
    (sound : ∀ n h u q, table n h u = some q →
      live (family n h ++ [u]) ∧ priority (family n h ++ [u]) = χ q)
    (thread : (n : Nat) → R n) (suffix : Nat → E) (state : Nat → Q)
    (member : ∀ n, table n (thread n) (suffix n) = some (state n))
    (next : ∀ n, family (n+1) (thread (n+1)) =
      family n (representative (table n)
        (fun h => edgeRank live priority closed winning K (family n h)) (thread n)) ++ [suffix n]) :
    NatSeqMinEvenParity (fun n => χ (state n)) := by
  let rank n h := edgeRank live priority closed winning K (family n h)
  let rep n := representative (table n) (rank n)
  let root n := family n (thread n)
  let chosen n := family n (rep n (thread n))
  let color (n : Nat) : Fin (K+1) := ⟨χ (state n), Nat.lt_succ_of_le (bounded _)⟩
  have key n : table n (rep n (thread n)) = table n (thread n) :=
    representative_key (table n) (rank n) (thread n)
  have folded n : table n (rep n (thread n)) (suffix n) = some (state n) := by
    rw [key n, member n]
  have actual n : live (root (n+1)) ∧ priority (root (n+1)) = χ (state n) := by
    change live (family (n+1) (thread (n+1))) ∧
      priority (family (n+1) (thread (n+1))) = χ (state n)
    rw [next n]
    exact sound n _ _ _ (folded n)
  exact folded_edges_parity live priority closed winning K root chosen suffix color
    (fun n => representative_rank (table n) (rank n) (thread n)) next
    (fun n => (actual n).1) (fun n => (actual n).2)

/-- The conclusion in the draft's indexing: parity of `q_n(h_n)`, including
the initial state. The finite priority bound is computed from `Q`, not an
extra hypothesis. The entries of table `n` label state `n+1`, not state `n`.
-/
theorem rank_minimal_state_sequence_accept [Fintype Q]
    (χ : Q → Nat)
    (R : Nat → Type) (family : (n : Nat) → R n → List E)
    (table : (n : Nat) → R n → E → Option Q)
    (sound : ∀ n h u q, table n h u = some q →
      live (family n h ++ [u]) ∧ priority (family n h ++ [u]) = χ q)
    (thread : (n : Nat) → R n) (suffix : Nat → E) (state : Nat → Q)
    (member : ∀ n, table n (thread n) (suffix n) = some (state (n+1)))
    (next : ∀ n, family (n+1) (thread (n+1)) =
      family n (representative (table n)
        (fun h => edgeRank live priority closed winning (Finset.univ.sup χ) (family n h))
        (thread n)) ++ [suffix n]) :
    NatSeqMinEvenParity (fun n => χ (state n)) := by
  have tail := rank_minimal_tables_accept live priority closed winning χ (Finset.univ.sup χ)
    (fun q => Finset.le_sup (f := χ) (Finset.mem_univ q)) R family table sound thread suffix
    (fun n => state (n+1)) member next
  apply (natSeqMinEvenParity_shift (fun n => χ (state n)) 1).mp
  simpa only [Nat.add_comm] using tail

/-- The current manuscript's indexing: e_(n+1) = r_n(e_n)u_n.
The ordinal progress is measured on r_n(e_n), not on the unreduced e_n.
`nextReduction` is the table-representative equation for the NEXT node's
reduction. The original-tree subset/label invariant remains explicit in
`sound`; the recursive tree construction must establish it. -/
theorem rank_minimal_reduced_edges_accept [Fintype Q]
    (χ : Q → Nat)
    (R : Nat → Type) (family : (n : Nat) → R n → List E)
    (table : (n : Nat) → R n → E → Option Q)
    (sound : ∀ n h u q, table n h u = some q →
      live (family n h ++ [u]) ∧ priority (family n h ++ [u]) = χ q)
    (edge : Nat → List E) (reduce : Nat → List E → List E)
    (thread : (n : Nat) → R n) (suffix : Nat → E) (state : Nat → Q)
    (reduced : ∀ n, family n (thread n) = reduce n (edge n))
    (step : ∀ n, edge (n+1) = reduce n (edge n) ++ [suffix n])
    (member : ∀ n, table n (thread n) (suffix n) = some (state (n+1)))
    (nextReduction : ∀ n, reduce (n+1) (family n (thread n) ++ [suffix n]) =
      family n (representative (table n)
        (fun h => edgeRank live priority closed winning (Finset.univ.sup χ) (family n h))
        (thread n)) ++ [suffix n]) :
    NatSeqMinEvenParity (fun n => χ (state n)) := by
  apply rank_minimal_state_sequence_accept live priority closed winning χ
    R family table sound thread suffix state member
  intro n
  rw [reduced (n+1), step n, ← reduced n]
  exact nextReduction n

end
end Characterisation.ComponentTrees
