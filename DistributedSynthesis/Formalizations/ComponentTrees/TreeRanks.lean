/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.TreeCoverage
import DistributedSynthesis.Formalizations.ComponentTrees.BlockHistories
import DistributedSynthesis.Formalizations.ComponentTrees.EdgeProgress

/-! The ranks of the original uncompressed tree. Coverage, unique labels,
and acceptance of every live block path are proved, not input certificates.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G)

def liveBlocks (words : List (BlockInput I₁ I₂ D)) : Prop :=
  M.eval (History.graphSequence (blockHistory words)) ∈ M.accept

theorem liveBlocks_closed (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (h k : List (BlockInput I₁ I₂ D)) (pref : h.IsPrefix k) (live : liveBlocks M k) :
    liveBlocks M h := by
  obtain ⟨tail, eq⟩ := pref
  apply (recognizes _).mp
  have alive := (recognizes _).mpr live
  rw [← eq] at alive
  simp only [blockHistory, List.flatMap_append, History.graphSequence, List.map_append] at alive
  exact livePrefix_closed A _ _ alive

variable [DecidablePred (· ∈ M.accept)]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
namespace UncompressedTree
variable {B M} (tree : UncompressedTree B M)

/-- q_U(e) is the actual label at any node containing e. -/
theorem stateOf_history (valid : tree.Valid) (positive : 0 < D)
    (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport UncompressedNode.offers tree node = true)
    (h : (tree node).position.Root) :
    tree.stateOf (historyBlocks D h.val) = (tree node).position.state h := by
  have length := (tree node).position.lengths _ h.property
  have eq := blockHistory_historyBlocks _ h.val length
  let occurrence : tree.Occurrence (historyBlocks D h.val) :=
    ⟨node, supported, (position_phase tree valid node supported).symm.trans
      (historyBlocks_length positive _ h.val length).symm,
      by rw [eq]; exact h.property⟩
  have states := stateOf_eq tree valid occurrence
  exact states.trans (congrArg (tree node).position.state (Subtype.ext eq))

variable (accepting : tree.Accepting) (A : Set (Nat → Graph))
variable (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)

def rank (h : EnvHistory I₁ I₂) : Lex (Fin (Finset.univ.sup B.priority + 1) → Ordinal) :=
  edgeRank (liveBlocks M) (fun words => B.priority (tree.stateOf words))
    (liveBlocks_closed M A recognizes)
    (stateOf_accepts tree accepting.1 accepting A recognizes)
    (Finset.univ.sup B.priority) (historyBlocks D h)

/-- The paper's final ordinal argument, with the original-tree acceptance
and original state assignments supplied by the tree itself. -/
theorem reduced_paths_accept (positive : 0 < D)
    (root chosen : Nat → EnvHistory I₁ I₂) (word : Nat → BlockInput I₁ I₂ D)
    (state : Nat → B.State)
    (lengths : ∀ n, List.length (chosen n) = n*D)
    (replace : ∀ n, tree.rank accepting A recognizes (chosen n) ≤ tree.rank accepting A recognizes (root n))
    (next : ∀ n, root (n+1) = chosen n ++ (word n).val)
    (alive : ∀ n, M.eval (History.graphSequence (root (n+1))) ∈ M.accept)
    (labels : ∀ n, tree.stateOf (historyBlocks D (root (n+1))) = state (n+1)) :
    NatSeqMinEvenParity (fun n => B.priority (state n)) := by
  let color n : Fin (Finset.univ.sup B.priority + 1) :=
    ⟨B.priority (state (n+1)), Nat.lt_succ_of_le (Finset.le_sup (f := B.priority) (Finset.mem_univ _))⟩
  have paths := folded_edges_parity (liveBlocks M) (fun words => B.priority (tree.stateOf words))
    (liveBlocks_closed M A recognizes) (stateOf_accepts tree accepting.1 accepting A recognizes)
    (Finset.univ.sup B.priority) (fun n => historyBlocks D (root n))
    (fun n => historyBlocks D (chosen n)) word color replace
    (by intro n; dsimp only; rw [next, historyBlocks_append positive n _ (lengths n)])
    (by
      intro n
      unfold liveBlocks
      have length : List.length (root (n+1)) = (n+1)*D := by
        rw [next, List.length_append, lengths, (word n).property, Nat.add_mul, Nat.one_mul]
      rw [blockHistory_historyBlocks (n+1) _ length]
      exact alive n)
    (by intro n; exact congrArg B.priority (labels n))
  apply (natSeqMinEvenParity_shift (fun n => B.priority (state n)) 1).mp
  simpa only [Nat.add_comm] using paths

end UncompressedTree
end
end Characterisation.ComponentTrees
