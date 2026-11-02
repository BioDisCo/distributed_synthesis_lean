/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ForwardTree

/-! The complete bounded-representation equivalence in main.tex.
The concrete product-automaton endpoint discharges the liveness interface.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G V : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Nonempty I₁] [Nonempty I₂] [Nontrivial V]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (A : Set (Nat → Graph))
variable (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
variable (positive : 0 < D)
variable (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
  Consensus.SolvesBy σ (Residual A u) D)

include recognizes positive consensus in
theorem uncompressed_to_compressed (original : UncompressedTree B M) (accepting : original.Accepting) :
    ∃ compressed : CompressedTree B M (reductionBound B), compressed.Accepting :=
  ⟨_, ForwardConstruction.tree_accepting B M A recognizes positive consensus original accepting⟩

include recognizes positive consensus in
/-- The generic form states precisely what the block automaton must know
about liveness. The concrete endpoint below proves that premise. -/
theorem bounded_representation (liveness : StateLiveness B M) :
    (∃ original : UncompressedTree B M, original.Accepting) ↔
      ∃ compressed : CompressedTree B M (reductionBound B), compressed.Accepting := by
  constructor
  · rintro ⟨original, accepting⟩
    exact uncompressed_to_compressed B M A recognizes positive consensus original accepting
  · rintro ⟨compressed, accepting⟩
    exact compressed_to_uncompressed B M liveness compressed accepting

include recognizes positive consensus in
/-- `thm:tree-bounded-representation`, for the paper's constructed automaton.
No liveness, coverage, rank, subset, or simulation certificate is an extra
assumption. The standing repeated-consensus premise is the one in main.tex. -/
theorem block_bounded_representation [Fintype G]
    (specification : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂)) :
    (∃ original : UncompressedTree (blockAutomaton (jointRecognizer M) specification D) M,
      original.Accepting) ↔
    ∃ compressed : CompressedTree (blockAutomaton (jointRecognizer M) specification D) M
        (reductionBound (blockAutomaton (jointRecognizer M) specification D)), compressed.Accepting :=
  bounded_representation _ M A recognizes positive consensus (blockAutomaton_stateLiveness M specification)

/-- The full-position bound b = Ba holds at EVERY supported node, including
its singleton root. It is distinct from the reduction-image bound B. -/
theorem CompressedTree.position_bound {bound : Nat} (positiveBound : 0 < bound)
    (tree : CompressedTree B M bound) (valid : tree.Valid)
    (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport CompressedNode.offers tree node = true) :
    (tree node).position.histories.card ≤ bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  cases node using List.reverseRecOn with
  | nil =>
    rw [valid [] supported]
    change 1 ≤ _
    letI : Nonempty (RoundRecord I₁ I₂ Graph Unit Unit) :=
      ⟨⟨Classical.arbitrary I₁, Classical.arbitrary I₂, .both, (), ()⟩⟩
    exact Nat.mul_pos positiveBound (Nat.pow_pos Nat.card_pos)
  | append_singleton node P =>
    have both : publicSupport CompressedNode.offers tree node = true ∧
        CompressedNode.offers (tree node) P = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    have next : (tree node).Successor P := of_decide_eq_true both.2
    have source : (tree (node ++ [P])).position = P := by simpa [observableAt] using valid _ supported
    rw [source]
    exact (tree node).successor_bound P next

end
end Characterisation.ComponentTrees
