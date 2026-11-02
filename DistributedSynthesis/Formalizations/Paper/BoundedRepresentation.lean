/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.BoundedRepresentation

/-!
# Uncompressed and compressed trees

Manuscript source label: `thm:tree-bounded-representation`.

## Paper statement

An accepting uncompressed component tree exists if and only if an accepting
  compressed component tree exists.
From an effectively given accepting compressed tree, one can effectively
  construct an accepting uncompressed tree.

## Correspondence

The endpoint uses the constructed block automaton, so liveness correctness is proved by
the library rather than assumed here. The remaining consensus premise is the standing
hypothesis in the paper.

## Reading the proof

See the [proof locations](PROOFS.md#uncompressed-and-compressed-trees) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.BoundedRepresentation

/-- Reuses `Characterisation.ComponentTrees.block_bounded_representation`. -/
theorem block_bounded_representation :
    ∀ {I₁ I₂ O₁ O₂ G V : Type} {D : ℕ} [inst : Fintype I₁]
      [inst_1 : Fintype I₂] [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] [Nonempty I₁] [Nonempty I₂] [Nontrivial V]
      (M : Recognizer Graph G) [inst_7 : DecidablePred fun (x : G) => x ∈ M.accept] (A : Set (ℕ → Graph)),
      (∀ (h : List Graph), LivePrefix A h ↔ M.eval h ∈ M.accept) →
        0 < D →
          (∀ (u : List Graph),
              LivePrefix A u →
                ∃ (σ : StrategyPair V V (Option V) (Option V)), ComponentGames.Consensus.SolvesBy σ (Residual A u) D) →
            ∀ [inst_8 : Fintype G] (specification : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂)),
              (∃ (original :
                  ComponentTrees.UncompressedTree
                    (ComponentTrees.blockAutomaton (ComponentTrees.jointRecognizer M) specification D) M),
                  original.Accepting) ↔
                ∃ (compressed :
                  ComponentTrees.CompressedTree
                    (ComponentTrees.blockAutomaton (ComponentTrees.jointRecognizer M) specification D) M
                    (ComponentTrees.reductionBound
                      (ComponentTrees.blockAutomaton (ComponentTrees.jointRecognizer M) specification D))),
                  compressed.Accepting :=
  @_root_.Characterisation.ComponentTrees.block_bounded_representation

end DistributedSynthesis.Paper.BoundedRepresentation
