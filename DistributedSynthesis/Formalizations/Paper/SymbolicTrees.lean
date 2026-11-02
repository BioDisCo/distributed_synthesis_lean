/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingDecode
import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingEncode

/-!
# Compressed and symbolic trees

Manuscript source label: `lem:tree-symbolic-equivalence`.

## Paper statement

An accepting compressed component tree exists if and only if an accepting
  symbolic component tree exists.
From an effectively given accepting symbolic component tree, one can
  effectively construct an accepting compressed component tree.

## Correspondence

GeneratingAlphabet stores the incoming generating table at the child. The finite orders and capacities implement the paper's chosen
finite representatives and bound b. liveCorrect identifies liveness with the prefix
recognizer; the constructed block automaton supplies this fact.

## Reading the proof

See the [proof locations](PROOFS.md#compressed-and-symbolic-trees) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.SymbolicTrees

/-- Reuses `Characterisation.ComponentTrees.GeneratingAlphabet.model_tree_iff`. -/
theorem model_tree_iff :
    ∀ {I₁ I₂ O₁ O₂ G : Type} {D capacity : ℕ} [inst : Fintype I₁]
      [inst_1 : Fintype I₂] [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] [Fintype O₁] [Fintype O₂]
      [inst_6 : DecidableEq O₁] [inst_7 : DecidableEq O₂] [inst_8 : LinearOrder I₁] [inst_9 : LinearOrder I₂]
      [inst_10 : LinearOrder O₁] [inst_11 : LinearOrder O₂]
      (B : DetParityAutomaton (PeriodicBlocks.BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D)) [inst_12 : LinearOrder B.State]
      (live : B.State → Bool) (bound : ℕ) (positive : 0 < capacity),
      bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity →
        ∀ (M : Recognizer Graph G) [inst_13 : DecidablePred fun (x : G) => x ∈ M.accept],
          (∀ (h : EnvHistory I₁ I₂) (q : B.State),
              ComponentTrees.StateReachable B h q → (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept)) →
            M.eval [] ∈ M.accept →
              ((∃ (code : LabeledTree (Fin capacity) (ComponentTrees.GeneratingAlphabet.Letter B live bound positive)),
                  ComponentTrees.GeneratingAlphabet.Accepting B live bound positive code) ↔
                ∃ (tree : ComponentTrees.CompressedTree B M bound), tree.Accepting) :=
  @_root_.Characterisation.ComponentTrees.GeneratingAlphabet.model_tree_iff

/-- Reuses `Characterisation.ComponentTrees.GeneratingAlphabet.decode_accepting`. -/
theorem decode_accepting :
    ∀ {I₁ I₂ O₁ O₂ G : Type} {D capacity : ℕ} [inst : Fintype I₁]
      [inst_1 : Fintype I₂] [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] [inst_4 : Fintype O₁] [inst_5 : Fintype O₂]
      [inst_6 : DecidableEq O₁] [inst_7 : DecidableEq O₂] [inst_8 : LinearOrder I₁] [inst_9 : LinearOrder I₂]
      [inst_10 : LinearOrder O₁] [inst_11 : LinearOrder O₂]
      (B : DetParityAutomaton (PeriodicBlocks.BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D)) [inst_12 : LinearOrder B.State]
      (live : B.State → Bool) (bound : ℕ) (positive : 0 < capacity) (M : Recognizer Graph G)
      [inst_13 : DecidablePred fun (x : G) => x ∈ M.accept]
      (liveCorrect :
        ∀ (h : EnvHistory I₁ I₂) (q : B.State),
          ComponentTrees.StateReachable B h q → (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
      (initialLive : M.eval [] ∈ M.accept)
      (code : LabeledTree (Fin capacity) (ComponentTrees.GeneratingAlphabet.Letter B live bound positive))
      (accepted : ComponentTrees.GeneratingAlphabet.Accepting B live bound positive code),
      (ComponentTrees.GeneratingAlphabet.decode B live bound positive M liveCorrect initialLive code
          accepted.left).Accepting :=
  @_root_.Characterisation.ComponentTrees.GeneratingAlphabet.decode_accepting

end DistributedSynthesis.Paper.SymbolicTrees
