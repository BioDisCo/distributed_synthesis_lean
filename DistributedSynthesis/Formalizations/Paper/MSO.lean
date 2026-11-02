/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingAlphabet
import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingEncode

/-!
# MSO defines the accepting symbolic trees

Manuscript source label: `lem:tree-mso`.

## Paper statement

One can construct an MSO formula $\operatorname{Acc}(\mathbf X)$ over the
  full $b$-ary tree whose models are exactly the accepting symbolic
  component trees.

## Correspondence

The sentence uses the current child-owned incoming generating tables and quantifies over
all compatible runs. sentence_correct is the language equivalence; mso_compressed_iff
connects it to concrete trees; satisfiable_correct checks the executable decision
procedure.

## Reading the proof

`sentence_correct` connects MSO satisfaction to the local table conditions and
acceptance of all compatible runs. `mso_compressed_iff` then uses the encoding
and decoding of compressed trees. `satisfiable_correct` adds the executable
MSO satisfiability procedure to this equivalence.

See the [proof locations](PROOFS.md#mso-defines-the-accepting-symbolic-trees-defines-the-accepting-symbolic-trees-defines-the-accepting-symbolic-trees) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.MSO

/-- Reuses `Characterisation.ComponentTrees.GeneratingAlphabet.sentence_correct`. -/
theorem sentence_correct :
    ∀ {I₁ I₂ O₁ O₂ : Type} {D capacity : ℕ} [inst : Fintype I₁]
      [inst_1 : Fintype I₂] [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] [inst_4 : Fintype O₁] [inst_5 : Fintype O₂]
      [inst_6 : DecidableEq O₁] [inst_7 : DecidableEq O₂] [inst_8 : LinearOrder I₁] [inst_9 : LinearOrder I₂]
      [inst_10 : LinearOrder O₁] [inst_11 : LinearOrder O₂]
      (B : DetParityAutomaton (PeriodicBlocks.BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D)) [inst_12 : LinearOrder B.State]
      (live : B.State → Bool) (bound : ℕ) (positive : 0 < capacity)
      (tree : LabeledTree (Fin capacity) (ComponentTrees.GeneratingAlphabet.Letter B live bound positive)),
      MSO.Tree.Satisfies tree (ComponentTrees.GeneratingAlphabet.sentence B live bound positive) ↔
        ComponentTrees.GeneratingAlphabet.Accepting B live bound positive tree :=
  @_root_.Characterisation.ComponentTrees.GeneratingAlphabet.sentence_correct

/-- Reuses `Characterisation.ComponentTrees.GeneratingAlphabet.mso_compressed_iff`. -/
theorem mso_compressed_iff :
    ∀ {I₁ I₂ O₁ O₂ G : Type} {D capacity : ℕ} [inst : Fintype I₁]
      [inst_1 : Fintype I₂] [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] [inst_4 : Fintype O₁] [inst_5 : Fintype O₂]
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
                  MSO.Tree.Satisfies code (ComponentTrees.GeneratingAlphabet.sentence B live bound positive)) ↔
                ∃ (tree : ComponentTrees.CompressedTree B M bound), tree.Accepting) :=
  @_root_.Characterisation.ComponentTrees.GeneratingAlphabet.mso_compressed_iff

/-- Reuses `Characterisation.ComponentTrees.GeneratingAlphabet.satisfiable_correct`. -/
theorem satisfiable_correct :
    ∀ {I₁ I₂ O₁ O₂ G : Type} {D capacity : ℕ} [inst : Fintype I₁]
      [inst_1 : Fintype I₂] [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] [inst_4 : Fintype O₁] [inst_5 : Fintype O₂]
      [inst_6 : DecidableEq O₁] [inst_7 : DecidableEq O₂] [inst_8 : LinearOrder I₁] [inst_9 : LinearOrder I₂]
      [inst_10 : LinearOrder O₁] [inst_11 : LinearOrder O₂]
      (B : DetParityAutomaton (PeriodicBlocks.BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D)) [inst_12 : LinearOrder B.State]
      (live : B.State → Bool) (bound : ℕ) (positive : 0 < capacity),
      bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity →
        ∀ (M : Recognizer Graph G) [inst_13 : DecidablePred fun (x : G) => x ∈ M.accept],
          (∀ (h : EnvHistory I₁ I₂) (q : B.State),
              ComponentTrees.StateReachable B h q → (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept)) →
            M.eval [] ∈ M.accept →
              (ComponentTrees.GeneratingAlphabet.satisfiable B live bound positive = true ↔
                ∃ (tree : ComponentTrees.CompressedTree B M bound), tree.Accepting) :=
  @_root_.Characterisation.ComponentTrees.GeneratingAlphabet.satisfiable_correct

end DistributedSynthesis.Paper.MSO
