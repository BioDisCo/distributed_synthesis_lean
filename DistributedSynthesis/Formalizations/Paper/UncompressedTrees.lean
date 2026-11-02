/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.CompiledObjective

/-!
# Algorithms and uncompressed component trees

Manuscript source label: `lem:tree-uncompressed-equivalence`.

## Paper statement

A distributed algorithm realizing~$\phi$ under~$A$ exists if and only if an
  accepting uncompressed component tree exists.
From an effectively given accepting uncompressed tree, one can compute the
  local output functions of a realizing algorithm.

## Correspondence

The compiled objective has language A-implies-phi. The forward equivalence and effective
readback use the same local views and full block outputs as the manuscript.

## Reading the proof

See the [proof locations](PROOFS.md#algorithms-and-uncompressed-component-trees) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.UncompressedTrees

/-- Reuses `Characterisation.ComponentTrees.CompiledObjective.uncompressed_equivalence`. -/
theorem uncompressed_equivalence :
    ∀ (A : Set (ℕ → Graph))
      (adversary : DetParityAutomaton Graph),
      (∀ (word : ℕ → Graph), word ∈ A ↔ adversary.Accepts word) →
        ∀ (i : WithInputs.Instance) {D : ℕ}
          [inst : DecidablePred fun (x : adversary.State) => x ∈ (prefixRecognizer adversary).accept]
          (objective : DetParityAutomaton (WithInputs.TupleLetter i)),
          (∀ (word : OmegaWord (WithInputs.TupleLetter i)),
              objective.Accepts word ↔ (WithInputs.guardedInstanceObjective adversary i).Accepts word) →
            A.Nonempty →
              0 < D →
                ((∃ (tree :
                    ComponentTrees.UncompressedTree
                      (ComponentTrees.blockAutomaton (ComponentTrees.jointRecognizer (prefixRecognizer adversary)) objective
                        D)
                      (prefixRecognizer adversary)),
                    tree.Accepting) ↔
                  WithInputs.Realizable A i) :=
  @_root_.Characterisation.ComponentTrees.CompiledObjective.uncompressed_equivalence

/-- Reuses `Characterisation.ComponentTrees.CompiledObjective.executable_readback_realizes`. -/
theorem executable_readback_realizes :
    ∀ (A : Set (ℕ → Graph))
      (adversary : DetParityAutomaton Graph),
      (∀ (word : ℕ → Graph), word ∈ A ↔ adversary.Accepts word) →
        ∀ (i : WithInputs.Instance) {D : ℕ}
          [inst : DecidablePred fun (x : adversary.State) => x ∈ (prefixRecognizer adversary).accept]
          (objective : DetParityAutomaton (WithInputs.TupleLetter i)),
          (∀ (word : OmegaWord (WithInputs.TupleLetter i)),
              objective.Accepts word ↔ (WithInputs.guardedInstanceObjective adversary i).Accepts word) →
            0 < D →
              ∀
                [inst_1 :
                  DecidableEq
                    (ComponentTrees.blockAutomaton (ComponentTrees.jointRecognizer (prefixRecognizer adversary)) objective
                        D).State]
                (tree :
                  ComponentTrees.UncompressedTree
                    (ComponentTrees.blockAutomaton (ComponentTrees.jointRecognizer (prefixRecognizer adversary)) objective
                      D)
                    (prefixRecognizer adversary)),
                tree.Accepting →
                  ∀ (env : EnvironmentSequence (Fin (i.inputOneSizeMinusOne + 1)) (Fin (i.inputTwoSizeMinusOne + 1))),
                    (fun (n : ℕ) => (env n).graph) ∈ A →
                      LTL.Satisfies (EncodedNoDirect.interp i)
                        (execution
                          (ComponentTrees.ExecutableReadback.strategy
                            (ComponentTrees.blockAutomaton (ComponentTrees.jointRecognizer (prefixRecognizer adversary))
                              objective D)
                            (prefixRecognizer adversary) tree (0, 0))
                          env)
                        (EncodedFiniteLTL.decode i.formula) :=
  @_root_.Characterisation.ComponentTrees.CompiledObjective.executable_readback_realizes

end DistributedSynthesis.Paper.UncompressedTrees
