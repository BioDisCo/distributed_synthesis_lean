/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.UncompressedEquivalence
import DistributedSynthesis.Formalizations.ComponentTrees.BoundedRepresentation

/-! Compose the two tree equivalences at the manuscript's original LTL
strength. `ModelEquivalence` and `Decision` complete the MSO decision route.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

/-- The first two equivalences in the final decidability proof. Fresh binary
consensus proposals are independent of all application input alphabets. -/
theorem compressed_equivalence
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (nonempty : A.Nonempty) (i : WithInputs.Instance) {D : Nat} (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool),
      ComponentGames.Consensus.SolvesBy σ (Residual A u) D) :
    (∃ tree : CompressedTree (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary)
      (reductionBound (synthesisBlockAutomaton adversary i D)), tree.Accepting) ↔
      WithInputs.Realizable A i := by
  have bounded := block_bounded_representation (prefixRecognizer adversary) A
    (prefixRecognizer_correct adversary A recognizes) positive consensus
    (WithInputs.guardedInstanceObjective adversary i)
  exact bounded.symm.trans (uncompressed_equivalence A adversary recognizes i nonempty positive)

/-- Effective synthesis after the finite model has been decoded to a
compressed tree. Both recursive tree reconstruction and local view lookup
are the separately implemented executable constructions. -/
theorem compressed_executable_readback
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (i : WithInputs.Instance) {D bound : Nat} (positive : 0 < D)
    [DecidableEq (synthesisBlockAutomaton adversary i D).State]
    (tree : CompressedTree (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary) bound)
    (accepting : tree.Accepting) :
    ∀ env, (fun n => (env n).graph) ∈ A →
      LTL.Satisfies (EncodedNoDirect.interp i)
        (execution (ExecutableReadback.strategy (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary)
          (ExecutableReverse.tree (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary)
            (blockAutomaton_stateLiveness (prefixRecognizer adversary)
              (WithInputs.guardedInstanceObjective adversary i)) tree accepting.1) (0, 0)) env)
        (EncodedFiniteLTL.decode i.formula) := by
  exact executable_readback_realizes A adversary recognizes i positive _
    (ExecutableReverse.tree_accepting (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary)
    (blockAutomaton_stateLiveness (prefixRecognizer adversary)
      (WithInputs.guardedInstanceObjective adversary i)) tree accepting.1 accepting)

end
end Characterisation.ComponentTrees
