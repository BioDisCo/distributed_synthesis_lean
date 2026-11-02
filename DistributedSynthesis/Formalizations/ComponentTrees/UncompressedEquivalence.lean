/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.AlgorithmTree
import DistributedSynthesis.Formalizations.ComponentTrees.ExecutionBlocks
import DistributedSynthesis.Formalizations.ComponentTrees.ExecutableReadback
import DistributedSynthesis.Library.Distributed.LeaderPhases.InputParityObjective

/-! The algorithm/uncompressed-tree equivalence at the manuscript's LTL
strength. The readback uses the same local prescriptions as the English proof.
No topological closure assumption on the omega-language is made.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

section Abstract
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Nonempty O₁] [Nonempty O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- Abstract equivalence for the complete block language. The prefix
recognizer is exact, and every live block stream is quantified. -/
theorem uncompressed_strategy_iff (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (initialLive : M.eval [] ∈ M.accept) (positive : 0 < D) :
    (∃ tree : UncompressedTree B M, tree.Accepting) ↔
      ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ word : Nat → BlockInput I₁ I₂ D,
        (∀ n, M.eval (History.graphSequence (blockHistory (branchNode word n))) ∈ M.accept) →
        NatSeqMinEvenParity (fun n => B.priority (strategyState σ B (branchNode word n))) := by
  have closed : PrefixClosed (fun g => M.eval g ∈ M.accept) := by
    intro h w live
    exact (recognizes h).mp (livePrefix_closed A h w ((recognizes _).mpr live))
  constructor
  · rintro ⟨tree, accepting⟩
    obtain ⟨σ, implements⟩ := tree.component_controller_strategy accepting.1
    exact ⟨σ, tree.accepts_strategy_blocks accepting.1 closed σ implements positive accepting A recognizes⟩
  · rintro ⟨σ, winning⟩
    exact ⟨AlgorithmTree.tree B M σ initialLive,
      AlgorithmTree.tree_accepting B M σ initialLive positive closed winning⟩
end Abstract

/-- The concrete block automaton used throughout the component-tree proof. -/
def synthesisBlockAutomaton (adversary : DetParityAutomaton Graph)
    (i : WithInputs.Instance) (D : Nat) :=
  blockAutomaton (jointRecognizer (prefixRecognizer adversary))
    (WithInputs.guardedInstanceObjective adversary i) D

section Concrete
variable (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
variable (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
variable (i : WithInputs.Instance) {D : Nat}
include recognizes

/-- Any strategy implementing the tree's local prescriptions realizes the
original formula on every admitted physical execution. -/
theorem implementing_strategy_realizes
    (positive : 0 < D)
    (tree : UncompressedTree (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary))
    (accepting : tree.Accepting) (σ : WithInputs.Strategies i)
    (implements : ∀ x : tree.Prescription,
      (σ.one (currentView .one (tree.prescribedHistory x)),
       σ.two (currentView .two (tree.prescribedHistory x))) = tree.prescribedOutput x) :
    ∀ env, (fun n => (env n).graph) ∈ A →
      LTL.Satisfies (EncodedNoDirect.interp i) (execution σ env) (EncodedFiniteLTL.decode i.formula) := by
  have prefixExact := prefixRecognizer_correct adversary A recognizes
  have closed : PrefixClosed (fun g => (prefixRecognizer adversary).eval g ∈ (prefixRecognizer adversary).accept) := by
    intro h w live
    exact (prefixExact h).mp (livePrefix_closed A h w ((prefixExact _).mpr live))
  intro env admitted
  have live n : (prefixRecognizer adversary).eval
      (History.graphSequence (blockHistory (branchNode (eventBlock (environmentWord env) D) n))) ∈
      (prefixRecognizer adversary).accept := by
    rw [eventBlock_history, environmentWord_graph]
    apply (prefixExact _).mp
    refine ⟨fun t => (env t).graph, admitted, ?_⟩
    simp [graphPrefix, branchNode_eq_ofFn]
  have parity := tree.accepts_strategy_blocks accepting.1 closed σ implements positive accepting
    A prefixExact (eventBlock (environmentWord env) D) live
  simp only [strategyState_execution] at parity
  have blocks := ((synthesisBlockAutomaton adversary i D).accepts_iff_natSeqMinEvenParity _).mpr parity
  have objective := (blockAutomaton_accepts (jointRecognizer (prefixRecognizer adversary))
    (WithInputs.guardedInstanceObjective adversary i) D positive _).mp blocks
  exact (WithInputs.guardedInstanceObjective_execution_iff adversary i σ env).mp objective
    ((recognizes _).mp admitted)

/-- Lemma `lem:tree-uncompressed-equivalence`, including nonclosed
omega-regular adversaries and arbitrary finite nonempty input/output alphabets.
Nonemptiness of A is precisely the standing assumption before the lemma. -/
theorem uncompressed_equivalence (nonempty : A.Nonempty) (positive : 0 < D) :
    (∃ tree : UncompressedTree (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary),
      tree.Accepting) ↔ WithInputs.Realizable A i := by
  constructor
  · rintro ⟨tree, accepting⟩
    obtain ⟨σ, implements⟩ := tree.component_controller_strategy accepting.1
    exact ⟨σ, implementing_strategy_realizes A adversary recognizes i positive tree accepting σ implements⟩
  · intro realizable
    obtain ⟨σ, winning⟩ := (WithInputs.realizable_iff_guarded_objective A adversary recognizes i).mp realizable
    have prefixExact := prefixRecognizer_correct adversary A recognizes
    have initialLive : (prefixRecognizer adversary).eval [] ∈ (prefixRecognizer adversary).accept := by
      apply (prefixExact []).mp
      obtain ⟨word, admitted⟩ := nonempty
      exact ⟨word, admitted, rfl⟩
    apply (uncompressed_strategy_iff (synthesisBlockAutomaton adversary i D)
      (prefixRecognizer adversary) A prefixExact initialLive positive).mpr
    refine ⟨σ, fun word _ => ?_⟩
    obtain ⟨env, same⟩ := exists_environment_blocks positive word
    have blocks := (blockAutomaton_accepts (jointRecognizer (prefixRecognizer adversary))
      (WithInputs.guardedInstanceObjective adversary i) D positive _).mpr (winning env)
    have parity := ((synthesisBlockAutomaton adversary i D).accepts_iff_natSeqMinEvenParity _).mp blocks
    simpa only [← strategyState_execution σ env, same] using parity

/-- Executable local-output lookup from an accepting, effectively given
uncompressed tree. The search itself is `ExecutableReadback.strategy`; this
correctness theorem retains the full original LTL specification. -/
theorem executable_readback_realizes (positive : 0 < D)
    [DecidableEq (synthesisBlockAutomaton adversary i D).State]
    (tree : UncompressedTree (synthesisBlockAutomaton adversary i D) (prefixRecognizer adversary))
    (accepting : tree.Accepting) :
    ∀ env, (fun n => (env n).graph) ∈ A →
      LTL.Satisfies (EncodedNoDirect.interp i)
        (execution (ExecutableReadback.strategy _ _ tree (0, 0)) env)
        (EncodedFiniteLTL.decode i.formula) := by
  apply implementing_strategy_realizes A adversary recognizes i positive tree accepting
  exact ExecutableReadback.strategy_implements _ _ tree accepting.1 (0, 0)

end Concrete
end
end Characterisation.ComponentTrees
