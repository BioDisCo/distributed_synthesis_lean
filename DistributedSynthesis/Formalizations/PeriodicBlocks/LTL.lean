/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.ObjectiveBridge

/-! The new reduction for the paper's finite-input LTL model. Only the
existing LTL-to-parity frontend and prefix recognizer are reused. The game
and both realizability implications are the periodic-block construction. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
open Characterisation.WithInputs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxSynthPendingDepth 16

/-- The concrete finite public game for one LTL instance. This is a typed
semantic construction, not a new encoded executable solver. -/
def instanceBlockGame (adversary : DetParityAutomaton Graph) (instanceData : Instance)
    (B D K : Nat) :=
  let objective := guardedInstanceObjective adversary instanceData
  blockGame (prefixRecognizer adversary) (fun q e y => objective.step q (e,y)) objective.priority
    (initialBlockOutcome (prefixRecognizer adversary) objective.initial B D) ((0,0) : HandoverCode B K)

/-- The full LTL realizability equivalence, with one finite block game.
Blocks have a fixed positive length. The width bounds the compressed
families, not the original input-dependent components. -/
theorem holes_periodic_LTL_characterization
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (holes : GeometricHoles A) (instanceData : Instance) :
    ∃ D B K : Nat, 0 < D ∧
      ((∃ tree, (instanceBlockGame adversary instanceData B D K).WinningTree tree) ↔
        WithInputs.Realizable A instanceData) := by
  classical
  let objective := guardedInstanceObjective adversary instanceData
  let K := Finset.univ.sup objective.priority
  have bounded : ∀ q, objective.priority q ≤ K :=
    fun q => Finset.le_sup (f:=objective.priority) (Finset.mem_univ q)
  have escape : ∀ (σ : Strategies instanceData)
      (word : Nat → RoundRecord (Fin (instanceData.inputOneSizeMinusOne+1))
        (Fin (instanceData.inputTwoSizeMinusOne+1)) Graph Unit Unit),
      (∃ n, ¬ LivePrefix A (History.graphSequence (branchNode word n))) →
        NatSeqMinEvenParity (fun n => objective.priority
          (strategyHistoryLabel σ (fun q e y => objective.step q (e,y)) objective.initial (branchNode word n))) := by
    intro σ word bad
    have accepted : objective.Accepts
        (fun n => recordContinuationLetter (execution σ (wordEnvironment word) n)) := by
      apply (guardedInstanceObjective_execution_iff adversary instanceData σ (wordEnvironment word)).mpr
      intro admitted
      obtain ⟨n,missing⟩ := bad
      apply False.elim
      apply missing
      refine ⟨(fun t => (wordEnvironment word t).graph),(recognizes _).mpr admitted,?_⟩
      have pref : History.graphSequence (branchNode word n) =
          graphPrefix (fun t => (wordEnvironment word t).graph) n := by
        calc
          _ = History.graphSequence (branchNode (environmentWord (wordEnvironment word)) n) := by
            rw [environmentWord_wordEnvironment]
          _ = branchNode (fun t => (wordEnvironment word t).graph) n := environmentWord_graph _ n
          _ = _ := by simp [graphPrefix,branchNode_eq_ofFn]
      have len : (History.graphSequence (branchNode word n)).length = n := by
        simp only [History.graphSequence,List.length_map,TreeNonemptiness.branch_length]
      rw [len]
      exact pref.symm
    simpa only [environmentWord_wordEnvironment] using
      (objective_accepts_history_iff objective σ (wordEnvironment word)).mp accepted
  obtain ⟨D,B,positive,equivalence⟩ := holes_periodic_block_game (prefixRecognizer adversary)
    (fun q e y => objective.step q (e,y)) objective.initial objective.priority (LivePrefix A) escape
    A ⟨adversary,recognizes⟩ holes rfl bounded (prefixRecognizer_correct adversary A recognizes)
  refine ⟨D,B,K,positive,?_⟩
  exact equivalence.trans ((realizable_iff_guarded_objective A adversary recognizes instanceData).trans
    (objective_realizability_history_iff objective)).symm

/-- A realizable instance has a finite public controller for the new game.
Conversely, such a controller yields a distributed realizing strategy. -/
theorem holes_periodic_LTL_finite_controller
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (holes : GeometricHoles A) (instanceData : Instance) :
    ∃ D B K : Nat, 0 < D ∧
      ((∃ table : RunParityTreeAutomaton.StateControlledTreeTable
          (instanceBlockGame adversary instanceData B D K).toRunAutomaton,
        (instanceBlockGame adversary instanceData B D K).WinningTree table.toTransitionRationalTree.labeledTree) ↔
        WithInputs.Realizable A instanceData) := by
  classical
  obtain ⟨D,B,K,positive,equivalence⟩ := holes_periodic_LTL_characterization A adversary recognizes holes instanceData
  refine ⟨D,B,K,positive,?_⟩
  constructor
  · rintro ⟨table,winning⟩
    exact equivalence.mp ⟨table.toTransitionRationalTree.labeledTree,winning⟩
  · intro realizable
    obtain ⟨tree,winning⟩ := equivalence.mpr realizable
    let game := instanceBlockGame adversary instanceData B D K
    letI : Nonempty (BlockOutcome (Fin (instanceData.inputOneSizeMinusOne+1))
        (Fin (instanceData.inputTwoSizeMinusOne+1)) adversary.State
        (guardedInstanceObjective adversary instanceData).State B D) :=
      ⟨initialBlockOutcome (prefixRecognizer adversary) (guardedInstanceObjective adversary instanceData).initial B D⟩
    obtain ⟨table,accepted⟩ := game.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨tree,(game.acceptsTree_iff_winningTree tree).mpr winning⟩
    exact ⟨table,(game.acceptsTree_iff_winningTree _).mp accepted⟩

end
end Characterisation.PeriodicBlocks
