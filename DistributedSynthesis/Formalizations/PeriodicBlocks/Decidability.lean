/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockFrontendCorrect
import DistributedSynthesis.Formalizations.PeriodicBlocks.LTL

/-! A uniform primitive-recursive solver obtained from the new fixed-block
reduction. The old distributed synthesis solver and its correctness theorem
are not used. -/
namespace Characterisation.PeriodicBlocks
open DistributedSynthesis Characterisation.WithInputs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 16

/-- Language equivalence to the guarded objective supplies the escape
condition of the block reduction, including for nonclosed adversaries. -/
theorem guarded_block_escape
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (i : Instance) (objective : DetParityAutomaton (TupleLetter i))
    (language : ∀ word, objective.Accepts word ↔ (guardedInstanceObjective adversary i).Accepts word)
    (σ : Strategies i)
    (word : Nat → RoundRecord (Fin (i.inputOneSizeMinusOne+1)) (Fin (i.inputTwoSizeMinusOne+1)) Graph Unit Unit)
    (bad : ∃ n, ¬ LivePrefix A (History.graphSequence (branchNode word n))) :
    NatSeqMinEvenParity (fun n => objective.priority
      (strategyHistoryLabel σ (fun q e y => objective.step q (e,y)) objective.initial (branchNode word n))) := by
  have accepted : objective.Accepts
      (fun n => recordContinuationLetter (execution σ (wordEnvironment word) n)) := by
    apply (language _).mpr
    apply (guardedInstanceObjective_execution_iff adversary i σ (wordEnvironment word)).mpr
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

/-- For a fixed positive block length with common roots, the compiled block
solver decides the original LTL instance. Every table is generated from the
instance and the fixed prefix recognizer. -/
theorem periodic_solver_correct
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    {S D : Nat} (graph : adversary.State ≃ Fin S) (positive : 0 < D)
    (common : ∀ (I₁ I₂ : Type), CommonBlockRoots (I₁:=I₁) (I₂:=I₂) (LivePrefix A) D)
    (i : Instance) (tables : EncodedParityTables.Data)
    (language : ∀ word, (EncodedLeaderObjective.automaton (i,tables)).Accepts word ↔
      (guardedInstanceObjective adversary i).Accepts word) :
    EncodedBlock.solveObjective (D,blockGraphData (prefixRecognizer adversary) graph,(i,tables)) = true ↔
      WithInputs.Realizable A i := by
  let objective := EncodedLeaderObjective.automaton (i,tables)
  rw [solveObjective_correct (prefixRecognizer adversary) graph D (i,tables) positive]
  rw [periodic_block_game_iff (prefixRecognizer adversary)
    (fun q e y => objective.step q (e,y)) objective.initial objective.priority
    (LivePrefix A) (livePrefix_closed A) (prefixRecognizer_correct adversary A recognizes)
    (guarded_block_escape A adversary recognizes i objective language) positive
    (EncodedLeaderObjective.priority_le_bound (i,tables)) (common _ _)
    (block_instanceBound (prefixRecognizer adversary) graph D (i,tables))]
  rw [← objective_realizability_history_iff objective,realizable_iff_guarded_objective A adversary recognizes i]
  apply exists_congr
  intro σ
  apply forall_congr'
  intro env
  exact language _

/-- Every fixed omega-regular adversary with graph-only holes admits a
primitive-recursive Boolean solver on the original finite-input LTL encoding.
The solver is constructed by the periodic-block route, including its numeric
encoding and correctness proof. -/
theorem holes_periodic_primitive_recursive_solver
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ solve : Instance → Bool, Primrec solve ∧ ∀ i, solve i = true ↔ WithInputs.Realizable A i := by
  obtain ⟨D,positive,common⟩ := holes_uniform_block_length A regular holes
  obtain ⟨adversary,recognizes⟩ := regular
  obtain ⟨tables,effective,language⟩ := EncodedGuardedObjective.uniform_frontend adversary
  let graph := Fintype.equivFin adversary.State
  let g := blockGraphData (prefixRecognizer adversary) graph
  let solve := fun i => EncodedBlock.solveObjective (D,g,(i,tables i))
  refine ⟨solve,EncodedBlock.solveObjective_primrec.comp
    ((Primrec.const D).pair ((Primrec.const g).pair (Primrec.id.pair effective))),?_⟩
  intro i
  exact periodic_solver_correct A adversary recognizes graph positive common i (tables i) (language i)

/-- Computable realizability, with precisely the original theorem's hypotheses. -/
theorem holes_periodic_realizable_computable
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ComputablePred (WithInputs.Realizable A) := by
  obtain ⟨solve,effective,correct⟩ := holes_periodic_primitive_recursive_solver A regular holes
  exact (Primrec.eq.comp effective (Primrec.const true)).computablePred.of_eq correct

end
end Characterisation.PeriodicBlocks
