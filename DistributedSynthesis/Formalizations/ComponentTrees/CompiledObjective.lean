/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentTrees.CompressedEquivalence

/-! Use any compiled guarded objective with the proved full-word language
identity. The encoded compiler discharges this interface at the public endpoint. -/
namespace Characterisation.ComponentTrees.CompiledObjective
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
variable (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
variable (i : WithInputs.Instance) {D : Nat}
variable [DecidablePred (· ∈ (prefixRecognizer adversary).accept)]
variable (objective : DetParityAutomaton (WithInputs.TupleLetter i))
variable (language : ∀ word, objective.Accepts word ↔
  (WithInputs.guardedInstanceObjective adversary i).Accepts word)
include recognizes language

/-- Any strategy implementing the tree's local prescriptions realizes the
original formula on every admitted physical execution. -/
theorem implementing_strategy_realizes
    (positive : 0 < D)
    (tree : UncompressedTree (blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D) (prefixRecognizer adversary))
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
  have blocks := ((blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D).accepts_iff_natSeqMinEvenParity _).mpr parity
  have objectiveAccepts := (blockAutomaton_accepts (jointRecognizer (prefixRecognizer adversary))
    objective D positive _).mp blocks
  exact (WithInputs.guardedInstanceObjective_execution_iff adversary i σ env).mp ((language _).mp objectiveAccepts)
    ((recognizes _).mp admitted)

/-- Lemma `lem:tree-uncompressed-equivalence`, including nonclosed
omega-regular adversaries and arbitrary finite nonempty input/output alphabets.
Nonemptiness of A is precisely the standing assumption before the lemma. -/
theorem uncompressed_equivalence (nonempty : A.Nonempty) (positive : 0 < D) :
    (∃ tree : UncompressedTree (blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D) (prefixRecognizer adversary),
      tree.Accepting) ↔ WithInputs.Realizable A i := by
  constructor
  · rintro ⟨tree, accepting⟩
    obtain ⟨σ, implements⟩ := tree.component_controller_strategy accepting.1
    exact ⟨σ, implementing_strategy_realizes A adversary recognizes i objective language positive tree accepting σ implements⟩
  · intro realizable
    obtain ⟨σ, winning⟩ := (WithInputs.realizable_iff_guarded_objective A adversary recognizes i).mp realizable
    have prefixExact := prefixRecognizer_correct adversary A recognizes
    have initialLive : (prefixRecognizer adversary).eval [] ∈ (prefixRecognizer adversary).accept := by
      apply (prefixExact []).mp
      obtain ⟨word, admitted⟩ := nonempty
      exact ⟨word, admitted, rfl⟩
    apply (uncompressed_strategy_iff (blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D)
      (prefixRecognizer adversary) A prefixExact initialLive positive).mpr
    refine ⟨σ, fun word _ => ?_⟩
    obtain ⟨env, same⟩ := exists_environment_blocks positive word
    have blocks := (blockAutomaton_accepts (jointRecognizer (prefixRecognizer adversary))
      objective D positive _).mpr ((language _).mpr (winning env))
    have parity := ((blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D).accepts_iff_natSeqMinEvenParity _).mp blocks
    simpa only [← strategyState_execution σ env, same] using parity

/-- Executable local-output lookup from an accepting, effectively given
uncompressed tree. The search itself is `ExecutableReadback.strategy`; this
correctness theorem retains the full original LTL specification. -/
theorem executable_readback_realizes (positive : 0 < D)
    [DecidableEq (blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D).State]
    (tree : UncompressedTree (blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D) (prefixRecognizer adversary))
    (accepting : tree.Accepting) :
    ∀ env, (fun n => (env n).graph) ∈ A →
      LTL.Satisfies (EncodedNoDirect.interp i)
        (execution (ExecutableReadback.strategy _ _ tree (0, 0)) env)
        (EncodedFiniteLTL.decode i.formula) := by
  apply implementing_strategy_realizes A adversary recognizes i objective language positive tree accepting
  exact ExecutableReadback.strategy_implements _ _ tree accepting.1 (0, 0)


/-- The original LTL problem, through both tree constructions, with the
compiled objective rather than a noncomputable automaton choice. -/
theorem compressed_equivalence (nonempty : A.Nonempty) (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool),
      ComponentGames.Consensus.SolvesBy σ (Residual A u) D) :
    (∃ tree : CompressedTree (blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D)
      (prefixRecognizer adversary) (reductionBound (blockAutomaton (jointRecognizer (prefixRecognizer adversary)) objective D)),
      tree.Accepting) ↔ WithInputs.Realizable A i :=
  (block_bounded_representation (prefixRecognizer adversary) A
    (prefixRecognizer_correct adversary A recognizes) positive consensus objective).symm.trans
      (uncompressed_equivalence A adversary recognizes i objective language nonempty positive)

end
end Characterisation.ComponentTrees.CompiledObjective
