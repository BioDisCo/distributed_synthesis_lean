/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedGameEquivalence
import DistributedSynthesis.Library.Distributed.LeaderPhases.InputParityObjective

/-! Graph-only holes give an exact finite-game characterization of the
finite-private-input LTL model, including X. The adversary's infinite
acceptance is retained by the original guarded objective. This is a semantic
reduction; it does not assert uniform computability of its encoded data. -/
namespace Characterisation
open DistributedSynthesis
namespace WithInputs

attribute [local instance] Classical.propDecidable

/-- The graph delay and graph-component bound are fixed before the input
instance. Only the input-dependent boundary width and objective rank bound
vary with that instance. -/
theorem holes_numbered_game_characterization
    (A : Set (Nat → Graph)) (nonempty : A.Nonempty)
    (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (holes : GeometricHoles A) :
    ∃ delay K, ∀ instanceData : Instance,
      ∃ B C, ∃ rank : (guardedInstanceObjective adversary instanceData).State → Fin (C+1),
        ∃ initial : NumberedSuccessorChoice (GQ:=adversary.State) (d:=delay) (K:=K) (B:=B) (C:=C)
            (guardedInstanceObjective adversary instanceData),
          (∀ q, (rank q).val = (guardedInstanceObjective adversary instanceData).priority q) ∧
          NumberedBoundaryRep (prefixRecognizer adversary) (guardedInstanceObjective adversary instanceData)
            (LivePrefix A) (fun _ => (guardedInstanceObjective adversary instanceData).initial)
            initial.1.1 initial.2 (boundaryOrigin (LivePrefix A) []) ∧
          (numberedLeaderGameTest (prefixRecognizer adversary) (guardedInstanceObjective adversary instanceData)
            rank initial.1 (numberedGameInitialCode (guardedInstanceObjective adversary instanceData) rank initial) = true ↔
              Realizable A instanceData) := by
  classical
  have regular : OmegaRegular A := ⟨adversary,recognizes⟩
  obtain ⟨delay,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨K,bounded⟩ := (omegaRegular_holes_iff_bounded_components A regular).mp holes
  refine ⟨delay,K,?_⟩
  intro instanceData
  let objective := guardedInstanceObjective adversary instanceData
  let I₁ := Fin (instanceData.inputOneSizeMinusOne+1)
  let I₂ := Fin (instanceData.inputTwoSizeMinusOne+1)
  obtain ⟨width,bound⟩ := bounded_leader_boundaries (I₁:=I₁) (I₂:=I₂)
    (LivePrefix A) (livePrefix_closed A) ⟨K,bounded⟩ delay recent
  let B := width+1
  let C := Finset.univ.sup objective.priority
  let rank : objective.State → Fin (C+1) := fun q => ⟨objective.priority q,
    Nat.lt_succ_of_le (Finset.le_sup (f:=objective.priority) (Finset.mem_univ q))⟩
  have rankExact : ∀ q, (rank q).val = objective.priority q := fun _ => rfl
  have live : LivePrefix A [] := by
    obtain ⟨word,admitted⟩ := nonempty
    exact ⟨word,admitted,rfl⟩
  have small : ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      leaderBoundary (LivePrefix A) delay h = true → Nat.card (InputHistoryComponent (LivePrefix A) h) ≤ B := by
    intro h alive boundary
    exact (bound h alive boundary).2.trans (Nat.le_succ width)
  have escape : ∀ (σ : Strategies instanceData) (env : EnvironmentSequence I₁ I₂),
      (∃ n, ¬ LivePrefix A (branchNode (fun t => (env t).graph) n)) →
      objective.Accepts (fun n => recordContinuationLetter (execution σ env n)) := by
    intro σ env bad
    apply (guardedInstanceObjective_execution_iff adversary instanceData σ env).mpr
    intro admitted
    obtain ⟨n,missing⟩ := bad
    apply False.elim
    apply missing
    refine ⟨(fun t => (env t).graph),(recognizes _).mpr admitted,?_⟩
    simp [graphPrefix,branchNode_eq_ofFn]
  obtain ⟨initial,represented,correct⟩ := numberedGameTest_exists_correct (d:=delay) (K:=K) (B:=B)
    (prefixRecognizer adversary) objective rank rankExact (LivePrefix A) (livePrefix_closed A)
    (prefixRecognizer_correct adversary A recognizes) recent bounded small live escape (Nat.zero_lt_succ width)
  refine ⟨B,C,rank,initial,rankExact,represented,?_⟩
  exact correct.trans (realizable_iff_guarded_objective A adversary recognizes instanceData).symm

end WithInputs
end Characterisation
