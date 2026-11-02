/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.Decidability
import DistributedSynthesis.Formalizations.ComponentGames.ComponentSoundness
import DistributedSynthesis.Formalizations.ComponentGames.Objective

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-- Abstract guarded-objective version; neither the prefix language nor
its omega-language is assumed closed in the infinite-word topology. -/
theorem component_game_history_iff
    {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
    [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    [Nonempty O₁] [Nonempty O₂]
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (χ : Q → Nat)
    (closed : PrefixClosed (fun g => M.eval g ∈ M.accept))
    (escape : ∀ (σ : StrategyPair I₁ I₂ O₁ O₂) (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit),
      (∃ n, M.eval (History.graphSequence (branchNode word n)) ∉ M.accept) →
      NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))))
    (positive : 0 < D) :
    (∃ tree, Winning (D:=D) M step .component q₀ χ tree) ↔
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
        NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))) := by
  constructor
  · rintro ⟨tree,winning⟩
    obtain ⟨σ,correct⟩ := component_winning_algorithm M step q₀ tree closed positive χ winning
    refine ⟨σ,fun word => ?_⟩
    by_cases live : ∀ n, M.eval (History.graphSequence (branchNode word n)) ∈ M.accept
    · exact correct word live
    · exact escape σ word (not_forall.mp live)
  · rintro ⟨σ,correct⟩
    exact ⟨algorithmTree q₀ σ,algorithm_winning_component M step q₀ σ positive χ correct⟩

/-- Lemma 3.10 at the paper's LTL strength. A is any omega-language
recognized by the given adversary automaton; D is any positive block length.
All input/output alphabets in Instance are finite and nonempty. -/
theorem component_game_equivalence
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (i : WithInputs.Instance) {D : Nat} (positive : 0 < D) :
    (∃ tree, Winning (D:=D) (prefixRecognizer adversary)
      (fun q e y => (WithInputs.guardedInstanceObjective adversary i).step q (e,y)) .component
      (WithInputs.guardedInstanceObjective adversary i).initial
      (WithInputs.guardedInstanceObjective adversary i).priority tree) ↔ WithInputs.Realizable A i := by
  let objective := WithInputs.guardedInstanceObjective adversary i
  have prefixExact := prefixRecognizer_correct adversary A recognizes
  have closed : PrefixClosed (fun g => (prefixRecognizer adversary).eval g ∈ (prefixRecognizer adversary).accept) := by
    intro h w live
    exact (prefixExact h).mp (livePrefix_closed A h w ((prefixExact (h++w)).mpr live))
  have escape : ∀ (σ : WithInputs.Strategies i)
      (word : Nat → RoundRecord (Fin (i.inputOneSizeMinusOne+1)) (Fin (i.inputTwoSizeMinusOne+1)) Graph Unit Unit),
      (∃ n, (prefixRecognizer adversary).eval (History.graphSequence (branchNode word n)) ∉ (prefixRecognizer adversary).accept) →
      NatSeqMinEvenParity (fun n => objective.priority (strategyHistoryLabel σ
        (fun q e y => objective.step q (e,y)) objective.initial (branchNode word n))) := by
    intro σ word bad
    apply guarded_block_escape A adversary recognizes i objective (fun _ => Iff.rfl) σ word
    obtain ⟨n,missing⟩ := bad
    exact ⟨n,fun live => missing ((prefixExact _).mp live)⟩
  rw [component_game_history_iff (prefixRecognizer adversary)
    (fun q e y => objective.step q (e,y)) objective.initial objective.priority closed escape positive]
  rw [← objective_realizability_history_iff objective]
  exact (WithInputs.realizable_iff_guarded_objective A adversary recognizes i).symm

end
end Characterisation.ComponentGames.HistoryGame
