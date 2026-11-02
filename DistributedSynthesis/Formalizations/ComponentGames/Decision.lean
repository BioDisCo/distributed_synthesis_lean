/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteEquivalence

namespace Characterisation.ComponentGames
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

/-- Exactly N |Sigma|^D, evaluated from the finite alphabets and states. -/
def computedWidth (I₁ I₂ O₁ O₂ G Q : Type)
    [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q] (D : Nat) : Nat :=
  (Fintype.card G * Fintype.card Q *
    Fintype.card (O₁ × O₂) ^ (∑ t : Fin D, Fintype.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ (t.val+1)) *
    2 ^ (Fintype.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D)) *
    Fintype.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D

theorem computedWidth_exact (I₁ I₂ O₁ O₂ G Q : Type)
    [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
    [Nonempty I₁] [Nonempty I₂] [Nonempty O₁] [Nonempty O₂] (D : Nat) :
    computedWidth I₁ I₂ O₁ O₂ G Q D = compressionBound I₁ I₂ O₁ O₂ G Q D := by
  classical
  rw [HistoryGame.compressionBound_exact]
  simp only [computedWidth,Nat.card_eq_fintype_card]

instance compiledObjectiveDecidableEq (d : EncodedGuardedObjective.Data) :
    DecidableEq (EncodedLeaderObjective.automaton (EncodedGuardedObjective.roundData d)).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount (EncodedGuardedObjective.roundData d))))

/-- The complete decision construction along the manuscript's route:
increasing consensus search, exact bounded history width, finite
representations, ternary-relation monitor, and finite parity solving. -/
def solve (d : EncodedGuardedObjective.Data)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) : Bool :=
  let D := Consensus.encodedConsensusBound d.1 promise
  let objective := EncodedLeaderObjective.automaton (EncodedGuardedObjective.roundData d)
  let W := computedWidth (Fin (d.2.inputOneSizeMinusOne+1)) (Fin (d.2.inputTwoSizeMinusOne+1))
    (Fin (d.2.outputOneSizeMinusOne+1)) (Fin (d.2.outputTwoSizeMinusOne+1)) (graphInput d.1).State objective.State D
  have width : 0 < W := by
    dsimp only [W]
    rw [computedWidth_exact]
    exact HistoryGame.compressionBound_positive (prefixRecognizer (graphInput d.1)) objective.initial
  Representation.decideBounded (D:=D) (prefixRecognizer (graphInput d.1))
    (fun q e y => objective.step q (e,y)) objective.priority W objective.initial width

/-- The English chain, now through the paper-specific finite arena rather
than substituting the older PeriodicBlocks arena. The numerical guarded
objective may be any compiler output with the checked language equality. -/
theorem solve_correct (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) :
    solve d promise = true ↔ WithInputs.Realizable {word | (graphInput d.1).Accepts word} d.2 := by
  let A : Set (Nat → Graph) := {word | (graphInput d.1).Accepts word}
  let adversary := graphInput d.1
  let objective := EncodedLeaderObjective.automaton (EncodedGuardedObjective.roundData d)
  let D := Consensus.encodedConsensusBound d.1 promise
  have language : ∀ word, objective.Accepts word ↔ (WithInputs.guardedInstanceObjective adversary d.2).Accepts word := by
    intro word
    have h := EncodedGuardedObjective.accepts_semantic_guard_iff d alphabet word
    rw [EncodedGuardedObjective.automaton_eq_round] at h
    exact h
  have prefixExact := prefixRecognizer_correct adversary A (fun _ => Iff.rfl)
  have closed : PrefixClosed (fun g => (prefixRecognizer adversary).eval g ∈ (prefixRecognizer adversary).accept) := by
    intro h w live
    exact (prefixExact h).mp (livePrefix_closed A h w ((prefixExact (h++w)).mpr live))
  have escape : ∀ (σ : WithInputs.Strategies d.2)
      (word : Nat → RoundRecord (Fin (d.2.inputOneSizeMinusOne+1)) (Fin (d.2.inputTwoSizeMinusOne+1)) Graph Unit Unit),
      (∃ n, (prefixRecognizer adversary).eval (History.graphSequence (branchNode word n)) ∉ (prefixRecognizer adversary).accept) →
      NatSeqMinEvenParity (fun n => objective.priority (strategyHistoryLabel σ
        (fun q e y => objective.step q (e,y)) objective.initial (branchNode word n))) := by
    intro σ word bad
    apply guarded_block_escape A adversary (fun _ => Iff.rfl) d.2 objective language σ word
    obtain ⟨n,missing⟩ := bad
    exact ⟨n,fun live => missing ((prefixExact _).mp live)⟩
  have consensus := Consensus.encodedConsensusBound_correct (V:=Bool) d.1 promise
  have holes := Consensus.recognizer_exact_holes A (prefixRecognizer adversary) prefixExact D consensus.1 consensus.2
  unfold solve
  rw [Representation.decideBounded_correct,computedWidth_exact]
  erw [HistoryGame.bounded_game_equivalence_of_holes (prefixRecognizer adversary)
    (fun q e y => objective.step q (e,y)) objective.initial objective.priority closed escape consensus.1 holes]
  erw [HistoryGame.replacement_game_equivalence,HistoryGame.component_game_history_iff (prefixRecognizer adversary)
    (fun q e y => objective.step q (e,y)) objective.initial objective.priority closed escape consensus.1]
  rw [← objective_realizability_history_iff objective,WithInputs.realizable_iff_guarded_objective A adversary (fun _ => Iff.rfl) d.2]
  apply exists_congr
  intro σ
  apply forall_congr'
  intro env
  exact language _

end Characterisation.ComponentGames
