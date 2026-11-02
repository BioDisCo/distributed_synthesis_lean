/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.Decision
import DistributedSynthesis.Formalizations.ComponentGames.BoundedSynthesis

namespace Characterisation.ComponentGames
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

local instance compiledObjectiveLinearOrder (d : EncodedGuardedObjective.Data) :
    LinearOrder (EncodedLeaderObjective.automaton (EncodedGuardedObjective.roundData d)).State :=
  inferInstanceAs (LinearOrder (Fin (EncodedRoundObjectives.stateCount (EncodedGuardedObjective.roundData d))))
local instance graphInputLinearOrder (d : EncodedParityTables.Data) : LinearOrder (graphInput d).State :=
  inferInstanceAs (LinearOrder (Fin (EncodedParityTables.size d)))

/-- Returns actual local output functions, obtained by finite controller
extraction, the manuscript simulations, and finite local-view readback. -/
def synthesize (d : EncodedGuardedObjective.Data)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) : Option (WithInputs.Strategies d.2) :=
  let D := Consensus.encodedConsensusBound d.1 promise
  let objective := EncodedLeaderObjective.automaton (EncodedGuardedObjective.roundData d)
  let W := computedWidth (Fin (d.2.inputOneSizeMinusOne+1)) (Fin (d.2.inputTwoSizeMinusOne+1))
    (Fin (d.2.outputOneSizeMinusOne+1)) (Fin (d.2.outputTwoSizeMinusOne+1)) (graphInput d.1).State objective.State D
  have width : 0 < W := by
    dsimp only [W]
    rw [computedWidth_exact]
    exact HistoryGame.compressionBound_positive (prefixRecognizer (graphInput d.1)) objective.initial
  ExecutableSynthesis.synthesizeBounded (D:=D) (prefixRecognizer (graphInput d.1))
    (fun q e y => objective.step q (e,y)) objective.priority W objective.initial width (0,0)


theorem synthesize_complete (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) :
    (∃ σ, synthesize d promise = some σ) ↔
      WithInputs.Realizable {word | (graphInput d.1).Accepts word} d.2 := by
  rw [← solve_correct d alphabet promise]
  unfold synthesize solve
  exact ExecutableSynthesis.synthesizeBounded_complete _ _ _ _ _ _ _

/-- Soundness is about the returned strategy itself, on every admitted
execution of the original LTL instance. -/
theorem synthesize_sound (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word}))
    (σ : WithInputs.Strategies d.2) (found : synthesize d promise = some σ) :
    ∀ env, (graphInput d.1).Accepts (fun n => (env n).graph) →
      LTL.Satisfies (EncodedNoDirect.interp d.2) (execution σ env) (EncodedFiniteLTL.decode d.2.formula) := by
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
  have liveCorrect (word : Nat → RoundRecord (Fin (d.2.inputOneSizeMinusOne+1)) (Fin (d.2.inputTwoSizeMinusOne+1)) Graph Unit Unit)
      (live : ∀ n, (prefixRecognizer adversary).eval (History.graphSequence (branchNode word n)) ∈ (prefixRecognizer adversary).accept) :
      NatSeqMinEvenParity (fun n => objective.priority (strategyHistoryLabel σ
        (fun q e y => objective.step q (e,y)) objective.initial (branchNode word n))) := by
    unfold synthesize at found
    exact ExecutableSynthesis.synthesizeBounded_sound _ _ _ _ _ _ _ σ found closed consensus.1 word live
  intro env admitted
  apply (WithInputs.guardedInstanceObjective_execution_iff adversary d.2 σ env).mp _ admitted
  apply (language _).mp
  apply (objective_accepts_history_iff objective σ env).mpr
  by_cases live : ∀ n, (prefixRecognizer adversary).eval (History.graphSequence
      (branchNode (environmentWord env) n)) ∈ (prefixRecognizer adversary).accept
  · exact liveCorrect _ live
  · exact escape σ _ (Classical.not_forall.mp live)

end Characterisation.ComponentGames
