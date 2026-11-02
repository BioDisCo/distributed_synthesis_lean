/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingEncode
import DistributedSynthesis.Formalizations.ComponentTrees.CompiledObjective
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusBound
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGuardedFrontend

/-! The decision procedure in current main.tex: consensus bound, compiled
block automaton, compressed component trees, and MSO satisfiability. -/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false

section Bounds
variable {I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))

def computedReductionBound : Nat :=
  (1 + Fintype.card B.State) ^ (Fintype.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
    Fintype.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D

def computedCapacity : Nat :=
  computedReductionBound B * Fintype.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D

theorem computedReductionBound_exact : computedReductionBound B = reductionBound B := by
  simp only [computedReductionBound,reductionBound,Nat.card_eq_fintype_card]

theorem computedCapacity_fits : computedReductionBound B * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤
    computedCapacity B := by simp only [computedCapacity,Nat.card_eq_fintype_card,le_refl]

theorem computedCapacity_positive [Nonempty I₁] [Nonempty I₂] : 0 < computedCapacity B := by
  classical
  letI : Nonempty (RoundRecord I₁ I₂ Graph Unit Unit) := ⟨⟨Classical.arbitrary I₁,Classical.arbitrary I₂,.both,(),()⟩⟩
  rw [computedCapacity,computedReductionBound_exact]
  exact Nat.mul_pos (reductionBound_positive B) (Nat.pow_pos Fintype.card_pos)
end Bounds

namespace Effective
open ComponentGames

def objective (d : EncodedGuardedObjective.Data) :=
  EncodedLeaderObjective.automaton (EncodedGuardedObjective.roundData d)

def automaton (d : EncodedGuardedObjective.Data) (D : Nat) :=
  blockAutomaton (jointRecognizer (prefixRecognizer (graphInput d.1))) (objective d) D

instance objectiveOrder (d : EncodedGuardedObjective.Data) : LinearOrder (objective d).State :=
  inferInstanceAs (LinearOrder (Fin (EncodedRoundObjectives.stateCount (EncodedGuardedObjective.roundData d))))
instance graphOrder (d : EncodedParityTables.Data) : LinearOrder (graphInput d).State :=
  inferInstanceAs (LinearOrder (Fin (EncodedParityTables.size d)))
instance stateOrder (d : EncodedGuardedObjective.Data) (D : Nat) : LinearOrder (automaton d D).State :=
  inferInstanceAs (LinearOrder ((graphInput d.1).State × (objective d).State × {p : Nat // p ∈ blockPriorities (objective d)}))

def live (d : EncodedGuardedObjective.Data) (D : Nat) (q : (automaton d D).State) : Bool :=
  decide (q.1 ∈ (prefixRecognizer (graphInput d.1)).accept)

theorem live_correct (d : EncodedGuardedObjective.Data) (D : Nat) h q
    (reachable : StateReachable (automaton d D) h q) :
    live d D q = true ↔ (prefixRecognizer (graphInput d.1)).eval (History.graphSequence h) ∈
      (prefixRecognizer (graphInput d.1)).accept := by
  simp only [live,decide_eq_true_eq]
  rw [reachable_graph_state (prefixRecognizer (graphInput d.1)) (objective d) h q reachable]

theorem objective_language (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3) (word : Nat → WithInputs.TupleLetter d.2) :
    (objective d).Accepts word ↔ (WithInputs.guardedInstanceObjective (graphInput d.1) d.2).Accepts word := by
  have language := EncodedGuardedObjective.accepts_semantic_guard_iff d alphabet word
  rw [EncodedGuardedObjective.automaton_eq_round] at language
  exact language

/-- Input data are the adversary table and LTL instance. The nowhere-dense
promise only justifies termination of the existing consensus-bound search. -/
def solve (d : EncodedGuardedObjective.Data)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) : Bool :=
  if (prefixRecognizer (graphInput d.1)).eval [] ∈ (prefixRecognizer (graphInput d.1)).accept then
    let D := Consensus.encodedConsensusBound d.1 promise
    GeneratingAlphabet.satisfiable (automaton d D) (live d D) (computedReductionBound (automaton d D))
      (computedCapacity_positive (automaton d D))
  else true

/-- Full LTL realizability, with no model, rank, transport, or consensus
certificate supplied beyond the manuscript's nowhere-dense promise. -/
theorem solve_correct (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) :
    solve d promise = true ↔ WithInputs.Realizable {word | (graphInput d.1).Accepts word} d.2 := by
  let A : Set (Nat → Graph) := {word | (graphInput d.1).Accepts word}
  have prefixExact := prefixRecognizer_correct (graphInput d.1) A (fun _ => Iff.rfl)
  unfold solve
  split
  · rename_i initialLive
    let D := Consensus.encodedConsensusBound d.1 promise
    have nonempty : A.Nonempty := by
      obtain ⟨word,admitted,_⟩ := (prefixExact []).mpr initialLive
      exact ⟨word,admitted⟩
    have consensus := Consensus.encodedConsensusBound_correct (V:=Bool) d.1 promise
    have finite := GeneratingAlphabet.satisfiable_correct (automaton d D) (live d D)
      (computedReductionBound (automaton d D)) (computedCapacity_positive (automaton d D))
      (computedCapacity_fits (automaton d D)) (prefixRecognizer (graphInput d.1)) (live_correct d D) initialLive
    have equivalence : (∃ tree : CompressedTree (automaton d D) (prefixRecognizer (graphInput d.1))
        (computedReductionBound (automaton d D)), tree.Accepting) ↔ WithInputs.Realizable A d.2 := by
      rw [computedReductionBound_exact]
      exact CompiledObjective.compressed_equivalence A (graphInput d.1) (fun _ => Iff.rfl)
        d.2 (objective d) (objective_language d alphabet) nonempty consensus.1 consensus.2
    exact finite.trans equivalence
  · rename_i empty
    refine ⟨fun _ => ?_,fun _ => rfl⟩
    refine ⟨⟨fun _ => 0,fun _ => 0⟩,?_⟩
    intro env admitted
    exact False.elim (empty ((prefixExact []).mp ⟨fun n => (env n).graph,admitted,rfl⟩))

end Effective
end Characterisation.ComponentTrees
