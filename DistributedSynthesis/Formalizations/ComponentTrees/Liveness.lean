/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.BlockAutomaton
import DistributedSynthesis.Formalizations.ComponentTrees.Positions

/-! State equality and liveness for the block automaton in `main.tex`.
The simulation uses this consequence of the product construction, rather
than assuming that arbitrary automata remember graph-recognizer states.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1800000

variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}

/-- The existing graph recognizer, reading the graph coordinate of a joint
input/output letter. Its state space and acceptance set are unchanged. -/
def jointRecognizer (M : Recognizer Graph G) : Recognizer (ContinuationLetter I₁ I₂ O₁ O₂) G where
  step q a := M.step q a.1.2.2
  start := M.start
  accept := M.accept

theorem jointRecognizer_eval (M : Recognizer Graph G)
    (w : List (ContinuationLetter I₁ I₂ O₁ O₂)) :
    (jointRecognizer M).eval w = M.eval (w.map (fun a => a.1.2.2)) := by
  simp only [Recognizer.eval, Recognizer.evalFrom, jointRecognizer, List.foldl_map]

theorem reachable_graph_state [Fintype G] (M : Recognizer Graph G)
    (A : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (h : EnvHistory I₁ I₂) (q : (blockAutomaton (jointRecognizer M) A D).State)
    (reachable : StateReachable (blockAutomaton (jointRecognizer M) A D) h q) :
    q.1 = M.eval (History.graphSequence h) := by
  obtain ⟨words, history, states⟩ := reachable
  have first := (blockAutomaton_finite_states (jointRecognizer M) A D words).1
  rw [states, jointRecognizer_eval] at first
  rw [← history]
  convert first using 1
  simp only [History.graphSequence, List.map_flatten, List.map_map, Function.comp_def]
  rfl

/-- The finite-prefix liveness specification asserted in the paper. -/
def StateLiveness
    (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
    (M : Recognizer Graph G) : Prop :=
  ∃ live : B.State → Prop, ∀ h q, StateReachable B h q →
    (live q ↔ M.eval (History.graphSequence h) ∈ M.accept)

theorem blockAutomaton_stateLiveness [Fintype G] (M : Recognizer Graph G)
    (A : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂)) :
    StateLiveness (blockAutomaton (jointRecognizer M) A D) M := by
  refine ⟨fun q => q.1 ∈ M.accept, fun h q reachable => ?_⟩
  change q.1 ∈ M.accept ↔ _
  rw [reachable_graph_state M A h q reachable]

theorem StateLiveness.equal_states
    {B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D)}
    {M : Recognizer Graph G} (spec : StateLiveness B M)
    {h k : EnvHistory I₁ I₂} {q r : B.State}
    (hr : StateReachable B h q) (kr : StateReachable B k r) (eq : q = r) :
    M.eval (History.graphSequence h) ∈ M.accept ↔ M.eval (History.graphSequence k) ∈ M.accept := by
  obtain ⟨live, characterises⟩ := spec
  exact (characterises h q hr).symm.trans (eq ▸ characterises k r kr)

end
end Characterisation.ComponentTrees
