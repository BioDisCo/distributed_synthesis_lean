/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometricBridge
import DistributedSynthesis.Library.Distributed.GraphAdversaries.SingletonInputs

/-! Every omega-regular adversary has a finite-state live-prefix recognizer.
The accept set is semantic (states having an accepting continuation); this
file establishes finite recognizability, not an executable liveness solver. -/

namespace Characterisation

open DistributedSynthesis

def prependGraphs (h : List Graph) (x : Nat → Graph) : Nat → Graph :=
  fun n => if n < h.length then h.getD n Graph.both else x (n - h.length)

theorem prependGraphs_prefix (h : List Graph) (x : Nat → Graph) :
    graphPrefix (prependGraphs h x) h.length = h := by
  apply List.ext_getElem
  · simp [graphPrefix]
  · intro i hi hj
    simp [graphPrefix, prependGraphs]

theorem prependGraphs_drop (h : List Graph) (x : Nat → Graph) :
    OmegaWord.drop (prependGraphs h x) h.length = x := by
  funext n
  simp [OmegaWord.drop, prependGraphs]

def prefixRecognizer (M : DetParityAutomaton Graph) : Recognizer Graph M.State where
  step := M.step
  start := M.initial
  accept := {q | ∃ x, M.AcceptsFrom q x}

theorem prefixRecognizer_eval (M : DetParityAutomaton Graph)
    (q : M.State) (x : Nat → Graph) (n : Nat) :
    (prefixRecognizer M).evalFrom q (graphPrefix x n) = M.runFrom q x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [graphPrefix_succ, Recognizer.evalFrom_of_append]
    change M.step ((prefixRecognizer M).evalFrom q (graphPrefix x n)) (x n) = _
    rw [ih]
    rfl

theorem prefixRecognizer_correct (M : DetParityAutomaton Graph)
    (A : Set (Nat → Graph)) (recognizes : ∀ x, x ∈ A ↔ M.Accepts x)
    (h : List Graph) :
    LivePrefix A h ↔ (prefixRecognizer M).eval h ∈ (prefixRecognizer M).accept := by
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨OmegaWord.drop x h.length, ?_⟩
    have stateEq : (prefixRecognizer M).eval h = M.runFrom M.initial x h.length := by
      change (prefixRecognizer M).evalFrom M.initial h = _
      simpa only [hp] using prefixRecognizer_eval M M.initial x h.length
    rw [stateEq]
    exact (M.acceptsFrom_runFrom_drop_iff M.initial x h.length).mpr ((recognizes x).mp hx)
  · rintro ⟨x, hx⟩
    let y := prependGraphs h x
    refine ⟨y, (recognizes y).mpr ?_, prependGraphs_prefix h x⟩
    apply (M.acceptsFrom_runFrom_drop_iff M.initial y h.length).mp
    have stateEq : M.runFrom M.initial y h.length = (prefixRecognizer M).eval h := by
      rw [← prefixRecognizer_eval, prependGraphs_prefix]
      rfl
    rw [stateEq, prependGraphs_drop]
    exact hx

/-- The geometric sufficient condition already entails a uniform finite-row
bound under the exact omega-regularity hypothesis of the conjecture. -/
theorem omegaRegular_geometric_holes_bound_rows (A : Set (Nat → Graph))
    (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ K, ∀ t a b, a ≤ b → b ≤ 3 ^ t →
      (∀ j, a ≤ j → j < b → LiveIndex (LivePrefix A) t j) → b - a < K := by
  obtain ⟨M, hM⟩ := regular
  exact geometric_holes_bound_rows A (prefixRecognizer M)
    (prefixRecognizer_correct M A hM) holes

end Characterisation
