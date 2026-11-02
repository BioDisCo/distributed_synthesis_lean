/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FinitePhaseOffers
import Mathlib.Data.Fintype.Pi

/-! An exact offer can retain the priority minima of all source roots over
an arbitrarily long phase. Its finite search state includes those minima;
searching only the original controller state would lose this information. -/
namespace Characterisation

section
variable {State Input H Outcome : Type} {C : Nat}

/-- Minimum of the physical transition priorities along the given word.
The maximum priority is the neutral value for an empty word. -/
def phaseWordMinima (step : State → Input → State)
    (priority : State → Input → H → Fin (C+1)) :
    State → List Input → H → Fin (C+1)
  | _, [], _ => Fin.last C
  | q, input :: rest, h =>
      min (priority q input h) (phaseWordMinima step priority (step q input) rest h)

def phaseMinimumStep (step : State → Input → State)
    (priority : State → Input → H → Fin (C+1))
    (state : State × (H → Fin (C+1))) (input : Input) :
    State × (H → Fin (C+1)) :=
  (step state.1 input, fun h => min (state.2 h) (priority state.1 input h))

theorem phaseMinimumRun_accumulator (step : State → Input → State)
    (priority : State → Input → H → Fin (C+1))
    (word : List Input) (initial : State) (old : H → Fin (C+1)) :
    word.foldl (phaseMinimumStep step priority) (initial, old) =
      (word.foldl step initial, fun h => min (old h) (phaseWordMinima step priority initial word h)) := by
  induction word generalizing initial old with
  | nil =>
    simp only [List.foldl_nil, phaseWordMinima]
    congr 1
    funext h
    exact (min_eq_left (Fin.le_last (old h))).symm
  | cons input rest ih =>
    simp only [List.foldl_cons, phaseMinimumStep]
    rw [ih]
    simp only [phaseWordMinima, min_assoc]

theorem phaseMinimumRun_exact (step : State → Input → State)
    (priority : State → Input → H → Fin (C+1)) (initial : State) (word : List Input) :
    word.foldl (phaseMinimumStep step priority) (initial, fun _ => Fin.last C) =
      (word.foldl step initial, phaseWordMinima step priority initial word) := by
  rw [phaseMinimumRun_accumulator]
  congr 1
  funext h
  exact min_eq_right (Fin.le_last _)

variable [Fintype State] [Fintype Input] [Fintype H] [DecidableEq H] [DecidableEq Outcome]

/-- Compute offers with one complete vector of phase minima. The collector
gets the minima through the current round, including its closing output. -/
def phaseOffersWithMinima (step : State → Input → State) (initial : State)
    (priority : State → Input → H → Fin (C+1))
    (collect : State → Input → (H → Fin (C+1)) → Finset Outcome) : Finset Outcome :=
  finitePhaseOffers (phaseMinimumStep step priority) (initial, fun _ => Fin.last C)
    (fun state input => collect state.1 input
      (fun h => min (state.2 h) (priority state.1 input h)))

omit [Fintype State] [Fintype Input] [Fintype H] [DecidableEq H] in
theorem phaseWordMinima_append (step : State → Input → State)
    (priority : State → Input → H → Fin (C+1)) (initial : State)
    (word : List Input) (input : Input) :
    phaseWordMinima step priority initial (word ++ [input]) =
      fun h => min (phaseWordMinima step priority initial word h)
        (priority (word.foldl step initial) input h) := by
  have run := phaseMinimumRun_exact step priority initial (word ++ [input])
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at run
  rw [phaseMinimumRun_exact] at run
  exact (congrArg Prod.snd run).symm

/-- Each whole outcome has one actual input word witnessing every source
minimum simultaneously. Conversely, every collected outcome is offered. -/
theorem phaseOffersWithMinima_exact (step : State → Input → State) (initial : State)
    (priority : State → Input → H → Fin (C+1))
    (collect : State → Input → (H → Fin (C+1)) → Finset Outcome) (outcome : Outcome) :
    outcome ∈ phaseOffersWithMinima step initial priority collect ↔
      ∃ word : List Input, ∃ input,
        outcome ∈ collect (word.foldl step initial) input
          (phaseWordMinima step priority initial (word ++ [input])) := by
  simp only [phaseOffersWithMinima, mem_finitePhaseOffers_iff, phaseMinimumRun_exact,
    phaseWordMinima_append]

end
end Characterisation
