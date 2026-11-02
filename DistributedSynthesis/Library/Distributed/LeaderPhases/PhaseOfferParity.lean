/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseOfferMinima
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderProgressRealization

/-! Connect the finite priority accumulator to the physical block minima
used by the existing global handover theorem. Every physical round of the
segment, including its last round, contributes to the recorded minimum. -/
namespace Characterisation
open DistributedSynthesis

variable {State Input H : Type} {C : Nat}

theorem phaseWordMinima_branchNode (step : State → Input → State)
    (priority : State → Input → H → Fin (C+1)) (initial : State)
    (env : Nat → Input) (n : Nat) (h : H) :
    (phaseWordMinima step priority initial (branchNode env (n+1)) h).val =
      rangeMin (fun t => (priority ((branchNode env t).foldl step initial) (env t) h).val) 0 n := by
  induction n with
  | zero =>
    simp only [branchNode, phaseWordMinima, List.nil_append, List.foldl_nil, rangeMin,
      min_eq_left (Fin.le_last _)]
  | succ n ih =>
    rw [branchNode, phaseWordMinima_append]
    change min _ _ = _
    rw [ih, rangeMin]
    simp only [Nat.zero_add]

/-- Alignment is required at each actual physical position. No equality
between words of different lengths or stuttering assumption is used. -/
theorem phaseWordMinima_cutBlockMin (step : State → Input → State)
    (priority : State → Input → H → Fin (C+1)) (initial : State)
    (env : Nat → Input) (physicalPriority cuts : Nat → Nat) (k : Nat) (h : H)
    (advances : cuts k < cuts (k+1))
    (aligned : ∀ i, i < cuts (k+1) - cuts k →
      (priority ((branchNode env i).foldl step initial) (env i) h).val =
        physicalPriority (cuts k + i)) :
    (phaseWordMinima step priority initial
      (branchNode env (cuts (k+1) - cuts k)) h).val =
      cutBlockMin physicalPriority cuts k := by
  have size : cuts (k+1) - cuts k = (cuts (k+1) - cuts k - 1) + 1 := by omega
  rw [size, phaseWordMinima_branchNode]
  unfold cutBlockMin
  apply rangeMin_congr
  intro i within
  simp only [Nat.zero_add]
  exact aligned i (by omega)

end Characterisation
