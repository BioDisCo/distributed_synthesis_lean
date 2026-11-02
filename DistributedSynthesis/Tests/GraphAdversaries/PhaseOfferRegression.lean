/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseOfferMinima

/-! Two regressions for exact offers: entries must share a word, and the
accumulated minimum must be included in the reachability state. -/
namespace Characterisation

private def diagonalOffers : Finset (Bool × Bool) :=
  finitePhaseOffers (fun (_ : Unit) (_ : Bool) => ()) ()
    (fun _ b => {(b,b)})

/-- Both component values are possible separately, but their incompatible
combination is not a joint offer. -/
theorem phaseOffers_keep_joint_witness :
    (false,false) ∈ diagonalOffers ∧ (true,true) ∈ diagonalOffers ∧
    (false,true) ∉ diagonalOffers := by decide

private def examplePriority (_ : Unit) (input : Bool) (_ : Unit) : Fin 2 :=
  if input then 0 else 1

private def exampleMinimumOffers : Finset (Bool × Fin 2) :=
  phaseOffersWithMinima (fun (_ : Unit) (_ : Bool) => ()) () examplePriority
    (fun _ input minimum => {(input,minimum ())})

/-- The same current input and original control can occur with different
whole-phase minima. The search includes both, including a zero seen before
the current odd-priority round. -/
theorem phaseOffers_retain_earlier_minimum :
    (false,0) ∈ exampleMinimumOffers ∧ (false,1) ∈ exampleMinimumOffers ∧
    examplePriority () false () = 1 := by decide

end Characterisation
