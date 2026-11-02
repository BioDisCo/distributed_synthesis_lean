/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ContinuationParity

/-! Winning residual membership alone cannot justify repeated leader
reselection. This counterexample concerns parity, without any uncertainty
about inputs or graph observations. -/
namespace Characterisation
open DistributedSynthesis

/-- A plan that meets its parity obligation after a finite delay. -/
def delayedEvenPlan (delay t : Nat) : Nat := if t < delay then 1 else 0

theorem delayedEvenPlan_wins (delay : Nat) :
    NatSeqMinEvenParity (delayedEvenPlan delay) := by
  refine ⟨0,⟨0,rfl⟩,?_,fun _ _ => Nat.zero_le _⟩
  intro n
  refine ⟨max n delay,le_max_left _ _,?_⟩
  exact if_neg (Nat.not_lt.mpr (le_max_right _ _))

/-- At round t select a winning plan that postpones the even priority
until t+1, and execute only its current output. Every selected plan wins;
the resulting physical run loses. No rounds have been deleted or moved. -/
theorem winning_restarts_can_lose :
    (∀ t, NatSeqMinEvenParity (delayedEvenPlan (t+1))) ∧
      ¬ NatSeqMinEvenParity (fun t => delayedEvenPlan (t+1) t) := by
  refine ⟨fun t => delayedEvenPlan_wins (t+1),?_⟩
  rintro ⟨p,even,seen,_⟩
  obtain ⟨t,_,eq⟩ := seen 0
  have one : p = 1 := by simpa [delayedEvenPlan] using eq.symm
  obtain ⟨m,hm⟩ := even
  omega

end Characterisation
