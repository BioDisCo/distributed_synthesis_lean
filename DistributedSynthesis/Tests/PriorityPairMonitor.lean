/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.PriorityPairMonitor

namespace DistributedSynthesis.Tests.PriorityPairMonitor

open DistributedSynthesis.PriorityPairMonitor

/-- Exercise a concrete stable even cycle in the actual compiled monitor.
Only three transitions are evaluated; no global state-space search is needed. -/
private def stableEvenPair (a b : Nat) : Bool :=
  let s := run a b (fun _ => a) (fun _ => b) 2
  decide (update a b s (a, b) = s) && decide (priority a b s (a, b) % 2 = 0)

/-- info: true -/
#guard_msgs in
#eval stableEvenPair 0 1

/-- info: true -/
#guard_msgs in
#eval stableEvenPair 1 0

-- The four-state echo table expands to a large numeric Muller compilation;
-- check its negative case through the proved bridge instead of enumerating it.
example (b₁ b₂ : Nat) (h₁ : 1 ≤ b₁) (h₂ : 1 ≤ b₂) :
    ¬ NatSeqMinEvenParity (combined b₁ b₂ (fun _ => 1) (fun _ => 1)) := by
  rw [combined_correct (fun _ => h₁) (fun _ => h₂), or_self]
  exact not_natSeqMinEvenParity_of_eventually_one _ 0 (fun _ _ => rfl)

end DistributedSynthesis.Tests.PriorityPairMonitor
