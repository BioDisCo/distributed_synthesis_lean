/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.NoDirectDecision

namespace DistributedSynthesis.Tests.NoDirectDecision

variable {In₁ In₂ Out₁ Out₂ : Type}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable (A : DetParityAutomaton.{0, 0} (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [DecidableEq A.State]

/-- The client supplies the objective only, not checkers, a tree solver, or a winner. -/
def solve : Bool := DistributedSynthesis.NoDirectDecision.solve A

example : solve A = true ↔ NoDirectJournal.Realizable A :=
  DistributedSynthesis.NoDirectDecision.solve_correct A

example : NoDirectJournal.Realizable A ↔
    ∃ tree, (JournalCheckers.noDirect A).toRunAutomaton.acceptsTree tree :=
  JournalCheckers.realizable_iff_nonempty A

def objective : DetParityAutomaton (RoundRecord Unit Unit Graph Unit Unit) where
  State := Unit
  stateFinite := inferInstance
  initial := ()
  step := fun _ _ => ()
  priority := fun _ => 0

/-- Only response-table enumeration is evaluated, not the enormous Piterman carrier. -/
def labelCount : Nat :=
  letI : DecidableEq objective.State := inferInstanceAs (DecidableEq Unit)
  letI := JournalCheckers.labelFintype objective
  Fintype.card (DetParityAutomaton.GlobalJournalLabel objective)

#guard labelCount = 1

end DistributedSynthesis.Tests.NoDirectDecision
