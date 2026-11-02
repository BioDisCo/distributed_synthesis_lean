/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.JournalCheckers
import DistributedSynthesis.Library.Automata.TreeNonemptiness

/-! # Executable no-direct-reversal synthesis for parity objectives

This module composes checker construction, label enumeration, and finite tree
nonemptiness. It takes concrete finite parity-automaton data, not an LTL formula
or an encoded instance. The Boolean algorithm has no solver/certificate input.
-/

namespace DistributedSynthesis.NoDirectDecision

variable {In₁ In₂ Out₁ Out₂ : Type}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable (A : DetParityAutomaton.{0, 0} (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [DecidableEq A.State]

def decideRealizable : Decidable (NoDirectJournal.Realizable A) := by
  letI : DecidableEq (JournalCheckers.noDirect A).State :=
    JournalCheckers.stateDecidableEq A.reversalForgiving
  letI := TreeNonemptiness.nonemptyDecidable (JournalCheckers.noDirect A)
  exact decidable_of_iff
    (∃ tree, (JournalCheckers.noDirect A).toRunAutomaton.acceptsTree tree)
    (JournalCheckers.realizable_iff_nonempty A).symm

def solve : Bool := @decide (NoDirectJournal.Realizable A) (decideRealizable A)

theorem solve_correct : solve A = true ↔ NoDirectJournal.Realizable A := by
  unfold solve
  exact @decide_eq_true_iff _ (decideRealizable A)

end DistributedSynthesis.NoDirectDecision
