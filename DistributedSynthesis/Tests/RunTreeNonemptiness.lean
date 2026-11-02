/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.RunTreeNonemptiness

namespace DistributedSynthesis.Tests.RunTreeNonemptiness

private def oneState (legal : Bool) (priority : Nat) : RunParityTreeAutomaton Bool Unit where
  State := Unit
  stateFinite := inferInstance
  initial := ()
  delta _ _ _ := legal = true
  priority _ := priority

private instance (legal : Bool) (priority : Nat) : DecidableEq (oneState legal priority).State :=
  inferInstanceAs (DecidableEq Unit)

private instance (legal : Bool) (priority : Nat) :
    ∀ q l f, Decidable ((oneState legal priority).delta q l f) :=
  fun _ _ _ => inferInstanceAs (Decidable (legal = true))

private def result (legal : Bool) (priority : Nat) : Bool :=
  @decide (∃ t, (oneState legal priority).acceptsTree t)
    ((oneState legal priority).nonemptyDecidable)

#guard result true 0
#guard !result true 1
#guard !result false 0

/-- The root has a transition; every child has none, despite even priorities. -/
private def illegalChild : RunParityTreeAutomaton (Fin 4) Unit where
  State := Bool
  stateFinite := inferInstance
  initial := false
  delta q _ children := q = false ∧ ∀ b, children b = true
  priority _ := 0

private instance : DecidableEq illegalChild.State := inferInstanceAs (DecidableEq Bool)
private instance : ∀ q l f, Decidable (illegalChild.delta q l f) :=
  fun q _ f => inferInstanceAs (Decidable (q = false ∧ ∀ b : Fin 4, f b = true))

-- Exercise the delayed safety check directly, without enumerating all policies.
private def firstChild := illegalChild.transitionMonitor.step
  (false, true) ((), fun _ => true) 0
private def grandchild := illegalChild.transitionMonitor.step
  firstChild ((), fun _ => true) 0

#guard firstChild.2
#guard !grandchild.2
#guard illegalChild.transitionMonitor.priority grandchild == 1

private theorem illegalChild_empty : ¬ ∃ tree, illegalChild.acceptsTree tree := by
  rintro ⟨tree, run, ⟨_, hstep⟩, _⟩
  have hroot : run [] = false ∧ ∀ b : Fin 4, run ([] ++ [b]) = true := hstep []
  have hchild : run [0] = false ∧ ∀ b : Fin 4, run ([0] ++ [b]) = true := hstep [0]
  exact Bool.false_ne_true (hchild.1.symm.trans (hroot.2 0))

example : ¬ ∃ tree, illegalChild.transitionMonitor.toRunAutomaton.acceptsTree tree := by
  intro h
  exact illegalChild_empty (illegalChild.transitionMonitor_nonempty_iff.mp h)

end DistributedSynthesis.Tests.RunTreeNonemptiness
