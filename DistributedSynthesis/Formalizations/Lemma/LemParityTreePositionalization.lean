/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-!
# Joint positionalization of finite parity prescription trees

For a finite state space, finite move alphabet, and finite directions, an
accepting history-dependent prescription tree can be replaced by one move
per state. Unlike safety representative selection, this uses the checked
parity-game theorem: arbitrary representatives need not preserve parity.
-/

namespace DistributedSynthesis
namespace ParityPrescription

universe s m d
variable {State : Type s} {Move : Type m} {Direction : Type d}
variable [Fintype State] [Fintype Move] [Fintype Direction]

def automaton (initial : State) (next : State → Move → Direction → State)
    (priority : State → Nat) : RunParityTreeAutomaton Direction Move where
  State := State
  stateFinite := inferInstance
  initial := initial
  delta := fun q move children ↦ ∀ direction, children direction = next q move direction
  priority := priority

def stateAt (initial : State) (next : State → Move → Direction → State)
    (policy : State → Move) (node : List Direction) : State :=
  node.foldl (fun q direction ↦ next q (policy q) direction) initial

omit [Fintype State] [Fintype Move] [Fintype Direction] in
theorem stateAt_append (initial : State) (next : State → Move → Direction → State)
    (policy : State → Move) (node : List Direction) (direction : Direction) :
    stateAt initial next policy (node ++ [direction]) =
      next (stateAt initial next policy node) (policy (stateAt initial next policy node)) direction := by
  simp [stateAt, List.foldl_append]

/-- A single finite-state policy preserves universal parity. No rank or
common-choice assumption is added to the accepted prescription tree. -/
theorem exists_positional (initial : State) (next : State → Move → Direction → State)
    (priority : State → Nat)
    (haccepts : ∃ tree, (automaton initial next priority).acceptsTree tree) :
    ∃ policy : State → Move, ∀ branch : Nat → Direction,
      NatSeqMinEvenParity (fun n ↦ priority (stateAt initial next policy (branchNode branch n))) := by
  classical
  obtain ⟨tree, run, haccept, hrational⟩ :=
    (automaton initial next priority).exists_transitionRationalRun_accepted haccepts
  let policy : State → Move := fun q ↦
    if h : ∃ node, run node = q then tree (Classical.choose h) else tree []
  have hlabel (node : List Direction) : policy (run node) = tree node := by
    dsimp only [policy]
    rw [dif_pos ⟨node,rfl⟩]
    exact (hrational _ node (Classical.choose_spec (show ∃ u, run u = run node from ⟨node,rfl⟩))).1
  have htrace (node : List Direction) : stateAt initial next policy node = run node := by
    induction node using List.reverseRecOn with
    | nil => exact haccept.1.1.symm
    | append_singleton node direction ih =>
      rw [stateAt_append, ih, hlabel]
      exact (haccept.1.2 node direction).symm
  refine ⟨policy, ?_⟩
  intro branch
  simpa only [htrace] using haccept.2 branch

end ParityPrescription
end DistributedSynthesis
