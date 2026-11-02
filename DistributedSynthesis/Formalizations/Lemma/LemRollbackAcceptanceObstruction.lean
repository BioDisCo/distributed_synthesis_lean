/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-!
# Rollback acceptance obstruction

Forward-path parity is not preserved by inserting cancelling backward
crossings.  The concrete two-state bounce below repeatedly traverses the
first edge of an accepting directed ray in both directions, yet has odd
minimum recurring priority.  Consequently a rollback-aware controller needs
an additional cycle certificate; exact undirected adjacency and stack
cancellation alone are insufficient.
-/

namespace DistributedSynthesis

/-- The first edge of the ray has odd priority; all later states have even
priority. -/
def rollbackObstructionPriority (state : Nat) : Nat :=
  if state < 2 then 1 else 0

/-- Genuine forward execution of the ray. -/
def rollbackObstructionForwardState (n : Nat) : Nat :=
  n

/-- Infinite traversal and rollback of the first ray edge. -/
def rollbackObstructionBounceState (n : Nat) : Nat :=
  n % 2

/-- Abstract non-neutral exact-parent step on the successor ray. -/
def RollbackObstructionExactStep (current next : Nat) : Prop :=
  next = current + 1 ∨ current = next + 1

theorem rollbackObstructionForward_step (n : Nat) :
    RollbackObstructionExactStep (rollbackObstructionForwardState n)
      (rollbackObstructionForwardState (n + 1)) := by
  exact Or.inl rfl

/-- Every bounce step is either the forward first edge or its exact
rollback. -/
theorem rollbackObstructionBounce_step (n : Nat) :
    RollbackObstructionExactStep (rollbackObstructionBounceState n)
      (rollbackObstructionBounceState (n + 1)) := by
  unfold RollbackObstructionExactStep rollbackObstructionBounceState
  omega

/-- Each rollback cancels the preceding forward crossing at the level of
states. -/
theorem rollbackObstructionBounce_twoStep (n : Nat) :
    rollbackObstructionBounceState (n + 2) =
      rollbackObstructionBounceState n := by
  simp [rollbackObstructionBounceState, Nat.add_mod]

/-- The directed ray is accepting: after its two-state odd prefix, priority
zero occurs forever. -/
theorem rollbackObstructionForward_minEven :
    NatSeqMinEvenParity (fun n ↦
      rollbackObstructionPriority (rollbackObstructionForwardState n)) := by
  refine ⟨0, ⟨0, by norm_num⟩, ?_, ?_⟩
  · intro n
    refine ⟨max n 2, Nat.le_max_left _ _, ?_⟩
    simp [rollbackObstructionPriority, rollbackObstructionForwardState]
  · intro q hq
    exact Nat.zero_le q

/-- The cancelling bounce is rejecting because it sees only priority one. -/
theorem rollbackObstructionBounce_not_minEven :
    ¬ NatSeqMinEvenParity (fun n ↦
      rollbackObstructionPriority (rollbackObstructionBounceState n)) := by
  apply not_natSeqMinEvenParity_of_eventually_one _ 0
  intro n hn
  simp [rollbackObstructionPriority, rollbackObstructionBounceState,
    Nat.mod_lt n (by omega : 0 < 2)]

end DistributedSynthesis
