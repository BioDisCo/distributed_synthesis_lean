/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteReceiveStateAwareController
import DistributedSynthesis.Formalizations.Lemma.LemReceiptMemoryLocalRepair

/-!
# Receipt-memory repair through exact state-aware compilation

Receive outputs use the decoded actual predecessor state; the future blind
control records the local receipt event. The compiler maintains the exact
automaton successor, rather than retaining a stale homogeneous scan.
-/

namespace DistributedSynthesis
namespace ReceiptMemoryStateAwareRepair
open DetParityAutomaton FinitePairedMealyController

abbrev A := ReceiptMemoryLocalRepair.objective

def policy : FiniteReceiveStateAwareController Unit Unit Bool Bool A.State where
  OneControl := Bool
  TwoControl := Bool
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := false
  initialTwo := false
  noRecvOne := fun b _ ↦ (false,b)
  noRecvTwo := fun b _ ↦ (false,b)
  recvOne := fun q _ _ _ _ ↦ (true,q.1.1)
  recvTwo := fun q _ _ _ _ ↦ (true,q.1.2)

theorem policy_step (bits : Bool × Bool) (e : EnvironmentRound Unit Unit) :
    policy.globalStep A (bits,(bits,true)) e =
      (receiptBits e.graph,(receiptBits e.graph,true)) := by
  rcases bits with ⟨one,two⟩
  rcases e with ⟨i,j,g⟩
  cases one <;> cases two <;> cases g <;> rfl

theorem policy_trace (env : EnvironmentSequence Unit Unit) (n : Nat) :
    policy.globalTrace A env n =
      (previousReceiptBits env n,(previousReceiptBits env n,true)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [FiniteReceiveStateAwareController.globalTrace, ih]
    exact policy_step (previousReceiptBits env n) (env n)

theorem policy_wins (env : EnvironmentSequence Unit Unit) : A.Accepts (policy.word A env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  intro N
  refine ⟨N, le_rfl, ?_⟩
  change A.priority (A.run (policy.word A env) N) = 0
  rw [← policy.globalTrace_state A env N, policy_trace]
  rfl

/-- The same finite implementation wins both mirrored receipt tests on
arbitrary graph sequences, with exact actual-state tracking supplied by the
compiler, not by the old owner's target certificate. -/
theorem compiled_physical_wins (env : EnvironmentSequence Unit Unit) :
    let C := (policy.compile A).mooreize
    A.Accepts (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) :=
  policy.compile_physical_accepts A policy_wins env

end ReceiptMemoryStateAwareRepair
end DistributedSynthesis
