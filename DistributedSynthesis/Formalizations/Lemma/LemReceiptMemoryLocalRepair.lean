/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyReceiptMemory
import DistributedSynthesis.Formalizations.Lemma.LemReceiptMemoryOwnerObstruction

/-!
# Receipt-memory regression repair and the remaining target obstruction

Adding one local receipt bit suffices for both mirrored safety tests on every
graph word. It does not repair a stale homogeneous scan: the corrected output
has an unsafe successor from that scan's old state. A general repair must
therefore change the represented context as well as the output.
-/

namespace DistributedSynthesis
namespace ReceiptMemoryLocalRepair
open DetParityAutomaton FinitePairedMealyController

abbrev Record := RoundRecord Unit Unit Graph Bool Bool

/-- Both processes must emit their own previous receipt bit. -/
def objective : DetParityAutomaton Record where
  State := (Bool × Bool) × Bool
  stateFinite := inferInstance
  initial := ((false, false), true)
  step := fun q r ↦ (receiptBits r.graph,
    q.2 && decide ((r.outputOne, r.outputTwo) = q.1))
  priority := fun q ↦ if q.2 then 0 else 1

variable (C : FinitePairedMealyController Unit Unit Bool Bool)

/-- Proof-side relation only: each receipt bit belongs to one endpoint. The
sticky safety bit is an automaton annotation, not a shared runtime oracle. -/
def Aligned (q : objective.State)
    (s : C.withReceiptMemory.OneControl × C.withReceiptMemory.TwoControl) : Prop :=
  q = ((s.1.2, s.2.2), true)

theorem aligned_step (q : objective.State)
    (s : C.withReceiptMemory.OneControl × C.withReceiptMemory.TwoControl)
    (e : EnvironmentRound Unit Unit) (h : Aligned C q s) :
    Aligned C (objective.step q (C.withReceiptMemory.semanticRecord s e))
      (C.withReceiptMemory.semanticAdvanceControls s e) := by
  rcases h with rfl
  unfold Aligned
  rw [withReceiptMemory_advance]
  change (receiptBits e.graph, true && decide
    (((C.withReceiptMemory.semanticRecord s e).outputOne,
      (C.withReceiptMemory.semanticRecord s e).outputTwo) = (s.1.2, s.2.2))) = _
  rw [withReceiptMemory_record_outputs]
  simp

/-- A controller installed after a prefix works from that prefix's actual
receipt state, not just from the empty-history initial state. -/
theorem repaired_runFrom (bits : Bool × Bool)
    (env : EnvironmentSequence Unit Unit) (n : Nat) :
    objective.runFrom (bits, true) ((C.withReceiptMemoryFrom bits).semanticWord env) n =
      (receiptBitsFrom bits env n, true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom, ih]
    change (receiptBits (env n).graph, true && decide
      ((((C.withReceiptMemoryFrom bits).semanticWord env n).outputOne,
        ((C.withReceiptMemoryFrom bits).semanticWord env n).outputTwo) =
          receiptBitsFrom bits env n)) = _
    rw [withReceiptMemoryFrom_word_outputs]
    simp [receiptBitsFrom]

theorem repaired_acceptsFrom (bits : Bool × Bool)
    (env : EnvironmentSequence Unit Unit) :
    objective.AcceptsFrom (bits, true) ((C.withReceiptMemoryFrom bits).semanticWord env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  intro N
  refine ⟨N, le_rfl, ?_⟩
  change objective.priority
    (objective.runFrom (bits, true) ((C.withReceiptMemoryFrom bits).semanticWord env) N) = 0
  rw [repaired_runFrom]
  rfl

/-- The actual DPA state agrees with the two stored local receipt bits at
every prefix, and no safety violation occurs. The base controls are arbitrary. -/
theorem repaired_run (env : EnvironmentSequence Unit Unit) (n : Nat) :
    objective.run (C.withReceiptMemory.semanticWord env) n =
      (previousReceiptBits env n, true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih]
    change (receiptBits (env n).graph,
      true && decide (((C.withReceiptMemory.semanticWord env n).outputOne,
        (C.withReceiptMemory.semanticWord env n).outputTwo) =
          previousReceiptBits env n)) = _
    rw [withReceiptMemory_word_outputs]
    simp [previousReceiptBits]

theorem repaired_accepts (env : EnvironmentSequence Unit Unit) :
    objective.Accepts (C.withReceiptMemory.semanticWord env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  intro N
  refine ⟨N, le_rfl, ?_⟩
  change objective.priority (objective.run (C.withReceiptMemory.semanticWord env) N) = 0
  rw [repaired_run]
  rfl

theorem repaired_original_run (env : EnvironmentSequence Unit Unit) (n : Nat) :
    ReceiptMemoryOwnerObstruction.objective.run (C.withReceiptMemory.semanticWord env) n =
      ((previousReceiptBits env n).1, true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih]
    have hout := congrArg Prod.fst (C.withReceiptMemory_word_outputs env n)
    dsimp only at hout
    change (ReceiptMemoryOwnerObstruction.receivesOne (env n).graph,
      true && decide ((C.withReceiptMemory.semanticWord env n).outputOne =
        (previousReceiptBits env n).1)) = _
    rw [hout]
    cases hg : (env n).graph <;>
      simp [previousReceiptBits, receiptBits, ReceiptMemoryOwnerObstruction.receivesOne, hg]

theorem repaired_original_accepts (env : EnvironmentSequence Unit Unit) :
    ReceiptMemoryOwnerObstruction.objective.Accepts (C.withReceiptMemory.semanticWord env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  intro N
  refine ⟨N, le_rfl, ?_⟩
  change ReceiptMemoryOwnerObstruction.objective.priority
    (ReceiptMemoryOwnerObstruction.objective.run (C.withReceiptMemory.semanticWord env) N) = 0
  rw [repaired_original_run]
  rfl

noncomputable section

theorem repaired_physical_acceptsFrom (bits : Bool × Bool)
    (env : EnvironmentSequence Unit Unit) :
    let P := (C.withReceiptMemoryFrom bits).mooreize
    objective.AcceptsFrom (bits, true)
      (P.globalMachine.globalMachineTraceWord P.globalOutputOne P.globalOutputTwo env) := by
  dsimp only
  rw [mooreize_word_eq_semanticWord]
  exact repaired_acceptsFrom C bits env

/-- Verification of the genuine finite physical implementation, including
simultaneous rounds and arbitrarily many direct reversals. -/
theorem repaired_physical_accepts (env : EnvironmentSequence Unit Unit) :
    let P := C.withReceiptMemory.mooreize
    let word := P.globalMachine.globalMachineTraceWord P.globalOutputOne P.globalOutputTwo env
    objective.Accepts word ∧ ReceiptMemoryOwnerObstruction.objective.Accepts word := by
  dsimp only
  rw [mooreize_word_eq_semanticWord]
  exact ⟨repaired_accepts C env, repaired_original_accepts C env⟩

end

/-- The corrected output is safe at the actual post-receipt context, but
unsafe at the homogeneous right scan. This prevents an output-only patch
from retaining that scan's exact safe-target certificate. -/
theorem corrected_output_separates_scan_states (r : Record) (hout : r.outputOne = true) :
    (ReceiptMemoryOwnerObstruction.objective.step (true, true) r).2 = true ∧
    (ReceiptMemoryOwnerObstruction.objective.step (false, true) r).2 = false := by
  simp [ReceiptMemoryOwnerObstruction.objective, hout]

/-- No single safe target can be the exact successor of the stale scan
on the corrected output. This failure is independent of bank size and ranks. -/
theorem no_safe_stale_target (r : Record) (hout : r.outputOne = true)
    (target : ReceiptMemoryOwnerObstruction.objective.State) (hsafe : target.2 = true) :
    ReceiptMemoryOwnerObstruction.objective.step (false, true) r ≠ target := by
  intro heq
  have hbad := (corrected_output_separates_scan_states r hout).2
  rw [heq, hsafe] at hbad
  cases hbad

end ReceiptMemoryLocalRepair
end DistributedSynthesis
