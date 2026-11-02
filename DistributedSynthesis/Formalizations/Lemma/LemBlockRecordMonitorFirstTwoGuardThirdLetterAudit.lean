/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlockRecordMonitorFirstTwoLetterGuard

/-!
# A two-letter guard does not determine a longer literal block

The heterogeneous literal tables use `firstTwoLetterGuard`.  This is exactly
enough for their one-step seam laws, but it cannot imply equality with an
independently chosen ordinary-policy word at offsets `j >= 2`.

The example below is deliberately objective-free.  Both words have the same
first two records and both win the same guarded monitor, while their third
records differ.  Consequently a later proof of a full
`CanonicalTraceAlignment.emittedRoundAt` field for blocks of length at least
three must use a new all-prefix coupling.  It cannot be obtained from the
present first-two guard or from `memberController_base_wins` alone.
-/

namespace DistributedSynthesis

namespace BlockRecordMonitor

/-- A one-state monitor accepting every Boolean-output block word. -/
def firstTwoThirdAuditBase : BlockRecordMonitor Unit Unit Bool Unit where
  State := Unit
  stateFinite := inferInstance
  initial := ()
  step := fun _ _ => ()
  priority := fun _ => 0

/-- The strengthened monitor tests no property beyond its two inert prefix
checks. -/
noncomputable def firstTwoThirdAuditGuard :
    BlockRecordMonitor Unit Unit Bool Unit :=
  firstTwoThirdAuditBase.firstTwoLetterGuard (fun _ => true)
    (fun _ _ => true)

/-- Two words differing only in their third receiver output. -/
def firstTwoThirdAuditWord (third : Bool) :
    Nat → RealizedBlockRound Unit Unit Bool Unit :=
  fun n => (((), ()), if n = 2 then third else false, ())

@[simp] theorem firstTwoThirdAuditWord_zero (third : Bool) :
    firstTwoThirdAuditWord third 0 = (((), ()), false, ()) := by
  simp [firstTwoThirdAuditWord]

@[simp] theorem firstTwoThirdAuditWord_one (third : Bool) :
    firstTwoThirdAuditWord third 1 = (((), ()), false, ()) := by
  simp [firstTwoThirdAuditWord]

@[simp] theorem firstTwoThirdAuditWord_two (third : Bool) :
    firstTwoThirdAuditWord third 2 = (((), ()), third, ()) := by
  simp [firstTwoThirdAuditWord]

/-- Every audit word wins: after the two true prefix checks the guard is
inert, and the base priority is constantly even. -/
theorem firstTwoThirdAuditGuard_wins (third : Bool) :
    firstTwoThirdAuditGuard.WinsPlay (firstTwoThirdAuditWord third) := by
  unfold WinsPlay
  have hsafe : ∀ n,
      (firstTwoThirdAuditGuard.run (firstTwoThirdAuditWord third) n).safe =
        true := by
    exact firstTwoThirdAuditBase.firstTwoLetterGuard_run_safe_of_allowed
      (fun _ => true) (fun _ _ => true) (firstTwoThirdAuditWord third) rfl rfl
  have hpriority :
      (fun n => firstTwoThirdAuditGuard.priority
        (firstTwoThirdAuditGuard.run (firstTwoThirdAuditWord third) n)) =
          fun _ => 2 := by
    funext n
    change (if
      (firstTwoThirdAuditGuard.run (firstTwoThirdAuditWord third) n).safe
      then 0 + 2 else 1) = 2
    rw [hsafe n]
    rfl
  rw [hpriority]
  refine ⟨2, ⟨1, rfl⟩, ?_, ?_⟩
  · intro n
    exact ⟨n, le_rfl, rfl⟩
  · intro q hq
    obtain ⟨k, _, hk⟩ := hq 0
    change 2 = q at hk
    omega

/-- Kernel-checked fail-fast verdict: winning the same two-letter guard and
agreeing on its complete checked prefix do not determine the next record. -/
theorem firstTwoLetterGuard_does_not_determine_third_record :
    ¬ (∀ left right : Nat → RealizedBlockRound Unit Unit Bool Unit,
      firstTwoThirdAuditGuard.WinsPlay left →
      firstTwoThirdAuditGuard.WinsPlay right →
      left 0 = right 0 → left 1 = right 1 → left 2 = right 2) := by
  intro hdet
  have hthird := hdet (firstTwoThirdAuditWord false)
    (firstTwoThirdAuditWord true)
    (firstTwoThirdAuditGuard_wins false)
    (firstTwoThirdAuditGuard_wins true) (by simp) (by simp)
  simp at hthird

end BlockRecordMonitor

end DistributedSynthesis
