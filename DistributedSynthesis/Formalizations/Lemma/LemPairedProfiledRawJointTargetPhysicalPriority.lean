/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointTargetBlockHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPhysicalScanPriority

/-!
# Physical block minima for target-parametric raw-joint controllers

Sender narrowing may change the certificate target carried by a block letter.
The target monitor deliberately promises only the two facts that survive that
narrowing: the emitted target is an allowed successor and its profiled erasure
is the literal physical close.  Those facts already suffice to identify the
target priority with the minimum priority of the physical block prefix.

In particular, nothing in this file identifies an emitted target with the
activation's pre-narrowing target function or with a canonical close key.
-/

namespace DistributedSynthesis

universe u v x y s t

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Literal physical prefixes -/

def profiledRawJointTargetRightPhysicalPrefixRecords
    {Target : Type t}
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map fun record ↦
    pairedRightRecordForRow row
      (profiledRawJointTargetRightPhysicalLetter A record)

def profiledRawJointTargetLeftPhysicalPrefixRecords
    {Target : Type t}
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map fun record ↦
    pairedLeftRecordForRow row
      (profiledRawJointTargetLeftPhysicalLetter A record)

/-! ## Exact monitor scan folds -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
theorem profiledRawJointTargetRightBlockMonitor_run_scan_eq_physicalFold
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁) :
    ∀ n : Nat,
    ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
      source).run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointTargetRightPhysicalLetter A)).foldl
        (pairedRightScanStep A) (pairedRightScanInitial A source.1.1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      change pairedRightScanStep A
          (((profiledRawJointTargetRightBlockMonitor A Target targetState
            Allowed source).run play n).2.1)
          (profiledRawJointTargetRightPhysicalLetter A (play n)) = _
      rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
      rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
theorem profiledRawJointTargetLeftBlockMonitor_run_scan_eq_physicalFold
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂) :
    ∀ n : Nat,
    ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
      source).run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointTargetLeftPhysicalLetter A)).foldl
        (pairedLeftScanStep A) (pairedLeftScanInitial A source.1.1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      change pairedLeftScanStep A
          (((profiledRawJointTargetLeftBlockMonitor A Target targetState
            Allowed source).run play n).2.1)
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) = _
      rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
      rfl

/-! ## The emitted target priority is the physical block minimum -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
theorem profiledRawJointTargetRight_targetPriority_eq_blockMin_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    pairedProfiledEntryPriority A
        (targetState ((play n).2.1.target row)) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row source.1.1)
          (profiledRawJointTargetRightPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  let target := targetState ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetRightPhysicalLetter A)
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A targetState
    Allowed source play hwin n row
  have hpriority :=
    pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq A
      target
      (((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
        source).run play n).2.1)
      row (profiledRawJointTargetRightPhysicalLetter A (play n)) hsafe.1
  have hscan :=
    profiledRawJointTargetRightBlockMonitor_run_scan_eq_physicalFold A
      targetState Allowed source play n
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  rw [hscan] at hpriority
  calc
    pairedProfiledEntryPriority A
        (targetState ((play n).2.1.target row)) =
        A.priority
          (pairedRightScanPairForRow A row
            (letters.foldl (pairedRightScanStep A)
              (pairedRightScanInitial A source.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointTargetRightPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
theorem profiledRawJointTargetLeft_targetPriority_eq_blockMin_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    pairedProfiledEntryPriority A
        (targetState ((play n).2.1.target row)) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row source.1.1)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  let target := targetState ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetLeftPhysicalLetter A)
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A targetState
    Allowed source play hwin n row
  have hpriority :=
    pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq A
      target
      (((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source).run play n).2.1)
      row (profiledRawJointTargetLeftPhysicalLetter A (play n)) hsafe.1
  have hscan :=
    profiledRawJointTargetLeftBlockMonitor_run_scan_eq_physicalFold A
      targetState Allowed source play n
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  rw [hscan] at hpriority
  calc
    pairedProfiledEntryPriority A
        (targetState ((play n).2.1.target row)) =
        A.priority
          (pairedLeftScanPairForRow A row
            (letters.foldl (pairedLeftScanStep A)
              (pairedLeftScanInitial A source.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointTargetLeftPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

end

end DetParityAutomaton

end DistributedSynthesis
