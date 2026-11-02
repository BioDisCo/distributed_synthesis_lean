/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftPolicyHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPhysicalScanPriority

/-!
# Physical block minima carried by raw-joint policy targets

The raw-joint block monitors check literal records emitted by the narrowed
finite controllers.  Their scan coordinate is therefore enough to identify
the priority stored in a checked target with the minimum original-DPA
priority of the actual physical block prefix.

This is the pointwise equality needed later by epoch pasting.  It never
compares the narrowed controller word with a realizing strategy word, and it
does not expose the proof-side orientation or row to a process.
-/

namespace DistributedSynthesis

universe u v x y s

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

/-- Original-DPA records literally emitted by a raw-joint right-controller
prefix at one sticky entry row. -/
def profiledRawJointUnitRightPhysicalPrefixRecords
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode)
      Out₁)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map fun record ↦
    pairedRightRecordForRow row
      (profiledRawJointUnitRightPhysicalLetter A record)

/-- Left-controller mirror. -/
def profiledRawJointUnitLeftPhysicalPrefixRecords
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode)
      Out₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map fun record ↦
    pairedLeftRecordForRow row
      (profiledRawJointUnitLeftPhysicalLetter A record)

/-! ## Exact scan folds -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The right raw monitor's scan is the literal fold of the physical records
seen so far. -/
theorem profiledRawJointUnitRightBlockMonitor_run_scan_eq_physicalFold
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁) :
    ∀ n : Nat,
    ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s}
      A strategy initialCode policy state source).run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointUnitRightPhysicalLetter A)).foldl
        (pairedRightScanStep A) (pairedRightScanInitial A source.1.1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      change pairedRightScanStep A
          (((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy initialCode policy state source).run
              play n).2.1)
          (profiledRawJointUnitRightPhysicalLetter A (play n)) = _
      rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
      rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left scan mirror. -/
theorem profiledRawJointUnitLeftBlockMonitor_run_scan_eq_physicalFold
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂) :
    ∀ n : Nat,
    ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s}
      A strategy initialCode policy state source).run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointUnitLeftPhysicalLetter A)).foldl
        (pairedLeftScanStep A) (pairedLeftScanInitial A source.1.1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      change pairedLeftScanStep A
          (((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy initialCode policy state source).run
              play n).2.1)
          (profiledRawJointUnitLeftPhysicalLetter A (play n)) = _
      rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
      rfl

/-! ## Winning targets carry the physical minimum -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every checked right-controller close exposes the live left slot whose
raw thread priority is exactly the minimum of the literal physical prefix. -/
theorem exists_profiledRawJointUnitRightTargetThreadPriority_eq_blockMin_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁)
    (hwin : (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy initialCode policy source.state
      source.slot).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot ∧
        profiledRawJointThreadRootPriority A (.inr slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.slot.1.1)
              (profiledRawJointUnitRightPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointUnitRight_target_active_slot_of_wins A strategy
      initialCode policy source play hwin n row
  refine ⟨slot, hslot, ?_⟩
  let target := profiledRawJointUnitRightTargetProfiledState A
    ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointUnitRightPhysicalLetter A)
  have htarget : target = .inr (.inr slot) :=
    profiledRawJointUnitRightTargetProfiledState_eq_of_active_slot A
      ((play n).2.1.target row) slot hslot
  have hsafe := profiledRawJointUnitRight_targetsSafe_of_wins A strategy
    initialCode policy source play hwin n row
  have hpriority :=
    pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq A
      target
      (((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy source.state
          source.slot).run play n).2.1)
      row (profiledRawJointUnitRightPhysicalLetter A (play n)) hsafe.1
  have hscan := profiledRawJointUnitRightBlockMonitor_run_scan_eq_physicalFold
    A strategy initialCode policy source.state source.slot play n
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.slot.1.1
      letters)
  rw [hscan] at hpriority
  calc
    profiledRawJointThreadRootPriority A (.inr slot) =
        pairedProfiledEntryPriority A target := by rw [htarget]; rfl
    _ = A.priority
          (pairedRightScanPairForRow A row
            (letters.foldl (pairedRightScanStep A)
              (pairedRightScanInitial A source.slot.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointUnitRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointUnitRightPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-controller mirror. -/
theorem exists_profiledRawJointUnitLeftTargetThreadPriority_eq_blockMin_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂)
    (hwin : (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy initialCode policy source.state
      source.slot).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot ∧
        profiledRawJointThreadRootPriority A (.inl slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.slot.1.1)
              (profiledRawJointUnitLeftPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointUnitLeft_target_active_slot_of_wins A strategy
      initialCode policy source play hwin n row
  refine ⟨slot, hslot, ?_⟩
  let target := profiledRawJointUnitLeftTargetProfiledState A
    ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointUnitLeftPhysicalLetter A)
  have htarget : target = .inr (.inl slot) :=
    profiledRawJointUnitLeftTargetProfiledState_eq_of_active_slot A
      ((play n).2.1.target row) slot hslot
  have hsafe := profiledRawJointUnitLeft_targetsSafe_of_wins A strategy
    initialCode policy source play hwin n row
  have hpriority :=
    pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq A
      target
      (((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy source.state
          source.slot).run play n).2.1)
      row (profiledRawJointUnitLeftPhysicalLetter A (play n)) hsafe.1
  have hscan := profiledRawJointUnitLeftBlockMonitor_run_scan_eq_physicalFold
    A strategy initialCode policy source.state source.slot play n
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.slot.1.1
      letters)
  rw [hscan] at hpriority
  calc
    profiledRawJointThreadRootPriority A (.inl slot) =
        pairedProfiledEntryPriority A target := by rw [htarget]; rfl
    _ = A.priority
          (pairedLeftScanPairForRow A row
            (letters.foldl (pairedLeftScanStep A)
              (pairedLeftScanInitial A source.slot.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointUnitLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointUnitLeftPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

end

end DetParityAutomaton

end DistributedSynthesis
