/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPhysicalScanPriority

/-!
# Physical block minima for root-pinned guarded-first targets

The guarded-first monitors already check the target emitted by the narrowed
controller against the literal physical close at every row.  Their scan
coordinate is the fold of those same physical letters.  Consequently the
active slot of the target emitted at any finite prefix carries exactly the
minimum original-DPA priority of that prefix.

This statement concerns the actual monitor play.  It neither compares that
play with a separately selected policy-bank record list nor assumes a
canonical representative of the same incidence code.
-/

namespace DistributedSynthesis

universe u v x y s w

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

def profiledRawJointGuardedFirstRightPhysicalPrefixRecords
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map fun record ↦
    pairedRightRecordForRow row
      (profiledRawJointGuardedFirstRightPhysicalLetter A record)

def profiledRawJointGuardedFirstLeftPhysicalPrefixRecords
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map fun record ↦
    pairedLeftRecordForRow row
      (profiledRawJointGuardedFirstLeftPhysicalLetter A record)

/-! ## Exact scan folds -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointGuardedFirstRightBlockMonitor_run_scan_eq_physicalFold
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁) :
    ∀ n : Nat,
    ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s, w}
      A strategy initial
      RootPred package source).run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointGuardedFirstRightPhysicalLetter A)).foldl
        (pairedRightScanStep A) (pairedRightScanInitial A source.1.1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      change pairedRightScanStep A
          (((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s, w}
            A strategy initial
            RootPred package source).run play n).2.1)
          (profiledRawJointGuardedFirstRightPhysicalLetter A (play n)) = _
      rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
      rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointGuardedFirstLeftBlockMonitor_run_scan_eq_physicalFold
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂) :
    ∀ n : Nat,
    ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s, w}
      A strategy initial
      RootPred package source).run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointGuardedFirstLeftPhysicalLetter A)).foldl
        (pairedLeftScanStep A) (pairedLeftScanInitial A source.1.1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      change pairedLeftScanStep A
          (((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s, w}
            A strategy initial
            RootPred package source).run play n).2.1)
          (profiledRawJointGuardedFirstLeftPhysicalLetter A (play n)) = _
      rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
      rfl

/-! ## Universe-free close-and-scan cores -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- An exact right close against an explicitly supplied physical scan is
enough to identify an active target thread and its literal block minimum.
This core deliberately does not mention a monitor state universe. -/
theorem
    exists_profiledRawJointGuardedFirstRightTargetThreadPriority_eq_blockMin_of_close
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)
    (n : Nat) (row : PairedEntryRow) (scan : PairedRightScanState A)
    (hclose :
      erasePairedProfiledState A
          (profiledRawJointGuardedFirstRightTargetProfiledState A
            ((play n).2.1.target row)) =
        pairedRightCloseTarget A scan row
          (profiledRawJointGuardedFirstRightPhysicalLetter A (play n)))
    (hscan : scan =
      ((omegaPrefix play n).map
          (profiledRawJointGuardedFirstRightPhysicalLetter A)).foldl
        (pairedRightScanStep A) (pairedRightScanInitial A source.1.1)) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot ∧
        profiledRawJointThreadRootPriority A (.inr slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.1.1)
              (profiledRawJointGuardedFirstRightPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  obtain ⟨slot, hslot⟩ : ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot := by
    cases hslot : ((play n).2.1.target row).1.family.left () with
    | none =>
        simp [profiledRawJointGuardedFirstRightTargetProfiledState, hslot,
          erasePairedProfiledState, pairedRightCloseTarget] at hclose
    | some slot => exact ⟨slot, rfl⟩
  refine ⟨slot, hslot, ?_⟩
  let target := profiledRawJointGuardedFirstRightTargetProfiledState A
    ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointGuardedFirstRightPhysicalLetter A)
  have htarget : target = .inr (.inr slot) :=
    profiledRawJointGuardedFirstRightTargetProfiledState_eq_of_active_slot A
      ((play n).2.1.target row) slot hslot
  have hpriority :=
    pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq A
      target scan row
        (profiledRawJointGuardedFirstRightPhysicalLetter A (play n)) hclose
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  rw [hscan] at hpriority
  calc
    profiledRawJointThreadRootPriority A (.inr slot) =
        pairedProfiledEntryPriority A target := by rw [htarget]; rfl
    _ = A.priority
          (pairedRightScanPairForRow A row
            (letters.foldl (pairedRightScanStep A)
              (pairedRightScanInitial A source.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointGuardedFirstRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointGuardedFirstRightPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left/right mirror of the universe-free close-and-scan core. -/
theorem
    exists_profiledRawJointGuardedFirstLeftTargetThreadPriority_eq_blockMin_of_close
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)
    (n : Nat) (row : PairedEntryRow) (scan : PairedLeftScanState A)
    (hclose :
      erasePairedProfiledState A
          (profiledRawJointGuardedFirstLeftTargetProfiledState A
            ((play n).2.1.target row)) =
        pairedLeftCloseTarget A scan row
          (profiledRawJointGuardedFirstLeftPhysicalLetter A (play n)))
    (hscan : scan =
      ((omegaPrefix play n).map
          (profiledRawJointGuardedFirstLeftPhysicalLetter A)).foldl
        (pairedLeftScanStep A) (pairedLeftScanInitial A source.1.1)) :
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot ∧
        profiledRawJointThreadRootPriority A (.inl slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.1.1)
              (profiledRawJointGuardedFirstLeftPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  obtain ⟨slot, hslot⟩ : ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot := by
    cases hslot : ((play n).2.1.target row).1.family.right () with
    | none =>
        simp [profiledRawJointGuardedFirstLeftTargetProfiledState, hslot,
          erasePairedProfiledState, pairedLeftCloseTarget] at hclose
    | some slot => exact ⟨slot, rfl⟩
  refine ⟨slot, hslot, ?_⟩
  let target := profiledRawJointGuardedFirstLeftTargetProfiledState A
    ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointGuardedFirstLeftPhysicalLetter A)
  have htarget : target = .inr (.inl slot) :=
    profiledRawJointGuardedFirstLeftTargetProfiledState_eq_of_active_slot A
      ((play n).2.1.target row) slot hslot
  have hpriority :=
    pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq A target
      scan row (profiledRawJointGuardedFirstLeftPhysicalLetter A (play n))
        hclose
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.1.1 letters)
  rw [hscan] at hpriority
  calc
    profiledRawJointThreadRootPriority A (.inl slot) =
        pairedProfiledEntryPriority A target := by rw [htarget]; rfl
    _ = A.priority
          (pairedLeftScanPairForRow A row
            (letters.foldl (pairedLeftScanStep A)
              (pairedLeftScanInitial A source.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointGuardedFirstLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointGuardedFirstLeftPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

/-! ## Active target thread priority equals the actual block minimum -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    exists_profiledRawJointGuardedFirstRightTargetThreadPriority_eq_blockMin_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)
    (hwin : (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s, w}
      A strategy initial
      RootPred package source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot ∧
        profiledRawJointThreadRootPriority A (.inr slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.1.1)
              (profiledRawJointGuardedFirstRightPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  let base := profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s, w}
    A strategy initial RootPred package source
  have hbaseRestart : (base.restartAt base.initial).WinsPlay play := by
    simpa [base, BlockRecordMonitor.restartAt] using hwin
  have hsafeNext := base.restartAt_safe_of_wins
    (fun state ↦ state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    base.initial play hbaseRestart (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [base, profiledRawJointGuardedFirstRightBlockMonitor,
    BlockRecordMonitor.restartAt, Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  have hsafe := hsafeNext.2 row
  obtain ⟨slot, hslot⟩ : ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot := by
    cases hslot : ((play n).2.1.target row).1.family.left () with
    | none =>
        simp [profiledRawJointGuardedFirstRightTargetProfiledState, hslot,
          erasePairedProfiledState, pairedRightCloseTarget] at hsafe
    | some slot => exact ⟨slot, rfl⟩
  refine ⟨slot, hslot, ?_⟩
  let target := profiledRawJointGuardedFirstRightTargetProfiledState A
    ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointGuardedFirstRightPhysicalLetter A)
  have htarget : target = .inr (.inr slot) :=
    profiledRawJointGuardedFirstRightTargetProfiledState_eq_of_active_slot A
      ((play n).2.1.target row) slot hslot
  have hpriority :=
    pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq A
      target
      ((base.run play n).2.1)
      row (profiledRawJointGuardedFirstRightPhysicalLetter A (play n)) hsafe
  have hscan :=
    profiledRawJointGuardedFirstRightBlockMonitor_run_scan_eq_physicalFold A
      strategy initial RootPred package source play n
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  rw [hscan] at hpriority
  calc
    profiledRawJointThreadRootPriority A (.inr slot) =
        pairedProfiledEntryPriority A target := by rw [htarget]; rfl
    _ = A.priority
          (pairedRightScanPairForRow A row
            (letters.foldl (pairedRightScanStep A)
              (pairedRightScanInitial A source.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointGuardedFirstRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointGuardedFirstRightPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    exists_profiledRawJointGuardedFirstLeftTargetThreadPriority_eq_blockMin_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)
    (hwin : (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s, w}
      A strategy initial
      RootPred package source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot ∧
        profiledRawJointThreadRootPriority A (.inl slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.1.1)
              (profiledRawJointGuardedFirstLeftPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  let base := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s, w}
    A strategy initial RootPred package source
  have hbaseRestart : (base.restartAt base.initial).WinsPlay play := by
    simpa [base, BlockRecordMonitor.restartAt] using hwin
  have hsafeNext := base.restartAt_safe_of_wins
    (fun state ↦ state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    base.initial play hbaseRestart (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [base, profiledRawJointGuardedFirstLeftBlockMonitor,
    BlockRecordMonitor.restartAt, Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  have hsafe := hsafeNext.2 row
  obtain ⟨slot, hslot⟩ : ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot := by
    cases hslot : ((play n).2.1.target row).1.family.right () with
    | none =>
        simp [profiledRawJointGuardedFirstLeftTargetProfiledState, hslot,
          erasePairedProfiledState, pairedLeftCloseTarget] at hsafe
    | some slot => exact ⟨slot, rfl⟩
  refine ⟨slot, hslot, ?_⟩
  let target := profiledRawJointGuardedFirstLeftTargetProfiledState A
    ((play n).2.1.target row)
  let letters := (omegaPrefix play n).map
    (profiledRawJointGuardedFirstLeftPhysicalLetter A)
  have htarget : target = .inr (.inl slot) :=
    profiledRawJointGuardedFirstLeftTargetProfiledState_eq_of_active_slot A
      ((play n).2.1.target row) slot hslot
  have hpriority :=
    pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq A target
      ((base.run play n).2.1)
      row (profiledRawJointGuardedFirstLeftPhysicalLetter A (play n)) hsafe
  have hscan :=
    profiledRawJointGuardedFirstLeftBlockMonitor_run_scan_eq_physicalFold A
      strategy initial RootPred package source play n
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.1.1 letters)
  rw [hscan] at hpriority
  calc
    profiledRawJointThreadRootPriority A (.inl slot) =
        pairedProfiledEntryPriority A target := by rw [htarget]; rfl
    _ = A.priority
          (pairedLeftScanPairForRow A row
            (letters.foldl (pairedLeftScanStep A)
              (pairedLeftScanInitial A source.1.1))).2 := hpriority
    _ = A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointGuardedFirstLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters,
        profiledRawJointGuardedFirstLeftPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

end

end DetParityAutomaton

end DistributedSynthesis
