/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOverlayEpochSlice

/-!
# Literal physical scan and compressed-block priority

The rationalized sender need not reproduce the raw strategy's sender word.
The parity argument therefore has to use the records that the installed
finite controller actually emits.  This file identifies the scan coordinate
of the open monitor with the DPA minimum of those literal records and then
transfers that minimum through a checked closing target.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Checked close targets carry the selected physical minimum -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- An exact right-close erasure equation fixes the profiled target's epoch
priority to the minimum stored in the selected scan row. -/
theorem pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter) :
    pairedProfiledEntryPriority A target =
      A.priority (pairedRightScanPairForRow A row scan).2 := by
  unfold pairedProfiledEntryPriority
  rw [herase]
  cases row <;> rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left close mirror. -/
theorem pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter) :
    pairedProfiledEntryPriority A target =
      A.priority (pairedLeftScanPairForRow A row scan).2 := by
  unfold pairedProfiledEntryPriority
  rw [herase]
  cases row <;> rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Classified-anchor form of the exact right-close priority equation. -/
theorem profiledOpenClassifiedAnchorPriority_eq_rightScanPairForRow_min_of_erase_eq
    (target : ProfiledOpenClassifiedAnchor A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A (target.toProfiledState A) =
      pairedRightCloseTarget A scan row letter) :
    profiledOpenClassifiedAnchorPriority A target =
      A.priority (pairedRightScanPairForRow A row scan).2 := by
  rw [profiledOpenClassifiedAnchorPriority_eq]
  exact pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq A
    target.toProfiledState scan row letter herase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Classified-anchor left-close form. -/
theorem profiledOpenClassifiedAnchorPriority_eq_leftScanPairForRow_min_of_erase_eq
    (target : ProfiledOpenClassifiedAnchor A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A (target.toProfiledState A) =
      pairedLeftCloseTarget A scan row letter) :
    profiledOpenClassifiedAnchorPriority A target =
      A.priority (pairedLeftScanPairForRow A row scan).2 := by
  rw [profiledOpenClassifiedAnchorPriority_eq]
  exact pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq A
    target.toProfiledState scan row letter herase

/-! ## Arbitrary physical-play prefixes -/

/-- The literal original-DPA records selected from a right-oriented realized
play.  In particular the blind output is the output actually emitted by the
finite controller, not an output copied from the realizing strategy. -/
def profiledRightPhysicalPrefixRecords
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map (fun record ↦
    pairedRightRecordForRow row (profiledRightPhysicalLetter A record))

/-- Left-oriented physical prefix records. -/
def profiledLeftPhysicalPrefixRecords
    (row : PairedEntryRow)
    (records : List (RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  records.map (fun record ↦
    pairedLeftRecordForRow row (profiledLeftPhysicalLetter A record))

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A checked right closing target has exactly the minimum priority of the
literal physical prefix preceding the closing letter.  This is valid for an
arbitrary play of the extracted monitor and therefore survives sender
rationalization. -/
theorem pairedProfiledEntryPriority_eq_rightPhysicalPrefixBlockMin_of_close
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (n : Nat) (row : PairedEntryRow)
    (target : PairedProfiledTreeState A)
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A
        (((profiledOpenRightBlockMonitor A code minimum profile).run
          play n).2.1)
        row (profiledRightPhysicalLetter A (play n))) :
    pairedProfiledEntryPriority A target =
      A.priority
        (blockMinState A (pairedCodeStateForRow A row code)
          (profiledRightPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  let letters := (omegaPrefix play n).map
    (profiledRightPhysicalLetter A)
  have hscan :
      ((profiledOpenRightBlockMonitor A code minimum profile).run play n).2.1 =
        letters.foldl (pairedRightScanStep A)
          (pairedRightScanInitial A code) := by
    rw [profiledOpenRightBlockMonitor_run_scan_eq_physicalFold]
    exact List.foldl_map.symm
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row code letters)
  calc
    pairedProfiledEntryPriority A target =
        A.priority
          (pairedRightScanPairForRow A row
            (((profiledOpenRightBlockMonitor A code minimum profile).run
              play n).2.1)).2 :=
      pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq A
        target _ row (profiledRightPhysicalLetter A (play n)) herase
    _ = A.priority
          (pairedRightScanPairForRow A row
            (letters.foldl (pairedRightScanStep A)
              (pairedRightScanInitial A code))).2 := by rw [hscan]
    _ = A.priority
          (blockMinState A (pairedCodeStateForRow A row code)
            (profiledRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters, profiledRightPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left arbitrary-play mirror. -/
theorem pairedProfiledEntryPriority_eq_leftPhysicalPrefixBlockMin_of_close
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (n : Nat) (row : PairedEntryRow)
    (target : PairedProfiledTreeState A)
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A
        (((profiledOpenLeftBlockMonitor A code minimum profile).run
          play n).2.1)
        row (profiledLeftPhysicalLetter A (play n))) :
    pairedProfiledEntryPriority A target =
      A.priority
        (blockMinState A (pairedCodeStateForRow A row code)
          (profiledLeftPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  let letters := (omegaPrefix play n).map
    (profiledLeftPhysicalLetter A)
  have hscan :
      ((profiledOpenLeftBlockMonitor A code minimum profile).run play n).2.1 =
        letters.foldl (pairedLeftScanStep A)
          (pairedLeftScanInitial A code) := by
    rw [profiledOpenLeftBlockMonitor_run_scan_eq_physicalFold]
    exact List.foldl_map.symm
  have hfold := congrArg (fun pair ↦ A.priority pair.2)
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row code letters)
  calc
    pairedProfiledEntryPriority A target =
        A.priority
          (pairedLeftScanPairForRow A row
            (((profiledOpenLeftBlockMonitor A code minimum profile).run
              play n).2.1)).2 :=
      pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq A
        target _ row (profiledLeftPhysicalLetter A (play n)) herase
    _ = A.priority
          (pairedLeftScanPairForRow A row
            (letters.foldl (pairedLeftScanStep A)
              (pairedLeftScanInitial A code))).2 := by rw [hscan]
    _ = A.priority
          (blockMinState A (pairedCodeStateForRow A row code)
            (profiledLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
      simpa only [letters, profiledLeftPhysicalPrefixRecords, List.map_map,
        Function.comp_apply, blockMinState] using hfold

/-! ## Installed witnessed-overlay endpoints -/

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Strong right finite-epoch endpoint.  The selected target of the closing
record carries the minimum of the literal record prefix emitted by the
installed overlay.  The sole premise is the close-target equation checked by
the open monitor; no equality with a raw strategy word occurs. -/
theorem profiledOpenWitnessedRightClosingTargetPriority_eq_physicalBlockMin
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (code : A.State × A.State) (inputs : List (In₁ × In₂))
    (inputOne : In₁) (inputTwo : In₂)
    (herase :
      erasePairedProfiledState A
          ((profiledOpenWitnessedRightRoundRecord A initialCode
            (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
              inputs) inputOne inputTwo).2.1.1.target overlay.entryRow) =
        pairedRightCloseTarget A
          (((profiledOpenWitnessedRightRoundOverlayRecords A initialCode
              overlay inputs).map
                (profiledOpenWitnessedRightOverlayPhysicalLetter A
                  initialCode)).foldl
            (pairedRightScanStep A) (pairedRightScanInitial A code))
          overlay.entryRow
          (profiledOpenWitnessedRightOverlayPhysicalLetter A initialCode
            (profiledOpenWitnessedRightRoundRecord A initialCode
              (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
                inputs) inputOne inputTwo))) :
    pairedProfiledEntryPriority A
        ((profiledOpenWitnessedRightRoundRecord A initialCode
          (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo).2.1.1.target overlay.entryRow) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A overlay.entryRow code)
          (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode
            overlay inputs)) := by
  let scan :=
    ((profiledOpenWitnessedRightRoundOverlayRecords A initialCode overlay
      inputs).map
        (profiledOpenWitnessedRightOverlayPhysicalLetter A initialCode)).foldl
      (pairedRightScanStep A) (pairedRightScanInitial A code)
  let closingRecord := profiledOpenWitnessedRightRoundRecord A initialCode
    (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs)
      inputOne inputTwo
  have htarget :=
    pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq A
      (closingRecord.2.1.1.target overlay.entryRow) scan overlay.entryRow
        (profiledOpenWitnessedRightOverlayPhysicalLetter A initialCode
          closingRecord) herase
  have hminimum :=
    profiledOpenWitnessedRightOverlayPhysicalRecords_blockMinPriority A
      initialCode overlay code inputs
  exact htarget.trans hminimum.symm

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left installed-overlay endpoint. -/
theorem profiledOpenWitnessedLeftClosingTargetPriority_eq_physicalBlockMin
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (code : A.State × A.State) (inputs : List (In₁ × In₂))
    (inputOne : In₁) (inputTwo : In₂)
    (herase :
      erasePairedProfiledState A
          ((profiledOpenWitnessedLeftRoundRecord A initialCode
            (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
              inputs) inputOne inputTwo).2.1.1.target overlay.entryRow) =
        pairedLeftCloseTarget A
          (((profiledOpenWitnessedLeftRoundOverlayRecords A initialCode
              overlay inputs).map
                (profiledOpenWitnessedLeftOverlayPhysicalLetter A
                  initialCode)).foldl
            (pairedLeftScanStep A) (pairedLeftScanInitial A code))
          overlay.entryRow
          (profiledOpenWitnessedLeftOverlayPhysicalLetter A initialCode
            (profiledOpenWitnessedLeftRoundRecord A initialCode
              (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
                inputs) inputOne inputTwo))) :
    pairedProfiledEntryPriority A
        ((profiledOpenWitnessedLeftRoundRecord A initialCode
          (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo).2.1.1.target overlay.entryRow) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A overlay.entryRow code)
          (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode
            overlay inputs)) := by
  let scan :=
    ((profiledOpenWitnessedLeftRoundOverlayRecords A initialCode overlay
      inputs).map
        (profiledOpenWitnessedLeftOverlayPhysicalLetter A initialCode)).foldl
      (pairedLeftScanStep A) (pairedLeftScanInitial A code)
  let closingRecord := profiledOpenWitnessedLeftRoundRecord A initialCode
    (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs)
      inputOne inputTwo
  have htarget :=
    pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq A
      (closingRecord.2.1.1.target overlay.entryRow) scan overlay.entryRow
        (profiledOpenWitnessedLeftOverlayPhysicalLetter A initialCode
          closingRecord) herase
  have hminimum :=
    profiledOpenWitnessedLeftOverlayPhysicalRecords_blockMinPriority A
      initialCode overlay code inputs
  exact htarget.trans hminimum.symm

end

end DetParityAutomaton

end DistributedSynthesis
