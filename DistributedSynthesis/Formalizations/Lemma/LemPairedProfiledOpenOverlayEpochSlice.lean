/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReanchoredEvaluationOneRoundTrace

/-!
# Physical epoch slices of installed witnessed overlays

An installed overlay emits a rationalized blind-sender output.  Hence its
literal physical word need not be the raw strategy word
`PairedStrategyMemory.selectedBlockWord`.  What is preserved unconditionally
is the quantity used by the parity argument: for either sticky entry row, the
two-row scan is exactly `blockEndAndMin` of the records physically emitted by
the overlay.

This file states that fact at finite-list granularity.  It deliberately keeps
the semantic retained-root invariant separate: that invariant identifies the
receiver row with a raw semantic row, but it cannot manufacture equality of
the rationalized sender coordinate.  A later global-machine adapter therefore
only has to identify its concrete trace slice with the physical list below and
identify the selected root priority with the corresponding scan minimum.
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

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## Erasing the pinned root tag to the physical paired letter -/

/-- Strip the proof-side descriptor/root tag and classified target data from
one right overlay record.  The remaining letter is exactly the finite letter
whose selected row is read by the physical DPA. -/
def profiledOpenWitnessedRightOverlayPhysicalLetter
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    (record : RealizedBlockRound
      ((Sigma fun member : ProfiledOpenHiddenDescriptorRightCarrier A
        value.1 ↦ ProfiledOpenHiddenDescriptorRightRoot A member.1) × In₂)
      In₁ (ProfiledOpenRightClassifiedOutput A) Out₁) :
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  ((record.1.1.2, record.1.2), record.2.1.1.physical, record.2.2)

/-- Left mirror of the physical-letter erasure. -/
def profiledOpenWitnessedLeftOverlayPhysicalLetter
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    (record : RealizedBlockRound
      ((Sigma fun member : ProfiledOpenHiddenDescriptorLeftCarrier A
        value.1 ↦ ProfiledOpenHiddenDescriptorLeftRoot A member.1) × In₁)
      In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂) :
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  ((record.1.1.2, record.1.2), record.2.1.1.physical, record.2.2)

/-- Literal right-oriented `RoundRecord` list emitted by an installed overlay,
with the overlay's sticky row selecting the informed output coordinate. -/
def profiledOpenWitnessedRightOverlayPhysicalRecords
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  (profiledOpenWitnessedRightRoundOverlayRecords A initialCode overlay inputs).map
    (fun record ↦ pairedRightRecordForRow overlay.entryRow
      (profiledOpenWitnessedRightOverlayPhysicalLetter A initialCode record))

/-- Left-oriented physical record list. -/
def profiledOpenWitnessedLeftOverlayPhysicalRecords
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  (profiledOpenWitnessedLeftRoundOverlayRecords A initialCode overlay inputs).map
    (fun record ↦ pairedLeftRecordForRow overlay.entryRow
      (profiledOpenWitnessedLeftOverlayPhysicalLetter A initialCode record))

section
omit [Inhabited I]

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenWitnessedRightRoundOverlay_step_entryRow
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    (overlay.step A initialCode inputOne inputTwo).entryRow = overlay.entryRow :=
  rfl

@[simp] theorem profiledOpenWitnessedLeftRoundOverlay_step_entryRow
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    (overlay.step A initialCode inputOne inputTwo).entryRow = overlay.entryRow :=
  rfl

@[simp] theorem profiledOpenWitnessedRightOverlayPhysicalRecords_nil
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) :
    profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay [] =
      [] :=
  rfl

@[simp] theorem profiledOpenWitnessedLeftOverlayPhysicalRecords_nil
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) :
    profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay [] =
      [] :=
  rfl

@[simp] theorem profiledOpenWitnessedRightOverlayPhysicalRecords_cons
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (input : In₁ × In₂) (rest : List (In₁ × In₂)) :
    profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay
        (input :: rest) =
      rightRoundRecord (input.2, input.1)
          (profiledOpenWitnessedRightSenderOutput A initialCode overlay input.1)
          (profiledOpenWitnessedRightReceiverOutput A initialCode overlay
            input.1 input.2) ::
        profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode
          (overlay.step A initialCode input.1 input.2) rest := by
  unfold profiledOpenWitnessedRightOverlayPhysicalRecords
  rw [profiledOpenWitnessedRightRoundOverlayRecords]
  simp only [List.map_cons]
  congr 1
  cases hrow : overlay.entryRow <;>
    simp only [profiledOpenWitnessedRightOverlayPhysicalLetter,
      pairedRightRecordForRow, profiledOpenWitnessedRightRoundRecord,
      profiledOpenWitnessedRightSenderOutput,
      profiledOpenWitnessedRightReceiverOutput, pairedRightInformedForRow,
      hrow]

@[simp] theorem profiledOpenWitnessedLeftOverlayPhysicalRecords_cons
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (input : In₁ × In₂) (rest : List (In₁ × In₂)) :
    profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay
        (input :: rest) =
      leftRoundRecord input
          (profiledOpenWitnessedLeftReceiverOutput A initialCode overlay
            input.1 input.2)
          (profiledOpenWitnessedLeftSenderOutput A initialCode overlay input.2) ::
        profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode
          (overlay.step A initialCode input.1 input.2) rest := by
  unfold profiledOpenWitnessedLeftOverlayPhysicalRecords
  rw [profiledOpenWitnessedLeftRoundOverlayRecords]
  simp only [List.map_cons]
  congr 1
  cases hrow : overlay.entryRow <;>
    simp only [profiledOpenWitnessedLeftOverlayPhysicalLetter,
      pairedLeftRecordForRow, profiledOpenWitnessedLeftRoundRecord,
      profiledOpenWitnessedLeftSenderOutput,
      profiledOpenWitnessedLeftReceiverOutput, pairedLeftInformedForRow, hrow]

end

end

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenWitnessedRightOverlayPhysicalRecords_length
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) :
    ∀ inputs : List (In₁ × In₂),
      (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay
        inputs).length = inputs.length := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => rfl
  | cons input rest ih =>
      simp only [profiledOpenWitnessedRightOverlayPhysicalRecords_cons,
        List.length_cons, Nat.succ.injEq]
      exact ih (overlay := overlay.step A initialCode input.1 input.2)

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenWitnessedLeftOverlayPhysicalRecords_length
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) :
    ∀ inputs : List (In₁ × In₂),
      (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay
        inputs).length = inputs.length := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => rfl
  | cons input rest ih =>
      simp only [profiledOpenWitnessedLeftOverlayPhysicalRecords_cons,
        List.length_cons, Nat.succ.injEq]
      exact ih (overlay := overlay.step A initialCode input.1 input.2)

/-! ## A row of the two-thread scan is exactly `blockEndAndMin` -/

/-- Select one row's current/minimum pair from a right scan. -/
def pairedRightScanPairForRow (row : PairedEntryRow)
    (scan : PairedRightScanState A) : A.State × A.State :=
  match row with
  | .first => (scan.1.1, scan.2.1)
  | .both => (scan.1.2, scan.2.2)

/-- Select one row's current/minimum pair from a left scan. -/
def pairedLeftScanPairForRow (row : PairedEntryRow)
    (scan : PairedLeftScanState A) : A.State × A.State :=
  match row with
  | .first => (scan.1.1, scan.2.1)
  | .both => (scan.1.2, scan.2.2)

/-- Select the entry state belonging to one latent row. -/
def pairedCodeStateForRow (row : PairedEntryRow)
    (code : A.State × A.State) : A.State :=
  match row with
  | .first => code.1
  | .both => code.2

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- Arbitrary-start right scan law. -/
theorem pairedRightScanFold_pairForRow
    (row : PairedEntryRow) (scan : PairedRightScanState A) :
    ∀ letters : List (PairedRightBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
      pairedRightScanPairForRow A row
          (letters.foldl (pairedRightScanStep A) scan) =
        (letters.map (pairedRightRecordForRow row)).foldl
          (fun currentMin record ↦
            let next := A.step currentMin.1 record
            (next, A.minPriorityState currentMin.2 next))
          (pairedRightScanPairForRow A row scan) := by
  intro letters
  induction letters generalizing scan with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      cases row <;>
        rfl

/-- Arbitrary-start left scan law. -/
theorem pairedLeftScanFold_pairForRow
    (row : PairedEntryRow) (scan : PairedLeftScanState A) :
    ∀ letters : List (PairedLeftBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)),
      pairedLeftScanPairForRow A row
          (letters.foldl (pairedLeftScanStep A) scan) =
        (letters.map (pairedLeftRecordForRow row)).foldl
          (fun currentMin record ↦
            let next := A.step currentMin.1 record
            (next, A.minPriorityState currentMin.2 next))
          (pairedLeftScanPairForRow A row scan) := by
  intro letters
  induction letters generalizing scan with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      cases row <;>
        rfl

/-- From the canonical paired-code start, the selected right scan row is
literally the DPA end/minimum pair of the selected physical record word. -/
theorem pairedRightScanFold_pairForRow_eq_blockEndAndMin
    (row : PairedEntryRow) (code : A.State × A.State)
    (letters : List (PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    pairedRightScanPairForRow A row
        (letters.foldl (pairedRightScanStep A)
          (pairedRightScanInitial A code)) =
      blockEndAndMin A (pairedCodeStateForRow A row code)
        (letters.map (pairedRightRecordForRow row)) := by
  rw [pairedRightScanFold_pairForRow]
  cases row <;>
    rfl

/-- Left canonical-start mirror. -/
theorem pairedLeftScanFold_pairForRow_eq_blockEndAndMin
    (row : PairedEntryRow) (code : A.State × A.State)
    (letters : List (PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    pairedLeftScanPairForRow A row
        (letters.foldl (pairedLeftScanStep A)
          (pairedLeftScanInitial A code)) =
      blockEndAndMin A (pairedCodeStateForRow A row code)
        (letters.map (pairedLeftRecordForRow row)) := by
  rw [pairedLeftScanFold_pairForRow]
  cases row <;>
    rfl

end

/-! ## Installed-overlay scan/minimum equations -/

section
omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The strongest unconditional right finite-epoch statement: the selected
scan row equals the end/minimum pair of the literal physical record slice.
No equality with the raw strategy's sender word is assumed. -/
theorem profiledOpenWitnessedRightOverlayPhysicalRecords_blockEndAndMin
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (code : A.State × A.State) (inputs : List (In₁ × In₂)) :
    blockEndAndMin A (pairedCodeStateForRow A overlay.entryRow code)
        (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay
          inputs) =
      pairedRightScanPairForRow A overlay.entryRow
        ((profiledOpenWitnessedRightRoundOverlayRecords A initialCode overlay
          inputs).map
            (profiledOpenWitnessedRightOverlayPhysicalLetter A initialCode)
          |>.foldl (pairedRightScanStep A) (pairedRightScanInitial A code)) := by
  symm
  simpa only [profiledOpenWitnessedRightOverlayPhysicalRecords, List.map_map,
    Function.comp_apply] using
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A overlay.entryRow code
      ((profiledOpenWitnessedRightRoundOverlayRecords A initialCode overlay
        inputs).map
          (profiledOpenWitnessedRightOverlayPhysicalLetter A initialCode)))

/-- Left finite-epoch scan/minimum equation. -/
theorem profiledOpenWitnessedLeftOverlayPhysicalRecords_blockEndAndMin
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (code : A.State × A.State) (inputs : List (In₁ × In₂)) :
    blockEndAndMin A (pairedCodeStateForRow A overlay.entryRow code)
        (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay
          inputs) =
      pairedLeftScanPairForRow A overlay.entryRow
        ((profiledOpenWitnessedLeftRoundOverlayRecords A initialCode overlay
          inputs).map
            (profiledOpenWitnessedLeftOverlayPhysicalLetter A initialCode)
          |>.foldl (pairedLeftScanStep A) (pairedLeftScanInitial A code)) := by
  symm
  simpa only [profiledOpenWitnessedLeftOverlayPhysicalRecords, List.map_map,
    Function.comp_apply] using
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A overlay.entryRow code
      ((profiledOpenWitnessedLeftRoundOverlayRecords A initialCode overlay
        inputs).map
          (profiledOpenWitnessedLeftOverlayPhysicalLetter A initialCode)))

/-- Priority form consumed by the automatic recut parity handoff. -/
theorem profiledOpenWitnessedRightOverlayPhysicalRecords_blockMinPriority
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (code : A.State × A.State) (inputs : List (In₁ × In₂)) :
    A.priority
        (blockMinState A (pairedCodeStateForRow A overlay.entryRow code)
          (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode
            overlay inputs)) =
      A.priority
        (pairedRightScanPairForRow A overlay.entryRow
          ((profiledOpenWitnessedRightRoundOverlayRecords A initialCode overlay
            inputs).map
              (profiledOpenWitnessedRightOverlayPhysicalLetter A initialCode)
            |>.foldl (pairedRightScanStep A)
              (pairedRightScanInitial A code))).2 := by
  unfold blockMinState
  rw [profiledOpenWitnessedRightOverlayPhysicalRecords_blockEndAndMin]

/-- Left priority form. -/
theorem profiledOpenWitnessedLeftOverlayPhysicalRecords_blockMinPriority
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (code : A.State × A.State) (inputs : List (In₁ × In₂)) :
    A.priority
        (blockMinState A (pairedCodeStateForRow A overlay.entryRow code)
          (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode
            overlay inputs)) =
      A.priority
        (pairedLeftScanPairForRow A overlay.entryRow
          ((profiledOpenWitnessedLeftRoundOverlayRecords A initialCode overlay
            inputs).map
              (profiledOpenWitnessedLeftOverlayPhysicalLetter A initialCode)
            |>.foldl (pairedLeftScanStep A)
              (pairedLeftScanInitial A code))).2 := by
  unfold blockMinState
  rw [profiledOpenWitnessedLeftOverlayPhysicalRecords_blockEndAndMin]

end

end

end DetParityAutomaton

end DistributedSynthesis
