/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalRealClosure
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalAutomaton

/-!
# Reality at the initial-to-recurrent seam

The root-pinned initial carrier retains a freshly advanced exceptional pair
when a receive may be the first strict reversal.  This file relates that
stored pair to a real matched phase.  The relation is proof-only; the local
summaries still contain just their independently computed controls.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (bundle : EndToEndOperationalControllerPackage A)

/-- A stored first-right pair is real if it is the two local projections of
one real right-oriented matched phase. -/
def EndToEndFirstRightControlPair.Real
    (pair : EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
      EndToEndGuardedFirstRightReceiverControl A bundle.rational) : Prop :=
  ∃ phase : EndToEndMatchedPhase A bundle.rational,
    phase.IsRight ∧
      phase.oneControl = .inl pair.1 ∧
      phase.twoControl = .inl pair.2 ∧
      IsRealEndToEndPhase A bundle.rational phase

/-- A fresh first-right update from a checked key is a real stored pair. -/
theorem endToEndOperationalFreshFirstRight_real
    (key : EndToEndInitialLeftBoundaryKey A bundle.rational)
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    ∃ pair,
      (endToEndOperationalFreshFirstRight A bundle (some key)
        receiverPreviouslyReceived move).2 = some pair ∧
      EndToEndFirstRightControlPair.Real A bundle pair := by
  let row := guardedEntryRowOfReceived receiverPreviouslyReceived
  let oldOwner :=
    initialEndToEndGuardedFirstRightOwner A bundle.rational key
  let oldReceiver :=
    initialEndToEndGuardedFirstRightReceiver A bundle.rational key row
  let base : EndToEndMatchedPhase A bundle.rational :=
    .firstRight oldOwner oldReceiver rfl
  let pair :=
    ((stepEndToEndGuardedFirstRightOwner A bundle.rational oldOwner move.1).2,
      (continueEndToEndGuardedFirstRightReceiver A bundle.rational oldReceiver
        oldOwner (move.2, move.1)).2)
  have hsome := endToEndFirstRight_real_close_staged A bundle.rational key row
    [] (move.2, move.1)
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstaged⟩
  have hphase := endToEndFirstRight_continue_eq_real_phase A bundle.rational
    key row [] none (move.2, move.1) target hstaged
  have hreal : IsRealEndToEndPhase A bundle.rational
      (base.continue A bundle.rational move).2 := by
    left
    refine ⟨key, row, [(move.2, move.1)], target, ?_⟩
    unfold IsRealEndToEndFirstRightPhaseAt
    exact hphase
  have horiented : (base.continue A bundle.rational move).2.IsRight :=
    base.continue_isRight A bundle.rational move (by
      simp [base, EndToEndMatchedPhase.IsRight])
  refine ⟨pair, ?_, ?_⟩
  · rfl
  · exact ⟨(base.continue A bundle.rational move).2, horiented, rfl, rfl,
      hreal⟩

/-- A stored first-left pair is the two projections of one real left phase.
The pair is ordered `(owner, receiver)`, while process one stores the
receiver and process two stores the owner. -/
def EndToEndFirstLeftControlPair.Real
    (pair : EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
      EndToEndGuardedFirstLeftReceiverControl A bundle.rational) : Prop :=
  ∃ phase : EndToEndMatchedPhase A bundle.rational,
    phase.IsLeft ∧
      phase.oneControl = .inr (.inl pair.2) ∧
      phase.twoControl = .inr (.inl pair.1) ∧
      IsRealEndToEndPhase A bundle.rational phase

/-- Fresh first-left mirror. -/
theorem endToEndOperationalFreshFirstLeft_real
    (key : EndToEndInitialRightBoundaryKey A bundle.rational)
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    ∃ pair,
      (endToEndOperationalFreshFirstLeft A bundle (some key)
        receiverPreviouslyReceived move).2 = some pair ∧
      EndToEndFirstLeftControlPair.Real A bundle pair := by
  let row := guardedEntryRowOfReceived receiverPreviouslyReceived
  let oldOwner :=
    initialEndToEndGuardedFirstLeftOwner A bundle.rational key
  let oldReceiver :=
    initialEndToEndGuardedFirstLeftReceiver A bundle.rational key row
  let base : EndToEndMatchedPhase A bundle.rational :=
    .firstLeft oldReceiver oldOwner rfl
  let pair :=
    ((stepEndToEndGuardedFirstLeftOwner A bundle.rational oldOwner move.2).2,
      (continueEndToEndGuardedFirstLeftReceiver A bundle.rational oldReceiver
        oldOwner move).2)
  have hsome := endToEndFirstLeft_real_close_staged A bundle.rational key row
    [] move
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstaged⟩
  have hphase := endToEndFirstLeft_continue_eq_real_phase A bundle.rational
    key row [] none move target hstaged
  have hreal : IsRealEndToEndPhase A bundle.rational
      (base.continue A bundle.rational move).2 := by
    right; left
    refine ⟨key, row, [move], target, ?_⟩
    unfold IsRealEndToEndFirstLeftPhaseAt
    exact hphase
  have horiented : (base.continue A bundle.rational move).2.IsLeft :=
    base.continue_isLeft A bundle.rational move (by
      simp [base, EndToEndMatchedPhase.IsLeft])
  refine ⟨pair, ?_, ?_⟩
  · rfl
  · exact ⟨(base.continue A bundle.rational move).2, horiented, rfl, rfl,
      hreal⟩

/-! ## Strict resolution into the real post-initial carrier -/

/-- Selecting a real stored first-right pair enters a real resolved-right
post shape and cannot take the seam fallback. -/
theorem endToEndOperationalInitialLeftSeamResolveRight_real
    (pair : EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
      EndToEndGuardedFirstRightReceiverControl A bundle.rational)
    (hreal : EndToEndFirstRightControlPair.Real A bundle pair)
    (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (shape : EndToEndOperationalPostShape A bundle.rational),
      endToEndOperationalInitialLeftSeamResolveRight A bundle pair move =
        (output, some (shape.oneControl, shape.twoControl)) ∧
      shape.Real A bundle.rational := by
  rcases hreal with ⟨phase, horiented, hone, htwo, hphase⟩
  have hmatched : endToEndMatchedRightOfControls A bundle.rational
      (.inl pair.1) (.inl pair.2) = some phase := by
    rw [← hone, ← htwo]
    exact endToEndMatchedRightOfControls_of_phase A bundle.rational phase
      horiented
  let next := (phase.continue A bundle.rational move).2
  have hnextOriented : next.IsRight :=
    phase.continue_isRight A bundle.rational move horiented
  have hnextReal : IsRealEndToEndPhase A bundle.rational next :=
    isRealEndToEndPhase_continue A bundle.rational phase hphase move
  let shape : EndToEndOperationalPostShape A bundle.rational :=
    .resolvedRight next hnextOriented
  refine ⟨(phase.continue A bundle.rational move).1, shape, ?_, ?_⟩
  · simp [endToEndOperationalInitialLeftSeamResolveRight, hmatched, shape,
      next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
  · exact hnextReal

/-- Strict-left mirror. -/
theorem endToEndOperationalInitialRightSeamResolveLeft_real
    (pair : EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
      EndToEndGuardedFirstLeftReceiverControl A bundle.rational)
    (hreal : EndToEndFirstLeftControlPair.Real A bundle pair)
    (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (shape : EndToEndOperationalPostShape A bundle.rational),
      endToEndOperationalInitialRightSeamResolveLeft A bundle pair move =
        (output, some (shape.oneControl, shape.twoControl)) ∧
      shape.Real A bundle.rational := by
  rcases hreal with ⟨phase, horiented, hone, htwo, hphase⟩
  have hmatched : endToEndMatchedLeftOfControls A bundle.rational
      (.inr (.inl pair.2)) (.inr (.inl pair.1)) = some phase := by
    rw [← hone, ← htwo]
    exact endToEndMatchedLeftOfControls_of_phase A bundle.rational phase
      horiented
  let next := (phase.continue A bundle.rational move).2
  have hnextOriented : next.IsLeft :=
    phase.continue_isLeft A bundle.rational move horiented
  have hnextReal : IsRealEndToEndPhase A bundle.rational next :=
    isRealEndToEndPhase_continue A bundle.rational phase hphase move
  let shape : EndToEndOperationalPostShape A bundle.rational :=
    .resolvedLeft next hnextOriented
  refine ⟨(phase.continue A bundle.rational move).1, shape, ?_, ?_⟩
  · simp [endToEndOperationalInitialRightSeamResolveLeft, hmatched, shape,
      next, EndToEndOperationalPostShape.oneControl,
      EndToEndOperationalPostShape.twoControl]
  · exact hnextReal

/-! ## The delayed seam receive used by the executable automaton -/

/-- When process one has locally selected a real first-right owner while
process two retains the matching seam pair, their next receive enters a real
post-initial shape. -/
theorem endToEndOperationalRecvPair_real_initialLeftSeam
    (pair : EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
      EndToEndGuardedFirstRightReceiverControl A bundle.rational)
    (hreal : EndToEndFirstRightControlPair.Real A bundle pair)
    (blind : bundle.leftController.Control) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      endToEndOperationalRecvPair A bundle
          (.post (.inl (.inl pair.1)))
          (.initialLeftSeam (blind, pair)) move =
        ((.post next.oneControl, output.1),
          (.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  rcases hreal with ⟨phase, horiented, hone, htwo, hphase⟩
  let shape : EndToEndOperationalPostShape A bundle.rational :=
    .resolvedRight phase horiented
  obtain ⟨output, next, hrecv, hnext⟩ :=
    endToEndOperationalPostRecv_realShape A bundle.rational shape hphase move
  refine ⟨output, next, ?_, hnext⟩
  have hone' : (.inl (.inl pair.1) : EndToEndOperationalPostOne A
      bundle.rational) = shape.oneControl := by
    simp [shape, EndToEndOperationalPostShape.oneControl, hone]
  have htwo' : (.inl (.inl pair.2) : EndToEndOperationalPostTwo A
      bundle.rational) = shape.twoControl := by
    simp [shape, EndToEndOperationalPostShape.twoControl, htwo]
  simp only [endToEndOperationalRecvPair]
  rw [hone', htwo', hrecv]

/-- Process-swapped seam receive. -/
theorem endToEndOperationalRecvPair_real_initialRightSeam
    (pair : EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
      EndToEndGuardedFirstLeftReceiverControl A bundle.rational)
    (hreal : EndToEndFirstLeftControlPair.Real A bundle pair)
    (blind : bundle.rightController.Control) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A bundle.rational),
      endToEndOperationalRecvPair A bundle
          (.initialRightSeam (blind, pair))
          (.post (.inl (.inr (.inl pair.1)))) move =
        ((.post next.oneControl, output.1),
          (.post next.twoControl, output.2)) ∧
      next.Real A bundle.rational := by
  rcases hreal with ⟨phase, horiented, hone, htwo, hphase⟩
  let shape : EndToEndOperationalPostShape A bundle.rational :=
    .resolvedLeft phase horiented
  obtain ⟨output, next, hrecv, hnext⟩ :=
    endToEndOperationalPostRecv_realShape A bundle.rational shape hphase move
  refine ⟨output, next, ?_, hnext⟩
  have hone' : (.inl (.inr (.inl pair.2)) : EndToEndOperationalPostOne A
      bundle.rational) = shape.oneControl := by
    simp [shape, EndToEndOperationalPostShape.oneControl, hone]
  have htwo' : (.inl (.inr (.inl pair.1)) : EndToEndOperationalPostTwo A
      bundle.rational) = shape.twoControl := by
    simp [shape, EndToEndOperationalPostShape.twoControl, htwo]
  simp only [endToEndOperationalRecvPair]
  rw [hone', htwo', hrecv]

end

end DetParityAutomaton

end DistributedSynthesis
