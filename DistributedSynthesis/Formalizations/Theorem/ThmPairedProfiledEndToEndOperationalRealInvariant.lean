/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalRecurrentReality

/-!
# Real end-to-end matched phases

A real phase is a concrete finite prefix of one of the six selected
controller families.  The witness past and orientation are proof-only.  This
is the invariant that turns the pointwise staging lemmas into closure of the
actual two-summary implementation.
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

variable (package : PairedInitialProfiledRationalPackage A)

def IsRealEndToEndFirstRightPhaseAt
    (key : EndToEndInitialLeftBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (target : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy))
    (phase : EndToEndMatchedPhase A package) : Prop :=
  phase = .firstRight
    ⟨key, (endToEndFirstRightFiniteStateAfter A package key past).1⟩
    ⟨key, row, (endToEndFirstRightFiniteStateAfter A package key past).2,
      some target⟩ rfl

def IsRealEndToEndFirstLeftPhaseAt
    (key : EndToEndInitialRightBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (target : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy))
    (phase : EndToEndMatchedPhase A package) : Prop :=
  phase = .firstLeft
    ⟨key, row, (endToEndFirstLeftFiniteStateAfter A package key past).2,
      some target⟩
    ⟨key, (endToEndFirstLeftFiniteStateAfter A package key past).1⟩ rfl

def IsRealEndToEndRightOriginRightPhaseAt
    (source : EndToEndRightOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (target : EndToEndRightOriginRecurrentLeftMacro A package)
    (phase : EndToEndMatchedPhase A package) : Prop :=
  phase = .rightOriginRight
    ⟨source, (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
      source.2.2 past).1⟩
    ⟨source, row, (profiledPolicyRightFiniteStateAfter A
      (source.2.1.policy A) source.2.2 past).2, some target⟩ rfl

def IsRealEndToEndRightOriginLeftPhaseAt
    (source : EndToEndRightOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (target : EndToEndRightOriginRecurrentRightMacro A package)
    (phase : EndToEndMatchedPhase A package) : Prop :=
  phase = .rightOriginLeft
    ⟨source, row, (profiledPolicyLeftFiniteStateAfter A
      (source.2.1.policy A) source.2.2 past).2, some target⟩
    ⟨source, (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
      source.2.2 past).1⟩ rfl

def IsRealEndToEndLeftOriginRightPhaseAt
    (source : EndToEndLeftOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (target : EndToEndLeftOriginRecurrentLeftMacro A package)
    (phase : EndToEndMatchedPhase A package) : Prop :=
  phase = .leftOriginRight
    ⟨source, (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
      source.2.2 past).1⟩
    ⟨source, row, (profiledPolicyRightFiniteStateAfter A
      (source.2.1.policy A) source.2.2 past).2, some target⟩ rfl

def IsRealEndToEndLeftOriginLeftPhaseAt
    (source : EndToEndLeftOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (target : EndToEndLeftOriginRecurrentRightMacro A package)
    (phase : EndToEndMatchedPhase A package) : Prop :=
  phase = .leftOriginLeft
    ⟨source, row, (profiledPolicyLeftFiniteStateAfter A
      (source.2.1.policy A) source.2.2 past).2, some target⟩
    ⟨source, (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
      source.2.2 past).1⟩ rfl

/-- Concrete-prefix reality for all six matched phase modes. -/
def IsRealEndToEndPhase (phase : EndToEndMatchedPhase A package) : Prop :=
  (∃ key row past target,
    IsRealEndToEndFirstRightPhaseAt A package key row past target phase) ∨
  (∃ key row past target,
    IsRealEndToEndFirstLeftPhaseAt A package key row past target phase) ∨
  (∃ source row past target,
    IsRealEndToEndRightOriginRightPhaseAt A package source row past target
      phase) ∨
  (∃ source row past target,
    IsRealEndToEndRightOriginLeftPhaseAt A package source row past target
      phase) ∨
  (∃ source row past target,
    IsRealEndToEndLeftOriginRightPhaseAt A package source row past target
      phase) ∨
  (∃ source row past target,
    IsRealEndToEndLeftOriginLeftPhaseAt A package source row past target phase)

/-! ## Exact continuation equations -/

theorem endToEndFirstRight_continue_eq_real_phase
    (key : EndToEndInitialLeftBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₂ × In₁))
    (pending : Option (EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy)))
    (move : In₂ × In₁)
    (target : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded :=
        (endToEndInitialLeftBoundaryActivation A package key).policy))
    (hstaged :
      (stepEndToEndGuardedFirstRightReceiverFor A package key
        (endToEndFirstRightFiniteStateAfter A package key past).1 row
        (endToEndFirstRightFiniteStateAfter A package key past).2 move).2.2 =
          some target) :
    let owner : EndToEndGuardedFirstRightOwnerControl A package :=
      ⟨key, (endToEndFirstRightFiniteStateAfter A package key past).1⟩
    let receiver : EndToEndGuardedFirstRightReceiverControl A package :=
      ⟨key, row, (endToEndFirstRightFiniteStateAfter A package key past).2,
        pending⟩
    ((EndToEndMatchedPhase.firstRight owner receiver rfl).continue A package
      (move.2, move.1)).2 =
      .firstRight
        ⟨key, (endToEndFirstRightFiniteStateAfter A package key
          (past ++ [move])).1⟩
        ⟨key, row, (endToEndFirstRightFiniteStateAfter A package key
          (past ++ [move])).2, some target⟩ rfl := by
  dsimp only
  have hafter :
      endToEndFirstRightFiniteStateAfter A package key (past ++ [move]) =
        stepEndToEndFirstRightFiniteState A package key
          (endToEndFirstRightFiniteStateAfter A package key past) move := by
    simp [endToEndFirstRightFiniteStateAfter, List.foldl_append]
  rw [hafter]
  have hmonitor :
      (stepEndToEndGuardedFirstRightReceiverFor A package key
        (endToEndFirstRightFiniteStateAfter A package key past).1 row
        (endToEndFirstRightFiniteStateAfter A package key past).2 move).2.1 =
      (endToEndFirstRightMonitor A package key).step
        (endToEndFirstRightFiniteStateAfter A package key past).2
        (narrowedRecord (endToEndFirstRightMonitor A package key)
          ((endToEndInitialLeftBoundaryController A package key).labelOf
            (endToEndFirstRightFiniteStateAfter A package key past).1)
          (endToEndFirstRightFiniteStateAfter A package key past).2 move) := by
    simp only [stepEndToEndGuardedFirstRightReceiverFor, narrowedRecord]
    split <;> rfl
  simp [EndToEndMatchedPhase.continue,
    continueEndToEndGuardedFirstRightReceiver,
    endToEndGuardedFirstRightOwnerControlFor,
    stepEndToEndGuardedFirstRightOwner,
    stepEndToEndFirstRightFiniteState,
    hmonitor, hstaged]

theorem endToEndFirstLeft_continue_eq_real_phase
    (key : EndToEndInitialRightBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₁ × In₂))
    (pending : Option (EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy)))
    (move : In₁ × In₂)
    (target : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded :=
        (endToEndInitialRightBoundaryActivation A package key).policy))
    (hstaged :
      (stepEndToEndGuardedFirstLeftReceiverFor A package key
        (endToEndFirstLeftFiniteStateAfter A package key past).1 row
        (endToEndFirstLeftFiniteStateAfter A package key past).2 move).2.2 =
          some target) :
    let receiver : EndToEndGuardedFirstLeftReceiverControl A package :=
      ⟨key, row, (endToEndFirstLeftFiniteStateAfter A package key past).2,
        pending⟩
    let owner : EndToEndGuardedFirstLeftOwnerControl A package :=
      ⟨key, (endToEndFirstLeftFiniteStateAfter A package key past).1⟩
    ((EndToEndMatchedPhase.firstLeft receiver owner rfl).continue A package
      move).2 =
      .firstLeft
        ⟨key, row, (endToEndFirstLeftFiniteStateAfter A package key
          (past ++ [move])).2, some target⟩
        ⟨key, (endToEndFirstLeftFiniteStateAfter A package key
          (past ++ [move])).1⟩ rfl := by
  dsimp only
  have hafter :
      endToEndFirstLeftFiniteStateAfter A package key (past ++ [move]) =
        stepEndToEndFirstLeftFiniteState A package key
          (endToEndFirstLeftFiniteStateAfter A package key past) move := by
    simp [endToEndFirstLeftFiniteStateAfter, List.foldl_append]
  rw [hafter]
  have hmonitor :
      (stepEndToEndGuardedFirstLeftReceiverFor A package key
        (endToEndFirstLeftFiniteStateAfter A package key past).1 row
        (endToEndFirstLeftFiniteStateAfter A package key past).2 move).2.1 =
      (endToEndFirstLeftMonitor A package key).step
        (endToEndFirstLeftFiniteStateAfter A package key past).2
        (narrowedRecord (endToEndFirstLeftMonitor A package key)
          ((endToEndInitialRightBoundaryController A package key).labelOf
            (endToEndFirstLeftFiniteStateAfter A package key past).1)
          (endToEndFirstLeftFiniteStateAfter A package key past).2 move) := by
    simp only [stepEndToEndGuardedFirstLeftReceiverFor, narrowedRecord]
    split <;> rfl
  simp [EndToEndMatchedPhase.continue,
    continueEndToEndGuardedFirstLeftReceiver,
    endToEndGuardedFirstLeftOwnerControlFor,
    stepEndToEndGuardedFirstLeftOwner,
    stepEndToEndFirstLeftFiniteState,
    hmonitor, hstaged]

theorem endToEndRightOriginRight_continue_eq_real_phase
    (source : EndToEndRightOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (pending : Option (EndToEndRightOriginRecurrentLeftMacro A package))
    (move : In₂ × In₁)
    (target : EndToEndRightOriginRecurrentLeftMacro A package)
    (hstaged :
      (stepEndToEndRightOriginRecurrentRightReceiverFor A package source
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 = some target) :
    let owner : EndToEndRightOriginRecurrentRightOwnerControl A package :=
      ⟨source, (profiledPolicyRightFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).1⟩
    let receiver : EndToEndRightOriginRecurrentRightReceiverControl A package :=
      ⟨source, row, (profiledPolicyRightFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).2, pending⟩
    ((EndToEndMatchedPhase.rightOriginRight owner receiver rfl).continue
      A package (move.2, move.1)).2 =
      .rightOriginRight
        ⟨source, (profiledPolicyRightFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).1⟩
        ⟨source, row, (profiledPolicyRightFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).2,
          some target⟩ rfl := by
  dsimp only
  have hafter :
      profiledPolicyRightFiniteStateAfter A (source.2.1.policy A) source.2.2
          (past ++ [move]) =
        stepProfiledPolicyRightFiniteState A (source.2.1.policy A) source.2.2
          (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past) move := by
    simp [profiledPolicyRightFiniteStateAfter, List.foldl_append]
  rw [hafter]
  have hmonitor :
      (stepEndToEndRightOriginRecurrentRightReceiverFor A package source
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.1 =
      (profiledPolicyRightMonitor A (source.2.1.policy A) source.2.2).step
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2
        (narrowedRecord
          (profiledPolicyRightMonitor A (source.2.1.policy A) source.2.2)
          ((profiledPolicyRightController A (source.2.1.policy A)
            source.2.2).labelOf
              (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
                source.2.2 past).1)
          (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past).2 move) := by
    simp [stepEndToEndRightOriginRecurrentRightReceiverFor,
      stepProfiledPolicyRightReceiverFor_monitor]
  simp [EndToEndMatchedPhase.continue,
    continueEndToEndRightOriginRecurrentRightReceiver,
    endToEndRightOriginRecurrentRightOwnerControlFor,
    stepEndToEndRightOriginRecurrentRightOwner,
    endToEndGuardedRightRecurrentRightController,
    stepProfiledPolicyRightFiniteState,
    hmonitor, hstaged]

theorem endToEndRightOriginLeft_continue_eq_real_phase
    (source : EndToEndRightOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (pending : Option (EndToEndRightOriginRecurrentRightMacro A package))
    (move : In₁ × In₂)
    (target : EndToEndRightOriginRecurrentRightMacro A package)
    (hstaged :
      (stepEndToEndRightOriginRecurrentLeftReceiverFor A package source
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 = some target) :
    let receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package :=
      ⟨source, row, (profiledPolicyLeftFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).2, pending⟩
    let owner : EndToEndRightOriginRecurrentLeftOwnerControl A package :=
      ⟨source, (profiledPolicyLeftFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).1⟩
    ((EndToEndMatchedPhase.rightOriginLeft receiver owner rfl).continue
      A package move).2 =
      .rightOriginLeft
        ⟨source, row, (profiledPolicyLeftFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).2,
          some target⟩
        ⟨source, (profiledPolicyLeftFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).1⟩ rfl := by
  dsimp only
  have hafter :
      profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A) source.2.2
          (past ++ [move]) =
        stepProfiledPolicyLeftFiniteState A (source.2.1.policy A) source.2.2
          (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past) move := by
    simp [profiledPolicyLeftFiniteStateAfter, List.foldl_append]
  rw [hafter]
  have hmonitor :
      (stepEndToEndRightOriginRecurrentLeftReceiverFor A package source
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.1 =
      (profiledPolicyLeftMonitor A (source.2.1.policy A) source.2.2).step
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2
        (narrowedRecord
          (profiledPolicyLeftMonitor A (source.2.1.policy A) source.2.2)
          ((profiledPolicyLeftController A (source.2.1.policy A)
            source.2.2).labelOf
              (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
                source.2.2 past).1)
          (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past).2 move) := by
    simp [stepEndToEndRightOriginRecurrentLeftReceiverFor,
      stepProfiledPolicyLeftReceiverFor_monitor]
  simp [EndToEndMatchedPhase.continue,
    continueEndToEndRightOriginRecurrentLeftReceiver,
    endToEndRightOriginRecurrentLeftOwnerControlFor,
    stepEndToEndRightOriginRecurrentLeftOwner,
    endToEndGuardedRightRecurrentLeftController,
    stepProfiledPolicyLeftFiniteState,
    hmonitor, hstaged]

theorem endToEndLeftOriginRight_continue_eq_real_phase
    (source : EndToEndLeftOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (pending : Option (EndToEndLeftOriginRecurrentLeftMacro A package))
    (move : In₂ × In₁)
    (target : EndToEndLeftOriginRecurrentLeftMacro A package)
    (hstaged :
      (stepEndToEndLeftOriginRecurrentRightReceiverFor A package source
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 = some target) :
    let owner : EndToEndLeftOriginRecurrentRightOwnerControl A package :=
      ⟨source, (profiledPolicyRightFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).1⟩
    let receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package :=
      ⟨source, row, (profiledPolicyRightFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).2, pending⟩
    ((EndToEndMatchedPhase.leftOriginRight owner receiver rfl).continue
      A package (move.2, move.1)).2 =
      .leftOriginRight
        ⟨source, (profiledPolicyRightFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).1⟩
        ⟨source, row, (profiledPolicyRightFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).2,
          some target⟩ rfl := by
  dsimp only
  have hafter :
      profiledPolicyRightFiniteStateAfter A (source.2.1.policy A) source.2.2
          (past ++ [move]) =
        stepProfiledPolicyRightFiniteState A (source.2.1.policy A) source.2.2
          (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past) move := by
    simp [profiledPolicyRightFiniteStateAfter, List.foldl_append]
  rw [hafter]
  have hmonitor :
      (stepEndToEndLeftOriginRecurrentRightReceiverFor A package source
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.1 =
      (profiledPolicyRightMonitor A (source.2.1.policy A) source.2.2).step
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2
        (narrowedRecord
          (profiledPolicyRightMonitor A (source.2.1.policy A) source.2.2)
          ((profiledPolicyRightController A (source.2.1.policy A)
            source.2.2).labelOf
              (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
                source.2.2 past).1)
          (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past).2 move) := by
    simp [stepEndToEndLeftOriginRecurrentRightReceiverFor,
      stepProfiledPolicyRightReceiverFor_monitor]
  simp [EndToEndMatchedPhase.continue,
    continueEndToEndLeftOriginRecurrentRightReceiver,
    endToEndLeftOriginRecurrentRightOwnerControlFor,
    stepEndToEndLeftOriginRecurrentRightOwner,
    endToEndGuardedLeftRecurrentRightController,
    stepProfiledPolicyRightFiniteState,
    hmonitor, hstaged]

theorem endToEndLeftOriginLeft_continue_eq_real_phase
    (source : EndToEndLeftOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (pending : Option (EndToEndLeftOriginRecurrentRightMacro A package))
    (move : In₁ × In₂)
    (target : EndToEndLeftOriginRecurrentRightMacro A package)
    (hstaged :
      (stepEndToEndLeftOriginRecurrentLeftReceiverFor A package source
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 = some target) :
    let receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package :=
      ⟨source, row, (profiledPolicyLeftFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).2, pending⟩
    let owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package :=
      ⟨source, (profiledPolicyLeftFiniteStateAfter A
        (source.2.1.policy A) source.2.2 past).1⟩
    ((EndToEndMatchedPhase.leftOriginLeft receiver owner rfl).continue
      A package move).2 =
      .leftOriginLeft
        ⟨source, row, (profiledPolicyLeftFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).2,
          some target⟩
        ⟨source, (profiledPolicyLeftFiniteStateAfter A
          (source.2.1.policy A) source.2.2 (past ++ [move])).1⟩ rfl := by
  dsimp only
  have hafter :
      profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A) source.2.2
          (past ++ [move]) =
        stepProfiledPolicyLeftFiniteState A (source.2.1.policy A) source.2.2
          (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past) move := by
    simp [profiledPolicyLeftFiniteStateAfter, List.foldl_append]
  rw [hafter]
  have hmonitor :
      (stepEndToEndLeftOriginRecurrentLeftReceiverFor A package source
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.1 =
      (profiledPolicyLeftMonitor A (source.2.1.policy A) source.2.2).step
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2
        (narrowedRecord
          (profiledPolicyLeftMonitor A (source.2.1.policy A) source.2.2)
          ((profiledPolicyLeftController A (source.2.1.policy A)
            source.2.2).labelOf
              (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
                source.2.2 past).1)
          (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
            source.2.2 past).2 move) := by
    simp [stepEndToEndLeftOriginRecurrentLeftReceiverFor,
      stepProfiledPolicyLeftReceiverFor_monitor]
  simp [EndToEndMatchedPhase.continue,
    continueEndToEndLeftOriginRecurrentLeftReceiver,
    endToEndLeftOriginRecurrentLeftOwnerControlFor,
    stepEndToEndLeftOriginRecurrentLeftOwner,
    endToEndGuardedLeftRecurrentLeftController,
    stepProfiledPolicyLeftFiniteState,
    hmonitor, hstaged]

/-- Ordinary continuation preserves concrete-prefix reality in all six
phase modes. -/
theorem isRealEndToEndPhase_continue
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (move : In₁ × In₂) :
    IsRealEndToEndPhase A package (phase.continue A package move).2 := by
  rcases hreal with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, pending, rfl⟩
    have hsome := endToEndFirstRight_real_close_staged A package key row past
      (move.2, move.1)
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    left
    refine ⟨key, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealEndToEndFirstRightPhaseAt
    exact endToEndFirstRight_continue_eq_real_phase A package key row past
      (some pending) (move.2, move.1) target hstaged
  · rcases hfirstLeft with ⟨key, row, past, pending, rfl⟩
    have hsome := endToEndFirstLeft_real_close_staged A package key row past move
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    right; left
    refine ⟨key, row, past ++ [move], target, ?_⟩
    unfold IsRealEndToEndFirstLeftPhaseAt
    exact endToEndFirstLeft_continue_eq_real_phase A package key row past
      (some pending) move target hstaged
  · rcases hrightRight with ⟨source, row, past, pending, rfl⟩
    have hsome := endToEndRightOriginRecurrentRight_real_close_staged A package
      source row past (move.2, move.1)
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    right; right; left
    refine ⟨source, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealEndToEndRightOriginRightPhaseAt
    exact endToEndRightOriginRight_continue_eq_real_phase A package source row
      past (some pending) (move.2, move.1) target hstaged
  · rcases hrightLeft with ⟨source, row, past, pending, rfl⟩
    have hsome := endToEndRightOriginRecurrentLeft_real_close_staged A package
      source row past move
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    right; right; right; left
    refine ⟨source, row, past ++ [move], target, ?_⟩
    unfold IsRealEndToEndRightOriginLeftPhaseAt
    exact endToEndRightOriginLeft_continue_eq_real_phase A package source row
      past (some pending) move target hstaged
  · rcases hleftRight with ⟨source, row, past, pending, rfl⟩
    have hsome := endToEndLeftOriginRecurrentRight_real_close_staged A package
      source row past (move.2, move.1)
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    right; right; right; right; left
    refine ⟨source, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealEndToEndLeftOriginRightPhaseAt
    exact endToEndLeftOriginRight_continue_eq_real_phase A package source row
      past (some pending) (move.2, move.1) target hstaged
  · rcases hleftLeft with ⟨source, row, past, pending, rfl⟩
    have hsome := endToEndLeftOriginRecurrentLeft_real_close_staged A package
      source row past move
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    right; right; right; right; right
    refine ⟨source, row, past ++ [move], target, ?_⟩
    unfold IsRealEndToEndLeftOriginLeftPhaseAt
    exact endToEndLeftOriginLeft_continue_eq_real_phase A package source row
      past (some pending) move target hstaged

/-! ## Reality across strict reversals -/

/-- A real right-oriented phase reverses into a real recurrent-left prefix.
The orientation is used only in this proof-level invariant; it is not stored
by either local summary. -/
theorem isRealEndToEndPhase_reverseRightToLeft
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hright : phase.IsRight) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    ∃ next,
      (phase.reverseRightToLeft A package move previouslyReceived).2 =
          some next ∧
        IsRealEndToEndPhase A package next := by
  rcases hreal with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, pending, rfl⟩
    let source : EndToEndRightOriginRecurrentLeftMacro A package :=
      ⟨key, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    have hsome := endToEndRightOriginRecurrentLeft_real_close_staged A package
      source newRow [] move
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    let base : EndToEndMatchedPhase A package := .rightOriginLeft
      (initialEndToEndRightOriginRecurrentLeftReceiver A package source newRow)
      (initialEndToEndRightOriginRecurrentLeftOwner A package source) rfl
    have hbase := endToEndRightOriginLeft_continue_eq_real_phase A package
      source newRow [] none move target hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseRightToLeft,
        switchEndToEndFirstRightOwnerToRecurrentLeftReceiver,
        switchEndToEndFirstRightReceiverToRecurrentLeftOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; left
      refine ⟨source, newRow, [move], target, ?_⟩
      unfold IsRealEndToEndRightOriginLeftPhaseAt
      exact hbase
  · rcases hfirstLeft with ⟨key, row, past, target, hphase⟩
    rw [hphase] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright
  · rcases hrightRight with ⟨source, row, past, pending, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    have hsome := endToEndRightOriginRecurrentLeft_real_close_staged A package
      pending newRow [] move
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    let base : EndToEndMatchedPhase A package := .rightOriginLeft
      (initialEndToEndRightOriginRecurrentLeftReceiver A package pending newRow)
      (initialEndToEndRightOriginRecurrentLeftOwner A package pending) rfl
    have hbase := endToEndRightOriginLeft_continue_eq_real_phase A package
      pending newRow [] none move target hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [newRow, EndToEndMatchedPhase.reverseRightToLeft,
        switchEndToEndRightOriginRightOwnerToLeftReceiver,
        switchEndToEndRightOriginRightReceiverToLeftOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; left
      refine ⟨pending, newRow, [move], target, ?_⟩
      unfold IsRealEndToEndRightOriginLeftPhaseAt
      exact hbase
  · rcases hrightLeft with ⟨source, row, past, target, hphase⟩
    rw [hphase] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright
  · rcases hleftRight with ⟨source, row, past, pending, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    have hsome := endToEndLeftOriginRecurrentLeft_real_close_staged A package
      pending newRow [] move
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    let base : EndToEndMatchedPhase A package := .leftOriginLeft
      (initialEndToEndLeftOriginRecurrentLeftReceiver A package pending newRow)
      (initialEndToEndLeftOriginRecurrentLeftOwner A package pending) rfl
    have hbase := endToEndLeftOriginLeft_continue_eq_real_phase A package
      pending newRow [] none move target hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [newRow, EndToEndMatchedPhase.reverseRightToLeft,
        switchEndToEndLeftOriginRightOwnerToLeftReceiver,
        switchEndToEndLeftOriginRightReceiverToLeftOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; right; right
      refine ⟨pending, newRow, [move], target, ?_⟩
      unfold IsRealEndToEndLeftOriginLeftPhaseAt
      exact hbase
  · rcases hleftLeft with ⟨source, row, past, target, hphase⟩
    rw [hphase] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright

/-- Left-to-right mirror of `isRealEndToEndPhase_reverseRightToLeft`. -/
theorem isRealEndToEndPhase_reverseLeftToRight
    (phase : EndToEndMatchedPhase A package)
    (hreal : IsRealEndToEndPhase A package phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    ∃ next,
      (phase.reverseLeftToRight A package (move.2, move.1)
          previouslyReceived).2 = some next ∧
        IsRealEndToEndPhase A package next := by
  rcases hreal with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, target, hphase⟩
    rw [hphase] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hfirstLeft with ⟨key, row, past, pending, rfl⟩
    let source : EndToEndLeftOriginRecurrentRightMacro A package :=
      ⟨key, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    have hsome := endToEndLeftOriginRecurrentRight_real_close_staged A package
      source newRow [] (move.2, move.1)
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    let base : EndToEndMatchedPhase A package := .leftOriginRight
      (initialEndToEndLeftOriginRecurrentRightOwner A package source)
      (initialEndToEndLeftOriginRecurrentRightReceiver A package source newRow)
      rfl
    have hbase := endToEndLeftOriginRight_continue_eq_real_phase A package
      source newRow [] none (move.2, move.1) target hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseLeftToRight,
        switchEndToEndFirstLeftOwnerToRecurrentRightReceiver,
        switchEndToEndFirstLeftReceiverToRecurrentRightOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; right; left
      refine ⟨source, newRow, [(move.2, move.1)], target, ?_⟩
      unfold IsRealEndToEndLeftOriginRightPhaseAt
      exact hbase
  · rcases hrightRight with ⟨source, row, past, target, hphase⟩
    rw [hphase] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hrightLeft with ⟨source, row, past, pending, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    have hsome := endToEndRightOriginRecurrentRight_real_close_staged A package
      pending newRow [] (move.2, move.1)
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    let base : EndToEndMatchedPhase A package := .rightOriginRight
      (initialEndToEndRightOriginRecurrentRightOwner A package pending)
      (initialEndToEndRightOriginRecurrentRightReceiver A package pending
        newRow) rfl
    have hbase := endToEndRightOriginRight_continue_eq_real_phase A package
      pending newRow [] none (move.2, move.1) target hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [newRow, EndToEndMatchedPhase.reverseLeftToRight,
        switchEndToEndRightOriginLeftOwnerToRightReceiver,
        switchEndToEndRightOriginLeftReceiverToRightOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; left
      refine ⟨pending, newRow, [(move.2, move.1)], target, ?_⟩
      unfold IsRealEndToEndRightOriginRightPhaseAt
      exact hbase
  · rcases hleftRight with ⟨source, row, past, target, hphase⟩
    rw [hphase] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hleftLeft with ⟨source, row, past, pending, rfl⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    have hsome := endToEndLeftOriginRecurrentRight_real_close_staged A package
      pending newRow [] (move.2, move.1)
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    let base : EndToEndMatchedPhase A package := .leftOriginRight
      (initialEndToEndLeftOriginRecurrentRightOwner A package pending)
      (initialEndToEndLeftOriginRecurrentRightReceiver A package pending newRow)
      rfl
    have hbase := endToEndLeftOriginRight_continue_eq_real_phase A package
      pending newRow [] none (move.2, move.1) target hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [newRow, EndToEndMatchedPhase.reverseLeftToRight,
        switchEndToEndLeftOriginLeftOwnerToRightReceiver,
        switchEndToEndLeftOriginLeftReceiverToRightOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; right; left
      refine ⟨pending, newRow, [(move.2, move.1)], target, ?_⟩
      unfold IsRealEndToEndLeftOriginRightPhaseAt
      exact hbase
end


end DetParityAutomaton

end DistributedSynthesis
