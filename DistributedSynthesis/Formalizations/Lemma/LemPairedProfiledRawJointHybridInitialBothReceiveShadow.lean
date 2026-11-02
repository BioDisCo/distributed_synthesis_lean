/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialOneRoundReplacement
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridStagedFrontReceivers

/-!
# Finite receive shadows across repeated initial `both` rounds

After a nonempty initial strict block, the first simultaneous round leaves an
old root receiver at one process and starts the opposite guarded receiver at
the other.  A second simultaneous round delivers the old receiver again, not
the matching owner expected by the new receiver.

The missing information is nevertheless locally computable on the first
simultaneous round.  From the delivered old receiver and the current input
pair, the new receiver can run the same controller label that the hypothetical
nonreceiver would run and retain its next owner control.  The structures below
store that owner dependently over the receiver's exact key.  Further receives
can therefore advance both hypothetical halves while ignoring the delivered
old receiver, which serves only as the honest local phase witness.

The same construction is given for the exact root-pinned immediate phase.
No independent policies are compared, and no graph, orientation, leader, or
strict-leader bit is stored or inspected.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## Guarded phase: initial-left / prospective right receiver -/

/-- Process two's prospective right receiver together with the matching
hypothetical process-one owner.  The dependent field makes key agreement
structural rather than a semantic premise. -/
structure ProfiledRawJointHybridInitialGuardedRightBothShadow where
  receiver : ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
    initialBank
  owner : (initialBank.initialLeft receiver.base.1).controller.Control

noncomputable instance
    profiledRawJointHybridInitialGuardedRightBothShadowFintype :
    Fintype (ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy
      hwin initialBank) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
        initialBank,
    (initialBank.initialLeft receiver.base.1).controller.Control
  let equiv :
      ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- First `both` after an initial-left block.  Besides the actual receiver
output, process two retains the owner that process one would have after the
same input pair. -/
noncomputable def
    startProfiledRawJointHybridInitialGuardedRightBothShadow
    (partner : ProfiledRawJointRootLeftReceiverControl A strategy)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      Option (ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy
        hwin initialBank) :=
  match profiledRawJointInitialLeftStagedKey A strategy partner with
  | none => ((default, default), none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialLeftOwner A strategy
        initialBank key
      let ownerNext := stepProfiledRawJointInitialLeftOwner A strategy
        initialBank initialOwner current.1
      let initialReceiver := initialProfiledRawJointInitialLeftReceiver A
        strategy initialBank key row
      let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
        initialBank key initialOwner.2 initialReceiver.2.2
          (current.2, current.1)
      let receiver :
          ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
            initialBank :=
        ⟨⟨key, row, result.2⟩,
          profiledRawJointHybridInitialLeftPendingOfChild A strategy hwin
            initialBank key (result.1.target row)⟩
      ((pairedRightClosingForRow row result.1.physical,
          pairedRightInformedForRow row result.1.physical),
        some ⟨receiver, ownerNext.2.2⟩)

/-- The new shadow exists exactly when the delivered old receiver carries a
staged guarded key. -/
@[simp] theorem
    startProfiledRawJointHybridInitialGuardedRightBothShadow_isSome
    (partner : ProfiledRawJointRootLeftReceiverControl A strategy)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (startProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
      initialBank partner row current).2.isSome =
      (profiledRawJointInitialLeftStagedKey A strategy partner).isSome := by
  unfold startProfiledRawJointHybridInitialGuardedRightBothShadow
  split <;> simp_all

/-- First-`both` outputs are the two closing projections of the same paired
receiver record.  In particular the process-one component is not the blind
owner output. -/
theorem startProfiledRawJointHybridInitialGuardedRightBothShadow_outputs
    (partner : ProfiledRawJointRootLeftReceiverControl A strategy)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (startProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
      initialBank partner row current).1 =
      match profiledRawJointInitialLeftStagedKey A strategy partner with
      | none => (default, default)
      | some key =>
          let initialOwner := initialProfiledRawJointInitialLeftOwner A
            strategy initialBank key
          let initialReceiver := initialProfiledRawJointInitialLeftReceiver A
            strategy initialBank key row
          let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
            initialBank key initialOwner.2 initialReceiver.2.2
              (current.2, current.1)
          (pairedRightClosingForRow row result.1.physical,
            pairedRightInformedForRow row result.1.physical) := by
  unfold startProfiledRawJointHybridInitialGuardedRightBothShadow
  split <;> simp_all

/-- A further `both` advances the stored matched owner/receiver pair.  The
delivered old receiver is deliberately not interpreted as an owner. -/
noncomputable def
    stepProfiledRawJointHybridInitialGuardedRightBothShadow
    (state : ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy
      hwin initialBank)
    (_deliveredOld : ProfiledRawJointRootLeftReceiverControl A strategy)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
        initialBank :=
  let key := state.receiver.base.1
  let row := state.receiver.base.2.1
  let controller := (initialBank.initialLeft key).controller
  let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
    initialBank key state.owner state.receiver.base.2.2
      (current.2, current.1)
  let receiver :
      ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
        initialBank :=
    ⟨⟨key, row, result.2⟩,
      profiledRawJointHybridInitialLeftPendingOfChild A strategy hwin
        initialBank key (result.1.target row)⟩
  ((pairedRightClosingForRow row result.1.physical,
      pairedRightInformedForRow row result.1.physical),
    ⟨receiver, controller.step state.owner current.1⟩)

@[simp] theorem
    stepProfiledRawJointHybridInitialGuardedRightBothShadow_key
    (state : ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy
      hwin initialBank)
    (deliveredOld : ProfiledRawJointRootLeftReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
      initialBank state deliveredOld current).2.receiver.base.1 =
      state.receiver.base.1 := by
  rfl

@[simp] theorem
    stepProfiledRawJointHybridInitialGuardedRightBothShadow_row
    (state : ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy
      hwin initialBank)
    (deliveredOld : ProfiledRawJointRootLeftReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
      initialBank state deliveredOld current).2.receiver.base.2.1 =
      state.receiver.base.2.1 := by
  rfl

/-- The repeated-`both` pair is the complete closing pair of one controller
record.  This deliberately does not identify the blind sender output with the
closing output. -/
theorem stepProfiledRawJointHybridInitialGuardedRightBothShadow_outputs
    (state : ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy
      hwin initialBank)
    (deliveredOld : ProfiledRawJointRootLeftReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
      initialBank state deliveredOld current).1 =
      let key := state.receiver.base.1
      let row := state.receiver.base.2.1
      let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
        initialBank key state.owner state.receiver.base.2.2
          (current.2, current.1)
      (pairedRightClosingForRow row result.1.physical,
        pairedRightInformedForRow row result.1.physical) := by
  rfl

/-! ## Guarded mirror: initial-right / prospective left receiver -/

/-- Process one's prospective left receiver and matching hypothetical
process-two owner. -/
structure ProfiledRawJointHybridInitialGuardedLeftBothShadow where
  receiver : ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
    initialBank
  owner : (initialBank.initialRight receiver.base.1).controller.Control

noncomputable instance
    profiledRawJointHybridInitialGuardedLeftBothShadowFintype :
    Fintype (ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy
      hwin initialBank) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
        initialBank,
    (initialBank.initialRight receiver.base.1).controller.Control
  let equiv :
      ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable def
    startProfiledRawJointHybridInitialGuardedLeftBothShadow
    (partner : ProfiledRawJointRootRightReceiverControl A strategy)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      Option (ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy
        hwin initialBank) :=
  match profiledRawJointInitialRightStagedKey A strategy partner with
  | none => ((default, default), none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialRightOwner A strategy
        initialBank key
      let ownerNext := stepProfiledRawJointInitialRightOwner A strategy
        initialBank initialOwner current.2
      let initialReceiver := initialProfiledRawJointInitialRightReceiver A
        strategy initialBank key row
      let result := stepProfiledRawJointInitialRightReceiverFor A strategy
        initialBank key initialOwner.2 initialReceiver.2.2 current
      let receiver :
          ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
            initialBank :=
        ⟨⟨key, row, result.2⟩,
          profiledRawJointHybridInitialRightPendingOfChild A strategy hwin
            initialBank key (result.1.target row)⟩
      ((pairedLeftInformedForRow row result.1.physical,
          pairedLeftClosingForRow row result.1.physical),
        some ⟨receiver, ownerNext.2.2⟩)

@[simp] theorem
    startProfiledRawJointHybridInitialGuardedLeftBothShadow_isSome
    (partner : ProfiledRawJointRootRightReceiverControl A strategy)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (startProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy hwin
      initialBank partner row current).2.isSome =
      (profiledRawJointInitialRightStagedKey A strategy partner).isSome := by
  unfold startProfiledRawJointHybridInitialGuardedLeftBothShadow
  split <;> simp_all

theorem startProfiledRawJointHybridInitialGuardedLeftBothShadow_outputs
    (partner : ProfiledRawJointRootRightReceiverControl A strategy)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (startProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy hwin
      initialBank partner row current).1 =
      match profiledRawJointInitialRightStagedKey A strategy partner with
      | none => (default, default)
      | some key =>
          let initialOwner := initialProfiledRawJointInitialRightOwner A
            strategy initialBank key
          let initialReceiver := initialProfiledRawJointInitialRightReceiver A
            strategy initialBank key row
          let result := stepProfiledRawJointInitialRightReceiverFor A strategy
            initialBank key initialOwner.2 initialReceiver.2.2 current
          (pairedLeftInformedForRow row result.1.physical,
            pairedLeftClosingForRow row result.1.physical) := by
  unfold startProfiledRawJointHybridInitialGuardedLeftBothShadow
  split <;> simp_all

noncomputable def
    stepProfiledRawJointHybridInitialGuardedLeftBothShadow
    (state : ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy
      hwin initialBank)
    (_deliveredOld : ProfiledRawJointRootRightReceiverControl A strategy)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy hwin
        initialBank :=
  let key := state.receiver.base.1
  let row := state.receiver.base.2.1
  let controller := (initialBank.initialRight key).controller
  let result := stepProfiledRawJointInitialRightReceiverFor A strategy
    initialBank key state.owner state.receiver.base.2.2 current
  let receiver :
      ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
        initialBank :=
    ⟨⟨key, row, result.2⟩,
      profiledRawJointHybridInitialRightPendingOfChild A strategy hwin
        initialBank key (result.1.target row)⟩
  ((pairedLeftInformedForRow row result.1.physical,
      pairedLeftClosingForRow row result.1.physical),
    ⟨receiver, controller.step state.owner current.2⟩)

@[simp] theorem
    stepProfiledRawJointHybridInitialGuardedLeftBothShadow_key
    (state : ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy
      hwin initialBank)
    (deliveredOld : ProfiledRawJointRootRightReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy hwin
      initialBank state deliveredOld current).2.receiver.base.1 =
      state.receiver.base.1 := by
  rfl

@[simp] theorem
    stepProfiledRawJointHybridInitialGuardedLeftBothShadow_row
    (state : ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy
      hwin initialBank)
    (deliveredOld : ProfiledRawJointRootRightReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy hwin
      initialBank state deliveredOld current).2.receiver.base.2.1 =
      state.receiver.base.2.1 := by
  rfl

/-- Guarded-left complete closing-pair mirror. -/
theorem stepProfiledRawJointHybridInitialGuardedLeftBothShadow_outputs
    (state : ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy
      hwin initialBank)
    (deliveredOld : ProfiledRawJointRootRightReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy hwin
      initialBank state deliveredOld current).1 =
      let key := state.receiver.base.1
      let row := state.receiver.base.2.1
      let result := stepProfiledRawJointInitialRightReceiverFor A strategy
        initialBank key state.owner state.receiver.base.2.2 current
      (pairedLeftInformedForRow row result.1.physical,
        pairedLeftClosingForRow row result.1.physical) := by
  rfl

/-! ## Exact root-pinned immediate phase -/

/-- Root-pinned right receiver with the exact hypothetical owner at the same
finite root-input index. -/
structure ProfiledRawJointHybridInitialPinnedRightBothShadow where
  receiver : ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
    hwin
  owner : ProfiledRawJointHybridInitialImmediateRightOwnerAt A strategy hwin
    receiver.first

noncomputable instance
    profiledRawJointHybridInitialPinnedRightBothShadowFintype :
    Fintype (ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy
      hwin) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin,
    ProfiledRawJointHybridInitialImmediateRightOwnerAt A strategy hwin
      receiver.first
  let equiv :
      ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin ≃
        Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Root-shadow first `both`: both hypothetical halves come from one exact
root-pinned controller record. -/
noncomputable def startProfiledRawJointHybridInitialPinnedRightBothShadow
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin :=
  let owner := profiledRawJointHybridInitialOneShadowNoRecv A strategy hwin
    controllers shadow current.1
  let receiver := profiledRawJointHybridInitialOneShadowRecvTwo A strategy
    hwin controllers shadow row current.2 current.1
  let first := shadow.common.1
  let monitor :=
    profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  let record := narrowedRecord monitor (controller.labeledTree [])
    monitor.initial (current.2, current.1)
  ((pairedRightClosingForRow row record.2.1.physical,
      pairedRightInformedForRow row record.2.1.physical),
    ⟨receiver.2, owner.2.owner⟩)

theorem startProfiledRawJointHybridInitialPinnedRightBothShadow_outputs
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (startProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin
      controllers shadow row current).1 =
      let first := shadow.common.1
      let monitor :=
        profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
      let controller :=
        profiledRawJointHybridInitialImmediateRightController A strategy hwin
          first
      let record := narrowedRecord monitor (controller.labeledTree [])
        monitor.initial (current.2, current.1)
      (pairedRightClosingForRow row record.2.1.physical,
        pairedRightInformedForRow row record.2.1.physical) := by
  rfl

/-- Consecutive `both` in the pinned branch; the delivered old receiver is a
phase witness, while the exact stored owner drives the receiver label. -/
noncomputable def stepProfiledRawJointHybridInitialPinnedRightBothShadow
    (state : ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin)
    (_deliveredOld : ProfiledRawJointRootLeftReceiverControl A strategy)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin :=
  let first := state.receiver.first
  let row := state.receiver.row
  let monitor :=
    profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  let label := controller.labelOf state.owner
  let output := label.2 state.receiver.receiver (current.2, current.1)
  let record := ((current.2, current.1), output, label.1 current.1)
  let receiver :
      ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin :=
    ⟨first, row, monitor.step state.receiver.receiver record,
      profiledRawJointHybridInitialImmediateRightStageOfChild A strategy hwin
        first (output.target row)⟩
  ((pairedRightClosingForRow row output.physical,
      pairedRightInformedForRow row output.physical),
    ⟨receiver, controller.step state.owner current.1⟩)

@[simp] theorem stepProfiledRawJointHybridInitialPinnedRightBothShadow_first
    (state : ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin)
    (deliveredOld : ProfiledRawJointRootLeftReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin
      state deliveredOld current).2.receiver.first = state.receiver.first :=
  rfl

/-- The pinned repeated-`both` pair uses the closing and informed projections
of one exact root-pinned record. -/
theorem stepProfiledRawJointHybridInitialPinnedRightBothShadow_outputs
    (state : ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin)
    (deliveredOld : ProfiledRawJointRootLeftReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialPinnedRightBothShadow A strategy hwin
      state deliveredOld current).1 =
      let first := state.receiver.first
      let row := state.receiver.row
      let controller :=
        profiledRawJointHybridInitialImmediateRightController A strategy hwin
          first
      let output := (controller.labelOf state.owner).2
        state.receiver.receiver (current.2, current.1)
      (pairedRightClosingForRow row output.physical,
        pairedRightInformedForRow row output.physical) := by
  rfl

/-- Pinned left mirror. -/
structure ProfiledRawJointHybridInitialPinnedLeftBothShadow where
  receiver : ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
    hwin
  owner : ProfiledRawJointHybridInitialImmediateLeftOwnerAt A strategy hwin
    receiver.first

noncomputable instance
    profiledRawJointHybridInitialPinnedLeftBothShadowFintype :
    Fintype (ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy
      hwin) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin,
    ProfiledRawJointHybridInitialImmediateLeftOwnerAt A strategy hwin
      receiver.first
  let equiv :
      ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin ≃
        Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable def startProfiledRawJointHybridInitialPinnedLeftBothShadow
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin :=
  let receiver := profiledRawJointHybridInitialTwoShadowRecvOne A strategy
    hwin controllers shadow row current.1 current.2
  let owner := profiledRawJointHybridInitialTwoShadowNoRecv A strategy hwin
    controllers shadow current.2
  let first := shadow.common.1
  let monitor :=
    profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  let record := narrowedRecord monitor (controller.labeledTree [])
    monitor.initial current
  ((pairedLeftInformedForRow row record.2.1.physical,
      pairedLeftClosingForRow row record.2.1.physical),
    ⟨receiver.2, owner.2.owner⟩)

theorem startProfiledRawJointHybridInitialPinnedLeftBothShadow_outputs
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (startProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin
      controllers shadow row current).1 =
      let first := shadow.common.1
      let monitor :=
        profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
      let controller :=
        profiledRawJointHybridInitialImmediateLeftController A strategy hwin
          first
      let record := narrowedRecord monitor (controller.labeledTree [])
        monitor.initial current
      (pairedLeftInformedForRow row record.2.1.physical,
        pairedLeftClosingForRow row record.2.1.physical) := by
  rfl

noncomputable def stepProfiledRawJointHybridInitialPinnedLeftBothShadow
    (state : ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin)
    (_deliveredOld : ProfiledRawJointRootRightReceiverControl A strategy)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin :=
  let first := state.receiver.first
  let row := state.receiver.row
  let monitor :=
    profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  let label := controller.labelOf state.owner
  let output := label.2 state.receiver.receiver current
  let record := (current, output, label.1 current.2)
  let receiver :
      ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin :=
    ⟨first, row, monitor.step state.receiver.receiver record,
      profiledRawJointHybridInitialImmediateLeftStageOfChild A strategy hwin
        first (output.target row)⟩
  ((pairedLeftInformedForRow row output.physical,
      pairedLeftClosingForRow row output.physical),
    ⟨receiver, controller.step state.owner current.2⟩)

@[simp] theorem stepProfiledRawJointHybridInitialPinnedLeftBothShadow_first
    (state : ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin)
    (deliveredOld : ProfiledRawJointRootRightReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin
      state deliveredOld current).2.receiver.first = state.receiver.first :=
  rfl

/-- Pinned-left complete closing-pair mirror. -/
theorem stepProfiledRawJointHybridInitialPinnedLeftBothShadow_outputs
    (state : ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin)
    (deliveredOld : ProfiledRawJointRootRightReceiverControl A strategy)
    (current : In₁ × In₂) :
    (stepProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy hwin
      state deliveredOld current).1 =
      let first := state.receiver.first
      let row := state.receiver.row
      let controller :=
        profiledRawJointHybridInitialImmediateLeftController A strategy hwin
          first
      let output := (controller.labelOf state.owner).2
        state.receiver.receiver current
      (pairedLeftInformedForRow row output.physical,
        pairedLeftClosingForRow row output.physical) := by
  rfl

/-! ## Finite branch sums consumed by the future front adapter -/

/-- The two honest process-two right-receiver phases. -/
inductive ProfiledRawJointHybridInitialRightBothShadow where
  | guarded
      (state : ProfiledRawJointHybridInitialGuardedRightBothShadow A strategy
        hwin initialBank)
  | pinned
      (state : ProfiledRawJointHybridInitialPinnedRightBothShadow A strategy
        hwin)
deriving Fintype

/-- Process-one left-receiver mirror. -/
inductive ProfiledRawJointHybridInitialLeftBothShadow where
  | guarded
      (state : ProfiledRawJointHybridInitialGuardedLeftBothShadow A strategy
        hwin initialBank)
  | pinned
      (state : ProfiledRawJointHybridInitialPinnedLeftBothShadow A strategy
        hwin)
deriving Fintype

end


end DetParityAutomaton

end DistributedSynthesis
