/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridStagedFrontReceivers

/-!
# Self-powered staged receivers at a repeated simultaneous round

After the first simultaneous receive at the end of a strict block, the new
guarded receiver may receive another receiver on the next round.  It therefore
cannot rely on the matching owner being delivered.  The matching owner is,
however, already computable at the first receive from exactly the same local
data: the delivered input and the controller root/owner that initialized the
receiver.

The finite wrappers below retain that owner control beside the staged exact
child/root.  A receive advances both components internally.  No graph,
orientation, leader flag, or partner-input history is stored.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## Old-initial guarded receivers -/

/-- The exceptional-right receiver plus the matching right owner control that
was advanced on the same local receive. -/
structure ProfiledRawJointHybridPoweredInitialLeftReceiver where
  receiver : ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
    initialBank
  owner : (initialBank.initialLeft receiver.base.1).controller.Control

/-- Exceptional-left mirror. -/
structure ProfiledRawJointHybridPoweredInitialRightReceiver where
  receiver : ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
    initialBank
  owner : (initialBank.initialRight receiver.base.1).controller.Control

noncomputable instance
    profiledRawJointHybridPoweredInitialLeftReceiverFintype :
    Fintype (ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
      initialBank) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
        initialBank,
    (initialBank.initialLeft receiver.base.1).controller.Control
  let equiv :
      ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridPoweredInitialRightReceiverFintype :
    Fintype (ProfiledRawJointHybridPoweredInitialRightReceiver A strategy hwin
      initialBank) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
        initialBank,
    (initialBank.initialRight receiver.base.1).controller.Control
  let equiv :
      ProfiledRawJointHybridPoweredInitialRightReceiver A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- First exceptional-right receive, retaining the matching advanced owner. -/
noncomputable def startProfiledRawJointHybridPoweredInitialLeftReceiver
    (partner : ProfiledRawJointRootLeftReceiverControl A strategy)
    (row : PairedEntryRow) (move : In₂ × In₁) :
    Out₂ × Option
      (ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointInitialLeftStagedKey A strategy partner with
  | none => (default, none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialLeftOwner A strategy
        initialBank key
      let initialReceiver := initialProfiledRawJointInitialLeftReceiver A
        strategy initialBank key row
      let controller := (initialBank.initialLeft key).controller
      let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
        initialBank key initialOwner.2 initialReceiver.2.2 move
      let receiver :
          ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
            initialBank :=
        ⟨⟨key, row, result.2⟩,
          profiledRawJointHybridInitialLeftPendingOfChild A strategy hwin
            initialBank key (result.1.target row)⟩
      (pairedRightInformedForRow row result.1.physical,
        some ⟨receiver, controller.step initialOwner.2 move.2⟩)

/-- First exceptional-left receive mirror. -/
noncomputable def startProfiledRawJointHybridPoweredInitialRightReceiver
    (partner : ProfiledRawJointRootRightReceiverControl A strategy)
    (row : PairedEntryRow) (move : In₁ × In₂) :
    Out₁ × Option
      (ProfiledRawJointHybridPoweredInitialRightReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointInitialRightStagedKey A strategy partner with
  | none => (default, none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialRightOwner A strategy
        initialBank key
      let initialReceiver := initialProfiledRawJointInitialRightReceiver A
        strategy initialBank key row
      let controller := (initialBank.initialRight key).controller
      let result := stepProfiledRawJointInitialRightReceiverFor A strategy
        initialBank key initialOwner.2 initialReceiver.2.2 move
      let receiver :
          ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
            initialBank :=
        ⟨⟨key, row, result.2⟩,
          profiledRawJointHybridInitialRightPendingOfChild A strategy hwin
            initialBank key (result.1.target row)⟩
      (pairedLeftInformedForRow row result.1.physical,
        some ⟨receiver, controller.step initialOwner.2 move.2⟩)

/-- Advance an exceptional-right receiver and its retained matching owner on
one receive, irrespective of whether the delivered local control was itself
an owner or a receiver. -/
noncomputable def
    advanceProfiledRawJointHybridPoweredInitialLeftReceiver
    (state : ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
      initialBank)
    (move : In₂ × In₁) :
    Out₂ × ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy
      hwin initialBank :=
  let key := state.receiver.base.1
  let row := state.receiver.base.2.1
  let controller := (initialBank.initialLeft key).controller
  let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
    initialBank key state.owner state.receiver.base.2.2 move
  let receiver :
      ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
        initialBank :=
    ⟨⟨key, row, result.2⟩,
      profiledRawJointHybridInitialLeftPendingOfChild A strategy hwin
        initialBank key (result.1.target row)⟩
  (pairedRightInformedForRow row result.1.physical,
    ⟨receiver, controller.step state.owner move.2⟩)

/-- Exceptional-left mirror self-powered advance. -/
noncomputable def
    advanceProfiledRawJointHybridPoweredInitialRightReceiver
    (state : ProfiledRawJointHybridPoweredInitialRightReceiver A strategy hwin
      initialBank)
    (move : In₁ × In₂) :
    Out₁ × ProfiledRawJointHybridPoweredInitialRightReceiver A strategy
      hwin initialBank :=
  let key := state.receiver.base.1
  let row := state.receiver.base.2.1
  let controller := (initialBank.initialRight key).controller
  let result := stepProfiledRawJointInitialRightReceiverFor A strategy
    initialBank key state.owner state.receiver.base.2.2 move
  let receiver :
      ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
        initialBank :=
    ⟨⟨key, row, result.2⟩,
      profiledRawJointHybridInitialRightPendingOfChild A strategy hwin
        initialBank key (result.1.target row)⟩
  (pairedLeftInformedForRow row result.1.physical,
    ⟨receiver, controller.step state.owner move.2⟩)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    advanceProfiledRawJointHybridPoweredInitialLeftReceiver_key
    (state : ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
      initialBank)
    (move : In₂ × In₁) :
    (advanceProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
      initialBank state move).2.receiver.base.1 = state.receiver.base.1 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    advanceProfiledRawJointHybridPoweredInitialRightReceiver_key
    (state : ProfiledRawJointHybridPoweredInitialRightReceiver A strategy hwin
      initialBank)
    (move : In₁ × In₂) :
    (advanceProfiledRawJointHybridPoweredInitialRightReceiver A strategy hwin
      initialBank state move).2.receiver.base.1 = state.receiver.base.1 :=
  rfl

/-! ## Common guarded receivers -/

/-- A common strict-left receiver retaining its matching left owner. -/
structure ProfiledRawJointHybridPoweredLeftStrictReceiver where
  receiver : ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin
  owner : (profiledRawJointHybridShadowLeftController A strategy hwin
    receiver.base.origin).Control

/-- Common strict-right mirror. -/
structure ProfiledRawJointHybridPoweredRightStrictReceiver where
  receiver : ProfiledRawJointHybridStagedRightStrictReceiver A strategy hwin
  owner : (profiledRawJointHybridShadowRightController A strategy hwin
    receiver.base.origin).Control

noncomputable instance profiledRawJointHybridPoweredLeftStrictReceiverFintype :
    Fintype (ProfiledRawJointHybridPoweredLeftStrictReceiver A strategy
      hwin) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin,
    (profiledRawJointHybridShadowLeftController A strategy hwin
      receiver.base.origin).Control
  let equiv : ProfiledRawJointHybridPoweredLeftStrictReceiver A strategy hwin ≃
      Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointHybridPoweredRightStrictReceiverFintype :
    Fintype (ProfiledRawJointHybridPoweredRightStrictReceiver A strategy
      hwin) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointHybridStagedRightStrictReceiver A strategy hwin,
    (profiledRawJointHybridShadowRightController A strategy hwin
      receiver.base.origin).Control
  let equiv :
      ProfiledRawJointHybridPoweredRightStrictReceiver A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨receiver, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Resolve a common process-one shadow and retain the advanced matching left
owner beside the staged strict receiver. -/
noncomputable def profiledRawJointHybridOneShadowRecvLeftOwnerPowered
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridPoweredLeftStrictReceiver A strategy
      hwin :=
  let monitor := ProfiledRawJointHybridShadowLeftMonitor A strategy hwin
    shadow.origin
  let controller := profiledRawJointHybridShadowLeftController A strategy hwin
    shadow.origin
  let ownerControl := profiledRawJointHybridLeftGuardOwnerFor A strategy hwin
    shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (ownInput, deliveredInput)
  let receiver :
      ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin :=
    ⟨⟨shadow.origin,
      monitor.step shadow.strictReceiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonLeftPendingOfChild A strategy hwin
        shadow.origin (output.target .both)⟩
  (pairedLeftInformedForRow .both output.physical,
    ⟨receiver, controller.step ownerControl deliveredInput⟩)

/-- Process-two common mirror powered entry. -/
noncomputable def profiledRawJointHybridTwoShadowRecvRightOwnerPowered
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridPoweredRightStrictReceiver A strategy
      hwin :=
  let monitor := ProfiledRawJointHybridShadowRightMonitor A strategy hwin
    shadow.origin
  let controller := profiledRawJointHybridShadowRightController A strategy hwin
    shadow.origin
  let ownerControl := profiledRawJointHybridRightGuardOwnerFor A strategy hwin
    shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (ownInput, deliveredInput)
  let receiver :
      ProfiledRawJointHybridStagedRightStrictReceiver A strategy hwin :=
    ⟨⟨shadow.origin,
      monitor.step shadow.strictReceiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonRightPendingOfChild A strategy hwin
        shadow.origin (output.target .both)⟩
  (pairedRightInformedForRow .both output.physical,
    ⟨receiver, controller.step ownerControl deliveredInput⟩)

/-- Self-powered common strict-left continuation. -/
noncomputable def advanceProfiledRawJointHybridPoweredLeftStrictReceiver
    (state : ProfiledRawJointHybridPoweredLeftStrictReceiver A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridPoweredLeftStrictReceiver A strategy
      hwin :=
  let origin := state.receiver.base.origin
  let monitor := ProfiledRawJointHybridShadowLeftMonitor A strategy hwin origin
  let controller := profiledRawJointHybridShadowLeftController A strategy hwin
    origin
  let label := controller.labelOf state.owner
  let output := label.2 state.receiver.base.receiver
    (ownInput, deliveredInput)
  let receiver :
      ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin :=
    ⟨⟨origin,
      monitor.step state.receiver.base.receiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonLeftPendingOfChild A strategy hwin origin
        (output.target .both)⟩
  (pairedLeftInformedForRow .both output.physical,
    ⟨receiver, controller.step state.owner deliveredInput⟩)

/-- Common strict-right mirror continuation. -/
noncomputable def advanceProfiledRawJointHybridPoweredRightStrictReceiver
    (state : ProfiledRawJointHybridPoweredRightStrictReceiver A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridPoweredRightStrictReceiver A strategy
      hwin :=
  let origin := state.receiver.base.origin
  let monitor := ProfiledRawJointHybridShadowRightMonitor A strategy hwin origin
  let controller := profiledRawJointHybridShadowRightController A strategy hwin
    origin
  let label := controller.labelOf state.owner
  let output := label.2 state.receiver.base.receiver
    (ownInput, deliveredInput)
  let receiver :
      ProfiledRawJointHybridStagedRightStrictReceiver A strategy hwin :=
    ⟨⟨origin,
      monitor.step state.receiver.base.receiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonRightPendingOfChild A strategy hwin origin
        (output.target .both)⟩
  (pairedRightInformedForRow .both output.physical,
    ⟨receiver, controller.step state.owner deliveredInput⟩)

@[simp] theorem advanceProfiledRawJointHybridPoweredLeftStrictReceiver_origin
    (state : ProfiledRawJointHybridPoweredLeftStrictReceiver A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    (advanceProfiledRawJointHybridPoweredLeftStrictReceiver A strategy hwin
      state ownInput deliveredInput).2.receiver.base.origin =
      state.receiver.base.origin :=
  rfl

@[simp] theorem advanceProfiledRawJointHybridPoweredRightStrictReceiver_origin
    (state : ProfiledRawJointHybridPoweredRightStrictReceiver A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    (advanceProfiledRawJointHybridPoweredRightStrictReceiver A strategy hwin
      state ownInput deliveredInput).2.receiver.base.origin =
      state.receiver.base.origin :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
