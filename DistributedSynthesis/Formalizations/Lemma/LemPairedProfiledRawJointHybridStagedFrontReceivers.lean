/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaChildFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridLeaderFreeShadowCarrier

/-!
# Exact pending children in the pre-recurrent receiver controls

A strict receiver which later observes `noRecv` must restart from the exact
literal child emitted by its preceding receive.  The sticky block monitor
stores only that child's projected profile; the exact child cannot be
reconstructed from the profile.  This file therefore adds precisely the
finite pending-child field used by the ordinary recurrent receiver controls.

The field is refreshed directly from the current controller label's
`target row`.  It is not a graph, orientation, or leader signal.
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

/-! ## Old initial guarded receivers -/

/-- Exact staged left root after an old exceptional-right receive. -/
abbrev ProfiledRawJointHybridInitialLeftPending
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :=
  Σ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointInitialLeftSelectedSource A strategy initialBank key),
    ProfiledRawJointUnitLeftPolicyMacro A strategy child.1
      ((initialBank.initialLeft key).activation.childPolicyBank A hwin child)

/-- Exact staged right root after an old exceptional-left receive. -/
abbrev ProfiledRawJointHybridInitialRightPending
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :=
  Σ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointInitialRightSelectedSource A strategy initialBank key),
    ProfiledRawJointUnitRightPolicyMacro A strategy child.1
      ((initialBank.initialRight key).activation.childPolicyBank A hwin child)

/-- Inspect the exact child's active lane and, when it is live, retain the
corresponding exact ordinary left-policy root. -/
noncomputable def profiledRawJointHybridInitialLeftPendingOfChild
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointInitialLeftSelectedSource A strategy initialBank key)) :
    Option (ProfiledRawJointHybridInitialLeftPending A strategy hwin
      initialBank key) := by
  classical
  by_cases hlive : ∃ slot, child.1.family.left () = some slot
  · let slot := Classical.choose hlive
    let hslot := Classical.choose_spec hlive
    exact some ⟨child,
      profiledRawJointLiteralChildLeftPolicyRoot A strategy
        (ProfiledRawJointInitialLeftSelectedSource A strategy initialBank key)
        ((initialBank.initialLeft key).activation.childPolicyBank A hwin)
        child slot hslot⟩
  · exact none

/-- Right-root mirror lane inspection. -/
noncomputable def profiledRawJointHybridInitialRightPendingOfChild
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointInitialRightSelectedSource A strategy initialBank key)) :
    Option (ProfiledRawJointHybridInitialRightPending A strategy hwin
      initialBank key) := by
  classical
  by_cases hlive : ∃ slot, child.1.family.right () = some slot
  · let slot := Classical.choose hlive
    let hslot := Classical.choose_spec hlive
    exact some ⟨child,
      profiledRawJointLiteralChildRightPolicyRoot A strategy
        (ProfiledRawJointInitialRightSelectedSource A strategy initialBank key)
        ((initialBank.initialRight key).activation.childPolicyBank A hwin)
        child slot hslot⟩
  · exact none

/-- Process two's exceptional-right receiver, enriched by the exact literal
child and exact left root emitted at its latest receive. -/
structure ProfiledRawJointHybridStagedInitialLeftReceiver where
  base : ProfiledRawJointInitialLeftReceiverControl.{u, v, x, y, s,
    max u v x y s} A strategy initialBank
  pending : Option (ProfiledRawJointHybridInitialLeftPending A strategy hwin
    initialBank base.1)

/-- Process one's exceptional-left receiver mirror. -/
structure ProfiledRawJointHybridStagedInitialRightReceiver where
  base : ProfiledRawJointInitialRightReceiverControl.{u, v, x, y, s,
    max u v x y s} A strategy initialBank
  pending : Option (ProfiledRawJointHybridInitialRightPending A strategy hwin
    initialBank base.1)

noncomputable instance
    profiledRawJointHybridStagedInitialLeftReceiverFintype :
    Fintype (ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
      initialBank) := by
  classical
  let Rep := Σ base : ProfiledRawJointInitialLeftReceiverControl.{u, v, x,
    y, s, max u v x y s} A strategy initialBank,
      Option (ProfiledRawJointHybridInitialLeftPending A strategy hwin
        initialBank base.1)
  let equiv :
      ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin initialBank ≃
        Rep := {
    toFun := fun state ↦ ⟨state.base, state.pending⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨base, child⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridStagedInitialRightReceiverFintype :
    Fintype (ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
      initialBank) := by
  classical
  let Rep := Σ base : ProfiledRawJointInitialRightReceiverControl.{u, v, x,
    y, s, max u v x y s} A strategy initialBank,
      Option (ProfiledRawJointHybridInitialRightPending A strategy hwin
        initialBank base.1)
  let equiv :
      ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin initialBank ≃
        Rep := {
    toFun := fun state ↦ ⟨state.base, state.pending⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨base, child⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Interpret an exceptional-right owner at the receiver's dependent key.
The mismatch branch only totalizes off-invariant control pairs. -/
noncomputable def profiledRawJointHybridInitialLeftOwnerFor
    (receiver : ProfiledRawJointHybridStagedInitialLeftReceiver A strategy
      hwin initialBank)
    (owner : ProfiledRawJointInitialLeftOwnerControl A strategy initialBank) :
    (initialBank.initialLeft receiver.base.1).controller.Control := by
  classical
  exact if h : owner.1 = receiver.base.1 then h ▸ owner.2
    else (initialBank.initialLeft receiver.base.1).controller.initial

/-- Initial-right/left-block mirror alignment. -/
noncomputable def profiledRawJointHybridInitialRightOwnerFor
    (receiver : ProfiledRawJointHybridStagedInitialRightReceiver A strategy
      hwin initialBank)
    (owner : ProfiledRawJointInitialRightOwnerControl A strategy initialBank) :
    (initialBank.initialRight receiver.base.1).controller.Control := by
  classical
  exact if h : owner.1 = receiver.base.1 then h ▸ owner.2
    else (initialBank.initialRight receiver.base.1).controller.initial

/-- Start the old exceptional-right receiver from a delivered root-left
receiver and stage the exact target emitted by that very first step. -/
noncomputable def startProfiledRawJointHybridStagedInitialLeftReceiver
    (partner : ProfiledRawJointRootLeftReceiverControl A strategy)
    (row : PairedEntryRow) (move : In₂ × In₁) :
    Out₂ × Option
      (ProfiledRawJointHybridStagedInitialLeftReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointInitialLeftStagedKey A strategy partner with
  | none => (default, none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialLeftOwner A strategy
        initialBank key
      let initialReceiver := initialProfiledRawJointInitialLeftReceiver A
        strategy initialBank key row
      let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
        initialBank key initialOwner.2 initialReceiver.2.2 move
      (pairedRightInformedForRow row result.1.physical,
        some ⟨⟨key, row, result.2⟩,
          profiledRawJointHybridInitialLeftPendingOfChild A strategy hwin
            initialBank key (result.1.target row)⟩)

/-- Old exceptional-left staged start mirror. -/
noncomputable def startProfiledRawJointHybridStagedInitialRightReceiver
    (partner : ProfiledRawJointRootRightReceiverControl A strategy)
    (row : PairedEntryRow) (move : In₁ × In₂) :
    Out₁ × Option
      (ProfiledRawJointHybridStagedInitialRightReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointInitialRightStagedKey A strategy partner with
  | none => (default, none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialRightOwner A strategy
        initialBank key
      let initialReceiver := initialProfiledRawJointInitialRightReceiver A
        strategy initialBank key row
      let result := stepProfiledRawJointInitialRightReceiverFor A strategy
        initialBank key initialOwner.2 initialReceiver.2.2 move
      (pairedLeftInformedForRow row result.1.physical,
        some ⟨⟨key, row, result.2⟩,
          profiledRawJointHybridInitialRightPendingOfChild A strategy hwin
            initialBank key (result.1.target row)⟩)

/-- Continue the old exceptional-right receiver and refresh its exact pending
child from the same controller label used for the physical output. -/
noncomputable def
    continueProfiledRawJointHybridStagedInitialLeftReceiver
    (receiver : ProfiledRawJointHybridStagedInitialLeftReceiver A strategy
      hwin initialBank)
    (owner : ProfiledRawJointInitialLeftOwnerControl A strategy initialBank)
    (move : In₂ × In₁) :
    Out₂ × ProfiledRawJointHybridStagedInitialLeftReceiver A strategy
      hwin initialBank :=
  let key := receiver.base.1
  let row := receiver.base.2.1
  let result := stepProfiledRawJointInitialLeftReceiverFor A strategy
    initialBank key
      (profiledRawJointHybridInitialLeftOwnerFor A strategy hwin initialBank
        receiver owner)
      receiver.base.2.2 move
  (pairedRightInformedForRow row result.1.physical,
    ⟨⟨key, row, result.2⟩,
      profiledRawJointHybridInitialLeftPendingOfChild A strategy hwin
        initialBank key (result.1.target row)⟩)

/-- Old exceptional-left receiver mirror. -/
noncomputable def
    continueProfiledRawJointHybridStagedInitialRightReceiver
    (receiver : ProfiledRawJointHybridStagedInitialRightReceiver A strategy
      hwin initialBank)
    (owner : ProfiledRawJointInitialRightOwnerControl A strategy initialBank)
    (move : In₁ × In₂) :
    Out₁ × ProfiledRawJointHybridStagedInitialRightReceiver A strategy
      hwin initialBank :=
  let key := receiver.base.1
  let row := receiver.base.2.1
  let result := stepProfiledRawJointInitialRightReceiverFor A strategy
    initialBank key
      (profiledRawJointHybridInitialRightOwnerFor A strategy hwin initialBank
        receiver owner)
      receiver.base.2.2 move
  (pairedLeftInformedForRow row result.1.physical,
    ⟨⟨key, row, result.2⟩,
      profiledRawJointHybridInitialRightPendingOfChild A strategy hwin
        initialBank key (result.1.target row)⟩)

/-! ## Generic common guarded receivers -/

local notation "CommonControl" =>
  ProfiledRawJointHybridCommonControl A strategy hwin

local notation "Installed" =>
  fun control ↦
    ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData A
      (profiledRawJointHybridCommonControlInstalled A strategy hwin control)

/-- Exact staged right root after a common guarded-left receive. -/
abbrev ProfiledRawJointHybridCommonLeftPending
    (origin : CommonControl) :=
  let installed := Installed origin
  let initial := installed.world.oneSidedState A .left
  let RootPred := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  Σ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package),
    ProfiledRawJointUnitRightPolicyMacro A strategy child.1
      (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
        RootPred package child)

/-- Exact staged left root after a common guarded-right receive. -/
abbrev ProfiledRawJointHybridCommonRightPending
    (origin : CommonControl) :=
  let installed := Installed origin
  let initial := installed.world.oneSidedState A .right
  let RootPred := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  Σ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package),
    ProfiledRawJointUnitLeftPolicyMacro A strategy child.1
      (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
        RootPred package child)

/-- Turn the exact child emitted by a common guarded-left controller into a
staged right root when its right lane is live. -/
noncomputable def profiledRawJointHybridCommonLeftPendingOfChild
    (origin : CommonControl)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy
        ((Installed origin).world.oneSidedState A .left)
        (profiledRawJointHybridExactLeftRootPredicate A (Installed origin))
        (profiledRawJointHybridExactLeftPolicy A hwin (Installed origin)))) :
    Option (ProfiledRawJointHybridCommonLeftPending A strategy hwin
      origin) := by
  classical
  let installed := Installed origin
  let initial := installed.world.oneSidedState A .left
  let RootPred := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  by_cases hlive : ∃ slot, child.1.family.right () = some slot
  · let slot := Classical.choose hlive
    let hslot := Classical.choose_spec hlive
    exact some ⟨child,
      profiledRawJointLiteralChildRightPolicyRoot A strategy
        (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
          package)
        (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
          initial RootPred package) child slot hslot⟩
  · exact none

/-- Common guarded-right/left-root mirror. -/
noncomputable def profiledRawJointHybridCommonRightPendingOfChild
    (origin : CommonControl)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy
        ((Installed origin).world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A (Installed origin))
        (profiledRawJointHybridExactRightPolicy A hwin (Installed origin)))) :
    Option (ProfiledRawJointHybridCommonRightPending A strategy hwin
      origin) := by
  classical
  let installed := Installed origin
  let initial := installed.world.oneSidedState A .right
  let RootPred := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  by_cases hlive : ∃ slot, child.1.family.left () = some slot
  · let slot := Classical.choose hlive
    let hslot := Classical.choose_spec hlive
    exact some ⟨child,
      profiledRawJointLiteralChildLeftPolicyRoot A strategy
        (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
          package)
        (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
          initial RootPred package) child slot hslot⟩
  · exact none

/-- Process one's resolved strict-left receiver with the exact latest child. -/
structure ProfiledRawJointHybridStagedLeftStrictReceiver where
  base : ProfiledRawJointHybridLeftStrictReceiver A strategy hwin
  pending : Option (ProfiledRawJointHybridCommonLeftPending A strategy hwin
    base.origin)

/-- Process-two strict-right mirror. -/
structure ProfiledRawJointHybridStagedRightStrictReceiver where
  base : ProfiledRawJointHybridRightStrictReceiver A strategy hwin
  pending : Option (ProfiledRawJointHybridCommonRightPending A strategy hwin
    base.origin)

noncomputable instance
    profiledRawJointHybridStagedLeftStrictReceiverFintype :
    Fintype (ProfiledRawJointHybridStagedLeftStrictReceiver A strategy
      hwin) := by
  classical
  let Rep := Σ base : ProfiledRawJointHybridLeftStrictReceiver A strategy hwin,
    Option (ProfiledRawJointHybridCommonLeftPending A strategy hwin
      base.origin)
  let equiv : ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin ≃
      Rep := {
    toFun := fun state ↦ ⟨state.base, state.pending⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨base, child⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridStagedRightStrictReceiverFintype :
    Fintype (ProfiledRawJointHybridStagedRightStrictReceiver A strategy
      hwin) := by
  classical
  let Rep := Σ base : ProfiledRawJointHybridRightStrictReceiver A strategy
    hwin,
    Option (ProfiledRawJointHybridCommonRightPending A strategy hwin
      base.origin)
  let equiv :
      ProfiledRawJointHybridStagedRightStrictReceiver A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.base, state.pending⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨base, child⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Resolve a process-one common shadow with a delivered left owner and store
the exact `.both` child emitted by that receive. -/
noncomputable def profiledRawJointHybridOneShadowRecvLeftOwnerStaged
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin :=
  let monitor := ProfiledRawJointHybridShadowLeftMonitor A strategy hwin
    shadow.origin
  let controller := profiledRawJointHybridShadowLeftController A strategy hwin
    shadow.origin
  let ownerControl := profiledRawJointHybridLeftGuardOwnerFor A strategy hwin
    shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (ownInput, deliveredInput)
  (pairedLeftInformedForRow .both output.physical,
    ⟨⟨shadow.origin,
      monitor.step shadow.strictReceiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonLeftPendingOfChild A strategy hwin
        shadow.origin (output.target .both)⟩)

/-- Process-two strict-right mirror staged entry. -/
noncomputable def profiledRawJointHybridTwoShadowRecvRightOwnerStaged
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridStagedRightStrictReceiver A strategy
      hwin :=
  let monitor := ProfiledRawJointHybridShadowRightMonitor A strategy hwin
    shadow.origin
  let controller := profiledRawJointHybridShadowRightController A strategy hwin
    shadow.origin
  let ownerControl := profiledRawJointHybridRightGuardOwnerFor A strategy hwin
    shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (ownInput, deliveredInput)
  (pairedRightInformedForRow .both output.physical,
    ⟨⟨shadow.origin,
      monitor.step shadow.strictReceiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonRightPendingOfChild A strategy hwin
        shadow.origin (output.target .both)⟩)

/-- Align a left guard owner with a staged receiver's dependent origin. -/
noncomputable def profiledRawJointHybridLeftGuardOwnerForStaged
    (receiver : ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin) :
    (profiledRawJointHybridShadowLeftController A strategy hwin
      receiver.base.origin).Control := by
  classical
  exact if h : owner.origin = receiver.base.origin then h ▸ owner.owner
    else (profiledRawJointHybridShadowLeftController A strategy hwin
      receiver.base.origin).initial

/-- Right guard-owner mirror alignment. -/
noncomputable def profiledRawJointHybridRightGuardOwnerForStaged
    (receiver : ProfiledRawJointHybridStagedRightStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin) :
    (profiledRawJointHybridShadowRightController A strategy hwin
      receiver.base.origin).Control := by
  classical
  exact if h : owner.origin = receiver.base.origin then h ▸ owner.owner
    else (profiledRawJointHybridShadowRightController A strategy hwin
      receiver.base.origin).initial

/-- Continue a resolved common strict-left receiver and refresh the exact
pending child. -/
noncomputable def
    continueProfiledRawJointHybridStagedLeftStrictReceiver
    (receiver : ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridStagedLeftStrictReceiver A strategy hwin :=
  let origin := receiver.base.origin
  let monitor := ProfiledRawJointHybridShadowLeftMonitor A strategy hwin origin
  let controller := profiledRawJointHybridShadowLeftController A strategy hwin
    origin
  let ownerControl := profiledRawJointHybridLeftGuardOwnerForStaged A strategy
    hwin receiver owner
  let label := controller.labelOf ownerControl
  let output := label.2 receiver.base.receiver (ownInput, deliveredInput)
  (pairedLeftInformedForRow .both output.physical,
    ⟨⟨origin,
      monitor.step receiver.base.receiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonLeftPendingOfChild A strategy hwin origin
        (output.target .both)⟩)

/-- Resolved strict-right mirror continuation. -/
noncomputable def
    continueProfiledRawJointHybridStagedRightStrictReceiver
    (receiver : ProfiledRawJointHybridStagedRightStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridStagedRightStrictReceiver A strategy
      hwin :=
  let origin := receiver.base.origin
  let monitor := ProfiledRawJointHybridShadowRightMonitor A strategy hwin origin
  let controller := profiledRawJointHybridShadowRightController A strategy hwin
    origin
  let ownerControl := profiledRawJointHybridRightGuardOwnerForStaged A strategy
    hwin receiver owner
  let label := controller.labelOf ownerControl
  let output := label.2 receiver.base.receiver (ownInput, deliveredInput)
  (pairedRightInformedForRow .both output.physical,
    ⟨⟨origin,
      monitor.step receiver.base.receiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩,
      profiledRawJointHybridCommonRightPendingOfChild A strategy hwin origin
        (output.target .both)⟩)

end

end DetParityAutomaton

end DistributedSynthesis
