/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentLocalHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedStrictMacroEmbedding

/-!
# Exact strict control families below the guarded root

The generic leader-free carrier indexes every recurrent local control by a
complete guarded child.  Ordinary block controllers, however, exist only at
false/one-sided children.  This module expresses that boundary in the type:

* a false/common child has no ordinary strict control;
* a false/one-sided child carries a fixed-first local controller state whose
  stored persistent source key is literally that child key.

Thus common/repeated-both handling cannot accidentally enter an ordinary
strict transition.  It remains confined to the exceptional adapter.  The
outer first-input pair selects the controller bank once and is never an
orientation or leader signal.
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

/-! ## The four exact dependent families -/

/-- Process-one owner controls exist exactly at false/one-sided children. -/
def ProfiledRawJointHybridRootPinnedStrictRightOwner
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) : Type _ :=
  match child with
  | ⟨_, .inl _⟩ => PEmpty
  | ⟨first, .inr key⟩ =>
      { control :
          ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
            strategy hwin first
            (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
              strategy hwin first) //
        control.1.key = key }

/-- Process-one receiver controls exist exactly at false/one-sided children. -/
def ProfiledRawJointHybridRootPinnedStrictLeftReceiver
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) : Type _ :=
  match child with
  | ⟨_, .inl _⟩ => PEmpty
  | ⟨first, .inr key⟩ =>
      { control :
          ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl
            A strategy hwin first //
        control.1.key = key }

/-- Process-two receiver controls exist exactly at false/one-sided children. -/
def ProfiledRawJointHybridRootPinnedStrictRightReceiver
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) : Type _ :=
  match child with
  | ⟨_, .inl _⟩ => PEmpty
  | ⟨first, .inr key⟩ =>
      { control :
          ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl
            A strategy hwin first //
        control.1.key = key }

/-- Process-two owner controls exist exactly at false/one-sided children. -/
def ProfiledRawJointHybridRootPinnedStrictLeftOwner
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) : Type _ :=
  match child with
  | ⟨_, .inl _⟩ => PEmpty
  | ⟨first, .inr key⟩ =>
      { control :
          ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
            strategy hwin first
            (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
              strategy hwin first) //
        control.1.key = key }

noncomputable instance profiledRawJointHybridRootPinnedStrictRightOwnerFintype
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
        child) := by
  classical
  rcases child with ⟨first, common | oneSided⟩
  · change Fintype PEmpty
    infer_instance
  · dsimp only [ProfiledRawJointHybridRootPinnedStrictRightOwner]
    infer_instance

noncomputable instance
    profiledRawJointHybridRootPinnedStrictLeftReceiverFintype
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
        child) := by
  classical
  rcases child with ⟨first, common | oneSided⟩
  · change Fintype PEmpty
    infer_instance
  · dsimp only [ProfiledRawJointHybridRootPinnedStrictLeftReceiver]
    infer_instance

noncomputable instance
    profiledRawJointHybridRootPinnedStrictRightReceiverFintype
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin
        child) := by
  classical
  rcases child with ⟨first, common | oneSided⟩
  · change Fintype PEmpty
    infer_instance
  · dsimp only [ProfiledRawJointHybridRootPinnedStrictRightReceiver]
    infer_instance

noncomputable instance profiledRawJointHybridRootPinnedStrictLeftOwnerFintype
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
        child) := by
  classical
  rcases child with ⟨first, common | oneSided⟩
  · change Fintype PEmpty
    infer_instance
  · dsimp only [ProfiledRawJointHybridRootPinnedStrictLeftOwner]
    infer_instance

/-! ## Exact initialization from child-indexed live macros -/

/-- Install a child-indexed right macro as an exact process-one owner. -/
noncomputable def profiledRawJointHybridRootPinnedStrictInitialRightOwner
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key) :=
  let persistent :=
    profiledRawJointHybridRootPinnedRightMacroToPersistent A strategy hwin
      first key source
  ⟨initialProfiledRawJointHybridInitialRootPinnedPersistentRightOwner A
      strategy hwin first
      (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first) persistent,
    rfl⟩

/-- Install a child-indexed left macro as an exact process-two owner. -/
noncomputable def profiledRawJointHybridRootPinnedStrictInitialLeftOwner
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key) :=
  let persistent :=
    profiledRawJointHybridRootPinnedLeftMacroToPersistent A strategy hwin first
      key source
  ⟨initialProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner A
      strategy hwin first
      (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first) persistent,
    rfl⟩

/-- Install a child-indexed right macro as an exact process-two receiver. -/
noncomputable def profiledRawJointHybridRootPinnedStrictInitialRightReceiver
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key))
    (row : PairedEntryRow) :
    ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key) :=
  let persistent :=
    profiledRawJointHybridRootPinnedRightMacroToPersistent A strategy hwin
      first key source
  ⟨initialProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver A
      strategy hwin first persistent row,
    rfl⟩

/-- Install a child-indexed left macro as an exact process-one receiver. -/
noncomputable def profiledRawJointHybridRootPinnedStrictInitialLeftReceiver
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key))
    (row : PairedEntryRow) :
    ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key) :=
  let persistent :=
    profiledRawJointHybridRootPinnedLeftMacroToPersistent A strategy hwin first
      key source
  ⟨initialProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver A
      strategy hwin first persistent row,
    rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
