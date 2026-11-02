/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedMacroControl
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentControllerBank

/-!
# Embedding persistent strict macros into the guarded child family

The recurrent controller bank is indexed by one fixed first-input pair and
stores a complete false/one-sided guarded key in every live macro.  The
leader-free carrier instead indexes its ordinary controls by the full guarded
child code.  These are the lossless conversions between the two views.

Only the false/one-sided summand is used here.  A false/common child remains
an exceptional state and has no ordinary strict macro through this bridge.
The outer first-input index is preserved definitionally.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (first : In₁ × In₂)

/-! ## The complete child carried by a persistent macro -/

/-- A persistent right-live macro carries this exact false/one-sided child. -/
def ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.child
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    ProfiledRawJointHybridRootPinnedChildCode A strategy hwin :=
  profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
    source.key

/-- Left-live mirror. -/
def ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.child
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    ProfiledRawJointHybridRootPinnedChildCode A strategy hwin :=
  profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
    source.key

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.child_first
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    (source.child A strategy hwin first).1 = first :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.child_first
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    (source.child A strategy hwin first).1 = first :=
  rfl

/-! ## Persistent macro to child-indexed macro -/

/-- Forget only the redundant stored key: the target child index retains it
exactly. -/
def ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.toChildMacro
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (source.child A strategy hwin first) :=
  { slot := source.slot
    active_slot := source.active_slot }

/-- Left-live mirror. -/
def ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.toChildMacro
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (source.child A strategy hwin first) :=
  { slot := source.slot
    active_slot := source.active_slot }

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.toChildMacro_slot
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    (source.toChildMacro A strategy hwin first).slot = source.slot :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.toChildMacro_slot
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    (source.toChildMacro A strategy hwin first).slot = source.slot :=
  rfl

/-! ## Child-indexed macro to persistent macro -/

/-- Reinsert the exact key already present in a false/one-sided child index. -/
def profiledRawJointHybridRootPinnedRightMacroToPersistent
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
      hwin first :=
  { key := key
    slot := source.slot
    active_slot := source.active_slot }

/-- Left-live mirror. -/
def profiledRawJointHybridRootPinnedLeftMacroToPersistent
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
      hwin first :=
  { key := key
    slot := source.slot
    active_slot := source.active_slot }

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridRootPinnedRightMacroToPersistent_key
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    (profiledRawJointHybridRootPinnedRightMacroToPersistent A strategy hwin
      first key source).key = key :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedLeftMacroToPersistent_key
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    (profiledRawJointHybridRootPinnedLeftMacroToPersistent A strategy hwin
      first key source).key = key :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedRightMacroToPersistent_slot
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    (profiledRawJointHybridRootPinnedRightMacroToPersistent A strategy hwin
      first key source).slot = source.slot :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedLeftMacroToPersistent_slot
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (source : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
        key)) :
    (profiledRawJointHybridRootPinnedLeftMacroToPersistent A strategy hwin
      first key source).slot = source.slot :=
  rfl

end

/-! ## Sigma packages consumed by the dependent carrier -/

/-- Lossless package of the complete next child and its right-live macro. -/
def ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.childPackage
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    Σ child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin child :=
  ⟨source.child A strategy hwin first,
    source.toChildMacro A strategy hwin first⟩

/-- Left-live mirror package. -/
def ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.childPackage
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    Σ child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin child :=
  ⟨source.child A strategy hwin first,
    source.toChildMacro A strategy hwin first⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.childPackage_first
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    (source.childPackage A strategy hwin first).1.1 = first :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.childPackage_first
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    (source.childPackage A strategy hwin first).1.1 = first :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
