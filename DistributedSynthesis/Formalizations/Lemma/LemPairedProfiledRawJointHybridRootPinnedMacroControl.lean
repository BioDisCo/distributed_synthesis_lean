/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialCommonSiblingBridge
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointLeaderFreeControllerCarrier

/-!
# Finite macro controls below the exact guarded root

For each finite first-input pair, the exact root-pinned policy has one finite
family of reachable post-root states.  A child code is either a false/common
key or a false/one-sided key of that same policy.  Live macro controls add only
the active finite slot.

The outer first-input index chooses the policy once.  The common/one-sided tag
is an internal policy-state tag.  Neither is a graph orientation or a leader
observation, and no transition in this file selects a fresh policy.
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

/-! ## One finite child family of guarded false states -/

/-- Every post-root child used by the initial common/strict adapter.  For a
fixed outer `first`, both summands belong to the one selected guarded policy
at `first`. -/
abbrev ProfiledRawJointHybridRootPinnedChildCode :=
  Σ first : In₁ × In₂,
    ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy hwin
        first ⊕
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
        first

noncomputable instance profiledRawJointHybridRootPinnedChildCodeFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) := by
  classical
  infer_instance

/-- Embed a reachable false/common state without changing its guarded policy
index. -/
def profiledRawJointHybridRootPinnedChildOfCommon
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first) :
    ProfiledRawJointHybridRootPinnedChildCode A strategy hwin :=
  ⟨first, .inl key⟩

/-- Embed a reachable false/one-sided state. -/
def profiledRawJointHybridRootPinnedChildOfOneSided
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first) :
    ProfiledRawJointHybridRootPinnedChildCode A strategy hwin :=
  ⟨first, .inr key⟩

/-- Incidence payload advertised by a guarded child. -/
def profiledRawJointHybridRootPinnedChildIncidenceCode
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  match child.2 with
  | .inl key => key.incidenceCode
  | .inr key => key.incidenceCode

/-- Its exact guarded-policy state. -/
def profiledRawJointHybridRootPinnedChildState
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy child.1 :=
  match child.2 with
  | .inl key => key.state
  | .inr key => key.state

section
omit [DecidableEq In₁] [DecidableEq In₂]

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Every packaged state is reachable in the policy selected by its outer
index. -/
theorem profiledRawJointHybridRootPinnedChildState_reachable
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin child.1
      (profiledRawJointHybridRootPinnedChildState A strategy hwin child) := by
  rcases child with ⟨first, common | oneSided⟩
  · exact common.reachable
  · exact oneSided.reachable

/-- The one-shot guard has been consumed at every packaged child. -/
theorem profiledRawJointHybridRootPinnedChildState_fresh_false
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    (profiledRawJointHybridRootPinnedChildState A strategy hwin child).1 =
      false := by
  rcases child with ⟨first, common | oneSided⟩
  · exact common.fresh_false
  · exact oneSided.fresh_false

@[simp] theorem profiledRawJointHybridRootPinnedChildIncidenceCode_common
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first) :
    profiledRawJointHybridRootPinnedChildIncidenceCode A strategy hwin
        (profiledRawJointHybridRootPinnedChildOfCommon A strategy hwin first
          key) =
      key.incidenceCode :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedChildIncidenceCode_oneSided
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first) :
    profiledRawJointHybridRootPinnedChildIncidenceCode A strategy hwin
        (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
          key) =
      key.incidenceCode :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedChildState_common
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first) :
    profiledRawJointHybridRootPinnedChildState A strategy hwin
        (profiledRawJointHybridRootPinnedChildOfCommon A strategy hwin first
          key) =
      key.state :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedChildState_oneSided
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first) :
    profiledRawJointHybridRootPinnedChildState A strategy hwin
        (profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin first
          key) =
      key.state :=
  rfl

end

end

/-! ## Finite live macros -/

/-- A right-live macro is an exact guarded child together with its active
right slot.  Reachability and the false bit are already stored in `child`. -/
structure ProfiledRawJointHybridRootPinnedRightMacro
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) where
  slot : ProfiledRawRightSlot A
  active_slot :
    (profiledRawJointHybridRootPinnedChildIncidenceCode A strategy hwin child
      ).family.right () = some slot

/-- Left-live mirror. -/
structure ProfiledRawJointHybridRootPinnedLeftMacro
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) where
  slot : ProfiledRawLeftSlot A
  active_slot :
    (profiledRawJointHybridRootPinnedChildIncidenceCode A strategy hwin child
      ).family.left () = some slot

noncomputable instance profiledRawJointHybridRootPinnedRightMacroFintype
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin child) := by
  classical
  exact Fintype.ofInjective
    (fun entry : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      child ↦ entry.slot) (by
        intro left right heq
        cases left
        cases right
        cases heq
        rfl)

noncomputable instance profiledRawJointHybridRootPinnedLeftMacroFintype
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin child) := by
  classical
  exact Fintype.ofInjective
    (fun entry : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      child ↦ entry.slot) (by
        intro left right heq
        cases left
        cases right
        cases heq
        rfl)

/-! ## Generic-carrier control shapes -/

/-- The root controls contain no information. -/
abbrev ProfiledRawJointHybridRootPinnedInitialOne := Unit
abbrev ProfiledRawJointHybridRootPinnedInitialTwo := Unit

/-- The exact reachable initial ambiguity is determined by the two finite
input pairs.  Each process reconstructs its own canonical shadow locally. -/
abbrev ProfiledRawJointHybridRootPinnedExceptionalOne :=
  ProfiledRawJointInitialCommonBothKey (In₁ := In₁) (In₂ := In₂)

abbrev ProfiledRawJointHybridRootPinnedExceptionalTwo :=
  ProfiledRawJointInitialCommonBothKey (In₁ := In₁) (In₂ := In₂)

/-- Control shape expected by the generic leader-free carrier.  Both roles of
a right-oriented block use the same right-live macro family. -/
abbrev ProfiledRawJointHybridRootPinnedOneControl :=
  ProfiledRawJointLeaderFreeOneControl
    ProfiledRawJointHybridRootPinnedInitialOne
    (ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂))
    (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin)
    (ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin)

/-- Process-two mirror. -/
abbrev ProfiledRawJointHybridRootPinnedTwoControl :=
  ProfiledRawJointLeaderFreeTwoControl
    ProfiledRawJointHybridRootPinnedInitialTwo
    (ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂))
    (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin)
    (ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin)

noncomputable instance profiledRawJointHybridRootPinnedOneControlFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedOneControl A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridRootPinnedTwoControlFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedTwoControl A strategy hwin) := by
  classical
  infer_instance

def profiledRawJointHybridRootPinnedInitialOneControl :
    ProfiledRawJointHybridRootPinnedOneControl A strategy hwin :=
  .initial ()

def profiledRawJointHybridRootPinnedInitialTwoControl :
    ProfiledRawJointHybridRootPinnedTwoControl A strategy hwin :=
  .initial ()

/-- Install the exact finite second-round ambiguity as an exceptional local
state.  This constructor takes only the locally reconstructed finite key. -/
def profiledRawJointHybridRootPinnedExceptionalOneControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedOneControl A strategy hwin :=
  .exceptional key

/-- Process-two mirror. -/
def profiledRawJointHybridRootPinnedExceptionalTwoControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedTwoControl A strategy hwin :=
  .exceptional key

/-! ## Exact shadows reconstructed by exceptional local states -/

noncomputable def profiledRawJointHybridRootPinnedExceptionalOneShadow
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin :=
  (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin controllers
    (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
      key.1).2 key.2.1 key.2.2).2

noncomputable def profiledRawJointHybridRootPinnedExceptionalTwoShadow
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin :=
  (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin controllers
    (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
      key.1).2 key.2.2 key.2.1).2

@[simp] theorem profiledRawJointHybridRootPinnedExceptionalOneShadow_key
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalOneShadow A strategy hwin
      controllers key).key = key :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedExceptionalTwoShadow_key
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalTwoShadow A strategy hwin
      controllers key).key = key :=
  rfl

/-! ## The three exact guarded children named by one exceptional key -/

/-- The hypothetical simultaneous child retained by both local exceptional
states. -/
noncomputable def profiledRawJointHybridRootPinnedExceptionalCommonChild
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedChildCode A strategy hwin :=
  profiledRawJointHybridRootPinnedChildOfCommon A strategy hwin key.1
    (profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
      key.1 key.2)

/-- The strict-left sibling seen by process one's ambiguous receive. -/
noncomputable def profiledRawJointHybridRootPinnedExceptionalStrictLeftChild
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedChildCode A strategy hwin :=
  profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin key.1
    (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin key.1
      (profiledRawJointHybridInitialSecondStrictLeftDirection key.1 key.2))

/-- Strict-right sibling mirror. -/
noncomputable def profiledRawJointHybridRootPinnedExceptionalStrictRightChild
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedChildCode A strategy hwin :=
  profiledRawJointHybridRootPinnedChildOfOneSided A strategy hwin key.1
    (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin key.1
      (profiledRawJointHybridInitialSecondStrictRightDirection key.1 key.2))

section
omit [DecidableEq In₁] [DecidableEq In₂]

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem
    profiledRawJointHybridRootPinnedExceptionalCommonChild_first
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalCommonChild A strategy hwin
      key).1 = key.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedExceptionalStrictLeftChild_first
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalStrictLeftChild A strategy hwin
      key).1 = key.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedExceptionalStrictRightChild_first
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalStrictRightChild A strategy
      hwin key).1 = key.1 :=
  rfl

end

end

/-! ## Exact live macro constructors from exceptional local states -/

/-- Process one's local exceptional state stages the simultaneous sibling at
its exact retained right slot. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalOneCommonRightMacro
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (profiledRawJointHybridRootPinnedExceptionalCommonChild A strategy hwin
        key) := by
  let shadow := profiledRawJointHybridRootPinnedExceptionalOneShadow A strategy
    hwin controllers key
  refine ⟨shadow.strictStage.slot, ?_⟩
  have hslot := shadow.strictStage.active_slot
  have hlive :=
    profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_simultaneousSibling
      A strategy hwin controllers key.1 key.2
  change
    (profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
      key.1 key.2).incidenceCode.family.right () =
        some shadow.strictStage.slot
  rw [← hlive]
  exact hslot

/-- The indistinguishable strict-left alternative stages the same local slot
inside the strict sibling key, without changing policy. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalOneStrictRightMacro
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin
      (profiledRawJointHybridRootPinnedExceptionalStrictLeftChild A strategy
        hwin key) := by
  let shadow := profiledRawJointHybridRootPinnedExceptionalOneShadow A strategy
    hwin controllers key
  refine ⟨shadow.strictStage.slot, ?_⟩
  have hslot := shadow.strictStage.active_slot
  have hlive :=
    profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_strictSibling A
      strategy hwin controllers key.1 key.2
  change
    (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin key.1
      (profiledRawJointHybridInitialSecondStrictLeftDirection key.1 key.2)
      ).incidenceCode.family.right () = some shadow.strictStage.slot
  rw [← hlive]
  exact hslot

/-- Process-two stages the simultaneous sibling at the exact retained left
slot. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalTwoCommonLeftMacro
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (profiledRawJointHybridRootPinnedExceptionalCommonChild A strategy hwin
        key) := by
  let shadow := profiledRawJointHybridRootPinnedExceptionalTwoShadow A strategy
    hwin controllers key
  refine ⟨shadow.strictStage.slot, ?_⟩
  have hslot := shadow.strictStage.active_slot
  have hlive :=
    profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_simultaneousSibling
      A strategy hwin controllers key.1 key.2
  change
    (profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
      key.1 key.2).incidenceCode.family.left () =
        some shadow.strictStage.slot
  rw [← hlive]
  exact hslot

/-- Strict-right mirror. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalTwoStrictLeftMacro
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin
      (profiledRawJointHybridRootPinnedExceptionalStrictRightChild A strategy
        hwin key) := by
  let shadow := profiledRawJointHybridRootPinnedExceptionalTwoShadow A strategy
    hwin controllers key
  refine ⟨shadow.strictStage.slot, ?_⟩
  have hslot := shadow.strictStage.active_slot
  have hlive :=
    profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_strictSibling A
      strategy hwin controllers key.1 key.2
  change
    (profiledRawJointHybridInitialRootPinnedStrictKey A strategy hwin key.1
      (profiledRawJointHybridInitialSecondStrictRightDirection key.1 key.2)
      ).incidenceCode.family.left () = some shadow.strictStage.slot
  rw [← hlive]
  exact hslot

/-! ## Local indistinguishability is literal slot equality -/

@[simp] theorem
    profiledRawJointHybridRootPinnedExceptionalOne_siblingMacro_slot
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalOneCommonRightMacro A strategy
      hwin controllers key).slot =
      (profiledRawJointHybridRootPinnedExceptionalOneStrictRightMacro A
        strategy hwin controllers key).slot :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedExceptionalTwo_siblingMacro_slot
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalTwoCommonLeftMacro A strategy
      hwin controllers key).slot =
      (profiledRawJointHybridRootPinnedExceptionalTwoStrictLeftMacro A strategy
        hwin controllers key).slot :=
  rfl

/-- Sigma packages are the exact shape consumed by a finite-front adapter.
They are proof-side alternatives from one local state, not a runtime branch on
the hidden graph. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalOneCommonPackage
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    Σ child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin child :=
  ⟨profiledRawJointHybridRootPinnedExceptionalCommonChild A strategy hwin
      key,
    profiledRawJointHybridRootPinnedExceptionalOneCommonRightMacro A strategy
      hwin controllers key⟩

noncomputable def
    profiledRawJointHybridRootPinnedExceptionalOneStrictPackage
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    Σ child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin child :=
  ⟨profiledRawJointHybridRootPinnedExceptionalStrictLeftChild A strategy
      hwin key,
    profiledRawJointHybridRootPinnedExceptionalOneStrictRightMacro A strategy
      hwin controllers key⟩

noncomputable def
    profiledRawJointHybridRootPinnedExceptionalTwoCommonPackage
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    Σ child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin child :=
  ⟨profiledRawJointHybridRootPinnedExceptionalCommonChild A strategy hwin
      key,
    profiledRawJointHybridRootPinnedExceptionalTwoCommonLeftMacro A strategy
      hwin controllers key⟩

noncomputable def
    profiledRawJointHybridRootPinnedExceptionalTwoStrictPackage
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    Σ child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin,
      ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin child :=
  ⟨profiledRawJointHybridRootPinnedExceptionalStrictRightChild A strategy
      hwin key,
    profiledRawJointHybridRootPinnedExceptionalTwoStrictLeftMacro A strategy
      hwin controllers key⟩

/-! ## Injection into the generic leader-free control sum -/

/-- A right-live macro has exactly the process-one owner shape expected by
the generic carrier. -/
def profiledRawJointHybridRootPinnedOneRightOwnerControl
    {child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin}
    (entry : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin child) :
    ProfiledRawJointHybridRootPinnedOneControl A strategy hwin :=
  .rightOwner child entry

/-- A left-live macro has the process-one receiver shape. -/
def profiledRawJointHybridRootPinnedOneLeftReceiverControl
    {child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin}
    (entry : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin child) :
    ProfiledRawJointHybridRootPinnedOneControl A strategy hwin :=
  .leftReceiver child entry

/-- Process-two/right receiver injection. -/
def profiledRawJointHybridRootPinnedTwoRightReceiverControl
    {child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin}
    (entry : ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin child) :
    ProfiledRawJointHybridRootPinnedTwoControl A strategy hwin :=
  .rightReceiver child entry

/-- Process-two/left owner injection. -/
def profiledRawJointHybridRootPinnedTwoLeftOwnerControl
    {child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin}
    (entry : ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin child) :
    ProfiledRawJointHybridRootPinnedTwoControl A strategy hwin :=
  .leftOwner child entry

/-- Proof-side simultaneous successor control for process one.  An executable
transition may use this only in the matching local branch; no graph argument
is present here. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalOneCommonRecurrentControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedOneControl A strategy hwin :=
  let package :=
    profiledRawJointHybridRootPinnedExceptionalOneCommonPackage A strategy hwin
      controllers key
  .rightOwner package.1 package.2

/-- Strict-left alternative at exactly the same local slot. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalOneStrictRecurrentControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedOneControl A strategy hwin :=
  let package :=
    profiledRawJointHybridRootPinnedExceptionalOneStrictPackage A strategy hwin
      controllers key
  .rightOwner package.1 package.2

/-- Process-two simultaneous successor witness. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalTwoCommonRecurrentControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedTwoControl A strategy hwin :=
  let package :=
    profiledRawJointHybridRootPinnedExceptionalTwoCommonPackage A strategy hwin
      controllers key
  .leftOwner package.1 package.2

/-- Process-two strict-right alternative. -/
noncomputable def
    profiledRawJointHybridRootPinnedExceptionalTwoStrictRecurrentControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedTwoControl A strategy hwin :=
  let package :=
    profiledRawJointHybridRootPinnedExceptionalTwoStrictPackage A strategy hwin
      controllers key
  .leftOwner package.1 package.2

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Both proof-side alternatives remain under the one policy index selected
by the first input pair. -/
theorem profiledRawJointHybridRootPinnedExceptional_children_samePolicyIndex
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedExceptionalCommonChild A strategy hwin
        key).1 = key.1 ∧
      (profiledRawJointHybridRootPinnedExceptionalStrictLeftChild A strategy
        hwin key).1 = key.1 ∧
      (profiledRawJointHybridRootPinnedExceptionalStrictRightChild A strategy
        hwin key).1 = key.1 := by
  exact ⟨rfl, rfl, rfl⟩

end


end DetParityAutomaton

end DistributedSynthesis
