/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaChildFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTargetFamily

/-!
# One recurrent family for the old finite front and the guarded common front

The established hybrid mega family contains the five recurrent entry classes
used by the old initial and strict front.  The guarded common construction has
its own finite target family, indexed by the represented guarded pair at the
strict close.  This file takes their disjoint union and exposes the uniform
source, policy, controller bank, and indexed leader-free kernel interface.

The sum tag is finite controller provenance.  It is never computed from a
graph, orientation, hierarchy side, leader bit, semantic world, or history.
No front transition is defined here.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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

/-! ## Combined finite child alphabet -/

/-- The old five-way recurrent family together with every guarded-common
target key. -/
abbrev ProfiledRawJointGuardedHybridCombinedChildCode :=
  ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank ⊕
    ProfiledRawJointGuardedCommonTargetKey A strategy hwin

noncomputable instance profiledRawJointGuardedHybridCombinedChildCodeFintype :
    Fintype
      (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
        initialBank) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointGuardedHybridCombinedChildCodeDecidableEq :
    DecidableEq
      (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
        initialBank) :=
  Classical.decEq _

/-- Embed one of the old five recurrent entry classes. -/
def profiledRawJointGuardedHybridCombinedChildOfMega
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank :=
  .inl child

/-- Embed a target produced by the guarded common strict-close construction. -/
def profiledRawJointGuardedHybridCombinedChildOfGuarded
    (child : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :
    ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank :=
  .inr child

/-! ## Uniform source, policy, and controller bank -/

/-- Recover the exact one-sided semantic source represented by either side of
the combined family. -/
noncomputable def profiledRawJointGuardedHybridCombinedChildSource
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) := by
  cases child with
  | inl mega =>
      exact profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        mega
  | inr guarded =>
      exact profiledRawJointGuardedCommonTargetSource A strategy hwin guarded

@[simp] theorem profiledRawJointGuardedHybridCombinedChildSource_mega
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
        initialBank
        (profiledRawJointGuardedHybridCombinedChildOfMega A strategy hwin
          initialBank child) =
      profiledRawJointHybridMegaChildSource A strategy hwin initialBank child :=
  rfl

@[simp] theorem profiledRawJointGuardedHybridCombinedChildSource_guarded
    (child : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :
    profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
        initialBank
        (profiledRawJointGuardedHybridCombinedChildOfGuarded A strategy hwin
          initialBank child) =
      profiledRawJointGuardedCommonTargetSource A strategy hwin child :=
  rfl

/-- Use the rational policy already fixed by the selected component. -/
noncomputable def profiledRawJointGuardedHybridCombinedChildPolicy
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
        initialBank child).code A) := by
  cases child with
  | inl mega =>
      exact profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        mega
  | inr guarded =>
      exact profiledRawJointGuardedCommonTargetPolicy A strategy hwin guarded

@[simp] theorem profiledRawJointGuardedHybridCombinedChildPolicy_mega
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
        initialBank
        (profiledRawJointGuardedHybridCombinedChildOfMega A strategy hwin
          initialBank child) =
      profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child :=
  rfl

@[simp] theorem profiledRawJointGuardedHybridCombinedChildPolicy_guarded
    (child : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :
    profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
        initialBank
        (profiledRawJointGuardedHybridCombinedChildOfGuarded A strategy hwin
          initialBank child) =
      profiledRawJointGuardedCommonTargetPolicy A strategy hwin child :=
  rfl

/-- Reuse the component's already verified recurrent controller bank. -/
noncomputable def profiledRawJointGuardedHybridCombinedControllerBank
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
        initialBank child)
      (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
        initialBank child) := by
  cases child with
  | inl mega =>
      exact profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank mega
  | inr guarded =>
      exact profiledRawJointGuardedCommonTargetControllerBank A strategy hwin
        guarded

@[simp] theorem profiledRawJointGuardedHybridCombinedControllerBank_mega
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
        initialBank
        (profiledRawJointGuardedHybridCombinedChildOfMega A strategy hwin
          initialBank child) =
      profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        child :=
  rfl

@[simp] theorem profiledRawJointGuardedHybridCombinedControllerBank_guarded
    (child : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :
    profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
        initialBank
        (profiledRawJointGuardedHybridCombinedChildOfGuarded A strategy hwin
          initialBank child) =
      profiledRawJointGuardedCommonTargetControllerBank A strategy hwin
        child :=
  rfl

/-! ## Four indexed recurrent local families -/

abbrev ProfiledRawJointGuardedHybridCombinedRightOwner
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :=
  ProfiledRawJointIndexedPolicyRightOwner A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank) child

abbrev ProfiledRawJointGuardedHybridCombinedLeftReceiver
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :=
  ProfiledRawJointIndexedPolicyLeftReceiver A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank) child

abbrev ProfiledRawJointGuardedHybridCombinedRightReceiver
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :=
  ProfiledRawJointIndexedPolicyRightReceiver A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank) child

abbrev ProfiledRawJointGuardedHybridCombinedLeftOwner
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :=
  ProfiledRawJointIndexedPolicyLeftOwner A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank) child

noncomputable instance profiledRawJointGuardedHybridCombinedRightOwnerFintype
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :
    Fintype (ProfiledRawJointGuardedHybridCombinedRightOwner A strategy hwin
      initialBank child) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointGuardedHybridCombinedLeftReceiverFintype
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :
    Fintype (ProfiledRawJointGuardedHybridCombinedLeftReceiver A strategy hwin
      initialBank child) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointGuardedHybridCombinedRightReceiverFintype
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :
    Fintype (ProfiledRawJointGuardedHybridCombinedRightReceiver A strategy hwin
      initialBank child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedHybridCombinedLeftOwnerFintype
    (child : ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
      initialBank) :
    Fintype (ProfiledRawJointGuardedHybridCombinedLeftOwner A strategy hwin
      initialBank child) := by
  classical
  infer_instance

/-! ## Specialized finite-front and kernel aliases -/

abbrev ProfiledRawJointGuardedHybridCombinedOneControl
    (InitialOne : Type i₁) (ExceptionalOne : Type e₁) :=
  ProfiledRawJointIndexedPolicyOneControl A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank) InitialOne ExceptionalOne

abbrev ProfiledRawJointGuardedHybridCombinedTwoControl
    (InitialTwo : Type i₂) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyTwoControl A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank) InitialTwo ExceptionalTwo

/-- The six genuinely local front maps required above the combined recurrent
family. -/
abbrev ProfiledRawJointGuardedHybridCombinedExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank) InitialOne InitialTwo ExceptionalOne ExceptionalTwo

/-- Complete indexed leader-free kernel once the finite front is supplied. -/
noncomputable def profiledRawJointGuardedHybridCombinedLeaderFreeKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointGuardedHybridCombinedExceptionalAdapter A
      strategy hwin initialBank InitialOne InitialTwo ExceptionalOne
      ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne
      InitialTwo ExceptionalOne ExceptionalTwo
      (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin
        initialBank)
      (ProfiledRawJointGuardedHybridCombinedRightOwner A strategy hwin
        initialBank)
      (ProfiledRawJointGuardedHybridCombinedLeftReceiver A strategy hwin
        initialBank)
      (ProfiledRawJointGuardedHybridCombinedRightReceiver A strategy hwin
        initialBank)
      (ProfiledRawJointGuardedHybridCombinedLeftOwner A strategy hwin
        initialBank) := by
  classical
  exact profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
    (ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank)
    (profiledRawJointGuardedHybridCombinedChildSource A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin
      initialBank)
    (profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
      initialBank) adapter

end

end DetParityAutomaton

end DistributedSynthesis
