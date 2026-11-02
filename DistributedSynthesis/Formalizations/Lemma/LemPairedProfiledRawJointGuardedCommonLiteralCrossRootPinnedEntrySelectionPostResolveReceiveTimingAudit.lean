/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveReceiverFork

/-!
# Timing audit for the post-resolve recurrent handoff

The same-target `first`/`both` receiver fork is a valid local object, but it
is not yet the fork created at an actual reversal.  At that boundary the
ordinary branch has already advanced the receiver belonging to the target
staged on the preceding block round.  The simultaneous branch starts at the
fresh target emitted by the current closing record.

This file records that two-target shape explicitly.  It also exposes the
important totalization branch: a fresh closed receiver has no staged opposite
target, so its first blind non-receive uses the fixed-policy fallback.  Thus
the same-target root law cannot discharge the actual receive law unless an
additional transition-link theorem identifies the old advanced continuation
with the newly chosen package.  No such theorem is assumed here.
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

/-! ## The actual old-target open continuations -/

/-- Advance the left receiver and left owner stored at the target staged on
the preceding right-block round.  This is the ordinary strict-left
postcontrol; it is not an unconsumed receiver root. -/
noncomputable def profiledRawJointPostResolveRightFreshAdvanceLeftReceiver
    (root : ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A strategy ×
      Out₁ :=
  let key : ProfiledRawJointPostResolveFreshTargetKey A strategy :=
    .inl root.1
  let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    (profiledRawJointPostResolveFreshTargetSource A strategy key)
    (profiledRawJointPostResolveFreshTargetPolicy A strategy key)
    (profiledRawJointPostResolveFreshTargetControllerBank A strategy key)
    root.2.2 root.2.1 input
  (⟨key, next.2⟩, next.1)

/-- Mirrored ordinary strict-right postcontrol. -/
noncomputable def profiledRawJointPostResolveLeftFreshAdvanceRightReceiver
    (root : ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    ProfiledRawJointPostResolveFreshTargetRightReceiverControl A strategy ×
      Out₂ :=
  let key : ProfiledRawJointPostResolveFreshTargetKey A strategy :=
    .inr root.1
  let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
    (profiledRawJointPostResolveFreshTargetSource A strategy key)
    (profiledRawJointPostResolveFreshTargetPolicy A strategy key)
    (profiledRawJointPostResolveFreshTargetControllerBank A strategy key)
    root.2.2 root.2.1 input
  (⟨key, next.2⟩, next.1)

/-! ## Two-target boundary forks -/

/-- The receiver fork at a right-to-left reversal.  Its open branch advances
the previously staged target.  Its closed branch is the unconsumed `both`
receiver at the freshly emitted target. -/
noncomputable def profiledRawJointPostResolveRightFreshReceiverBoundaryFork
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    FiniteDelayedFork
      (ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A strategy) :=
  ⟨(profiledRawJointPostResolveRightFreshAdvanceLeftReceiver A strategy
      oldRoot input).1,
    (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy
      newRoot.1).closedControl⟩

/-- Mirrored left-to-right boundary fork. -/
noncomputable def profiledRawJointPostResolveLeftFreshReceiverBoundaryFork
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    FiniteDelayedFork
      (ProfiledRawJointPostResolveFreshTargetRightReceiverControl A strategy) :=
  ⟨(profiledRawJointPostResolveLeftFreshAdvanceRightReceiver A strategy
      oldRoot input).1,
    (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy
      newRoot.1).closedControl⟩

@[simp] theorem
    profiledRawJointPostResolveRightFreshReceiverBoundaryFork_open_key
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    (profiledRawJointPostResolveRightFreshReceiverBoundaryFork A strategy
      oldRoot newRoot input).openControl.1 = .inl oldRoot.1 :=
  rfl

@[simp] theorem
    profiledRawJointPostResolveRightFreshReceiverBoundaryFork_closed_key
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    (profiledRawJointPostResolveRightFreshReceiverBoundaryFork A strategy
      oldRoot newRoot input).closedControl.1 = .inl newRoot.1 :=
  rfl

@[simp] theorem
    profiledRawJointPostResolveLeftFreshReceiverBoundaryFork_open_key
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    (profiledRawJointPostResolveLeftFreshReceiverBoundaryFork A strategy
      oldRoot newRoot input).openControl.1 = .inr oldRoot.1 :=
  rfl

@[simp] theorem
    profiledRawJointPostResolveLeftFreshReceiverBoundaryFork_closed_key
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    (profiledRawJointPostResolveLeftFreshReceiverBoundaryFork A strategy
      oldRoot newRoot input).closedControl.1 = .inr newRoot.1 :=
  rfl

/-! ## Why the same-target blind relation is insufficient -/

/-- Every pair admitted by the current process-one blind relation carries
the same target-bank key. -/
theorem profiledRawJointPostResolveFreshOneBlind_keys_eq
    (left right : ProfiledRawJointPostResolveFreshOneBlindControl A strategy)
    (hblind : ProfiledRawJointPostResolveFreshOneBlind A strategy left right) :
    match left, right with
    | .inl leftReceiver, .inl rightReceiver =>
        leftReceiver.1 = rightReceiver.1
    | .inr leftOwner, .inr rightOwner => leftOwner.1 = rightOwner.1
    | _, _ => False := by
  cases hblind <;> rfl

/-- Process-two mirror. -/
theorem profiledRawJointPostResolveFreshTwoBlind_keys_eq
    (left right : ProfiledRawJointPostResolveFreshTwoBlindControl A strategy)
    (hblind : ProfiledRawJointPostResolveFreshTwoBlind A strategy left right) :
    match left, right with
    | .inl leftReceiver, .inl rightReceiver =>
        leftReceiver.1 = rightReceiver.1
    | .inr leftOwner, .inr rightOwner => leftOwner.1 = rightOwner.1
    | _, _ => False := by
  cases hblind <;> rfl

/-- If the preceding and refreshed right-close targets differ, the actual
boundary fork is not covered by the current same-key blind relation. -/
theorem
    profiledRawJointPostResolveRightFreshReceiverBoundaryFork_not_sameKeyBlind
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) (hne : oldRoot.1 ≠ newRoot.1) :
    ¬ ProfiledRawJointPostResolveFreshOneBlind A strategy
        (.inl
          (profiledRawJointPostResolveRightFreshReceiverBoundaryFork A strategy
            oldRoot newRoot input).openControl)
        (.inl
          (profiledRawJointPostResolveRightFreshReceiverBoundaryFork A strategy
            oldRoot newRoot input).closedControl) := by
  intro hblind
  have hkeys := profiledRawJointPostResolveFreshOneBlind_keys_eq A strategy _ _
    hblind
  exact hne (Sum.inl.inj hkeys)

/-- Mirrored key obstruction. -/
theorem
    profiledRawJointPostResolveLeftFreshReceiverBoundaryFork_not_sameKeyBlind
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) (hne : oldRoot.1 ≠ newRoot.1) :
    ¬ ProfiledRawJointPostResolveFreshTwoBlind A strategy
        (.inl
          (profiledRawJointPostResolveLeftFreshReceiverBoundaryFork A strategy
            oldRoot newRoot input).openControl)
        (.inl
          (profiledRawJointPostResolveLeftFreshReceiverBoundaryFork A strategy
            oldRoot newRoot input).closedControl) := by
  intro hblind
  have hkeys := profiledRawJointPostResolveFreshTwoBlind_keys_eq A strategy _ _
    hblind
  exact hne (Sum.inr.inj hkeys)

/-! ## The fresh closed branch takes the fallback path -/

/-- A newly installed closed left receiver has no staged right target.  Its
first blind non-receive therefore uses the package's arbitrary fallback
right macro. -/
theorem profiledRawJointPostResolveRightFreshClosedReceiver_noRecv_eq_fallback
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy)
    (input : In₁) :
    let globalKey : ProfiledRawJointPostResolveFreshTargetKey A strategy :=
      .inl key
    let source := profiledRawJointPostResolveFreshTargetSource A strategy
      globalKey
    let policy := profiledRawJointPostResolveFreshTargetPolicy A strategy
      globalKey
    let bank := profiledRawJointPostResolveFreshTargetControllerBank A strategy
      globalKey
    let receiver :=
      profiledRawJointPostResolveRightFreshInitialLeftReceiver A strategy key
        .both
    let target := profiledRawJointUnitPolicyFallbackRight A strategy source
      policy bank receiver.1
    let restart := profiledRawJointUnitRestartRight A strategy source policy
      bank target .both
    let next := stepProfiledRawJointUnitRightPolicyOwner A strategy source
      policy bank restart.1 input
    profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv A strategy
        ⟨globalKey, receiver⟩ input =
      (⟨globalKey, next.2⟩, next.1) := by
  simp [profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv,
    profiledRawJointUnitPolicyStartRightOwner,
    profiledRawJointUnitPolicyLeftReceiverTarget,
    profiledRawJointPostResolveRightFreshInitialLeftReceiver,
    initialProfiledRawJointUnitLeftPolicyReceiver]

/-- Mirrored fallback equation. -/
theorem profiledRawJointPostResolveLeftFreshClosedReceiver_noRecv_eq_fallback
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy)
    (input : In₂) :
    let globalKey : ProfiledRawJointPostResolveFreshTargetKey A strategy :=
      .inr key
    let source := profiledRawJointPostResolveFreshTargetSource A strategy
      globalKey
    let policy := profiledRawJointPostResolveFreshTargetPolicy A strategy
      globalKey
    let bank := profiledRawJointPostResolveFreshTargetControllerBank A strategy
      globalKey
    let receiver :=
      profiledRawJointPostResolveLeftFreshInitialRightReceiver A strategy key
        .both
    let target := profiledRawJointUnitPolicyFallbackLeft A strategy source
      policy bank receiver.1
    let restart := profiledRawJointUnitRestartLeft A strategy source policy
      bank target .both
    let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
      policy bank restart.1 input
    profiledRawJointPostResolveFreshTargetRightReceiverNoRecv A strategy
        ⟨globalKey, receiver⟩ input =
      (⟨globalKey, next.2⟩, next.1) := by
  simp [profiledRawJointPostResolveFreshTargetRightReceiverNoRecv,
    profiledRawJointUnitPolicyStartLeftOwner,
    profiledRawJointUnitPolicyRightReceiverTarget,
    profiledRawJointPostResolveLeftFreshInitialRightReceiver,
    initialProfiledRawJointUnitRightPolicyReceiver]

end

end DetParityAutomaton

end DistributedSynthesis
