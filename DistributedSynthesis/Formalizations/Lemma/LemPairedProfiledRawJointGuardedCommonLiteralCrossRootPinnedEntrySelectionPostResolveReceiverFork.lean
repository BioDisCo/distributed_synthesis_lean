/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveBlindActivation

/-!
# Two-row recurrent receiver forks below a staged target

The row used to select a target from a completed block and the rows of the
next receive-created ambiguity have different roles.  The old strict/common
member selects one target.  At that fixed target, the new strict/open and
simultaneous/closed candidates are receiver roots at rows `first` and `both`.

Both roots have the same source macro and initially have no staged opposite
target.  Consequently a local non-receive makes both execute the same
fallback restart and produces the identical recurrent owner.  This file
states and proves that receiver-side blind-fork law for both orientations.
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

/-! ## Fresh receiver roots at the two new rows -/

/-- At one right-close target, retain both possible process-one left-receiver
roots.  The target key was already selected using the old block row. -/
noncomputable def profiledRawJointPostResolveRightFreshLeftReceiverFork
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy) :
    FiniteDelayedFork
      (ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A strategy) :=
  ⟨⟨.inl key,
      profiledRawJointPostResolveRightFreshInitialLeftReceiver A strategy key
        .first⟩,
    ⟨.inl key,
      profiledRawJointPostResolveRightFreshInitialLeftReceiver A strategy key
        .both⟩⟩

/-- Mirrored process-two right-receiver fork below a left-close target. -/
noncomputable def profiledRawJointPostResolveLeftFreshRightReceiverFork
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy) :
    FiniteDelayedFork
      (ProfiledRawJointPostResolveFreshTargetRightReceiverControl A strategy) :=
  ⟨⟨.inr key,
      profiledRawJointPostResolveLeftFreshInitialRightReceiver A strategy key
        .first⟩,
    ⟨.inr key,
      profiledRawJointPostResolveLeftFreshInitialRightReceiver A strategy key
        .both⟩⟩

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointPostResolveRightFreshLeftReceiverFork_open_row
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy) :
    (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy key
      ).openControl.2.2.1 = .first :=
  rfl

@[simp] theorem profiledRawJointPostResolveRightFreshLeftReceiverFork_closed_row
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy) :
    (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy key
      ).closedControl.2.2.1 = .both :=
  rfl

@[simp] theorem profiledRawJointPostResolveLeftFreshRightReceiverFork_open_row
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy) :
    (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy key
      ).openControl.2.2.1 = .first :=
  rfl

@[simp] theorem profiledRawJointPostResolveLeftFreshRightReceiverFork_closed_row
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy) :
    (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy key
      ).closedControl.2.2.1 = .both :=
  rfl

end

/-! ## The blind receiver-to-owner transition -/

/-- A process-one left receiver starts the right owner staged by its local
receiver state.  The target-bank key itself is unchanged. -/
noncomputable def profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv
    (control :
      ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A strategy)
    (input : In₁) :
    ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy × Out₁ :=
  match control with
  | ⟨key, receiver⟩ =>
      let next := profiledRawJointUnitPolicyStartRightOwner A strategy
        (profiledRawJointPostResolveFreshTargetSource A strategy key)
        (profiledRawJointPostResolveFreshTargetPolicy A strategy key)
        (profiledRawJointPostResolveFreshTargetControllerBank A strategy key)
        receiver input
      (⟨key, next.2⟩, next.1)

/-- Process-two mirror. -/
noncomputable def profiledRawJointPostResolveFreshTargetRightReceiverNoRecv
    (control :
      ProfiledRawJointPostResolveFreshTargetRightReceiverControl A strategy)
    (input : In₂) :
    ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy × Out₂ :=
  match control with
  | ⟨key, receiver⟩ =>
      let next := profiledRawJointUnitPolicyStartLeftOwner A strategy
        (profiledRawJointPostResolveFreshTargetSource A strategy key)
        (profiledRawJointPostResolveFreshTargetPolicy A strategy key)
        (profiledRawJointPostResolveFreshTargetControllerBank A strategy key)
        receiver input
      (⟨key, next.2⟩, next.1)

/-- The fresh first/both left receivers take definitionally the same local
non-receive step. -/
theorem profiledRawJointPostResolveRightFreshLeftReceiverFork_noRecv_eq
    (key : ProfiledRawJointPostResolveRightFreshTarget A strategy)
    (input : In₁) :
    profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv A strategy
        (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy key
          ).openControl input =
      profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv A strategy
        (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy key
          ).closedControl input := by
  rfl

/-- Mirrored definitional equality. -/
theorem profiledRawJointPostResolveLeftFreshRightReceiverFork_noRecv_eq
    (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy)
    (input : In₂) :
    profiledRawJointPostResolveFreshTargetRightReceiverNoRecv A strategy
        (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy key
          ).openControl input =
      profiledRawJointPostResolveFreshTargetRightReceiverNoRecv A strategy
        (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy key
          ).closedControl input := by
  rfl

/-! ## Output-aware blind relations -/

/-- Process one's receiver fork followed by its common right-owner state. -/
abbrev ProfiledRawJointPostResolveFreshOneBlindControl :=
  ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A strategy ⊕
    ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy

/-- Process-two mirror. -/
abbrev ProfiledRawJointPostResolveFreshTwoBlindControl :=
  ProfiledRawJointPostResolveFreshTargetRightReceiverControl A strategy ⊕
    ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveFreshOneBlindControl A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolveFreshTwoBlindControl A strategy) := by
  classical
  infer_instance

/-- Total process-one blind step. -/
noncomputable def profiledRawJointPostResolveFreshOneBlindNoRecv
    (control : ProfiledRawJointPostResolveFreshOneBlindControl A strategy)
    (input : In₁) :
    ProfiledRawJointPostResolveFreshOneBlindControl A strategy × Out₁ :=
  match control with
  | .inl receiver =>
      let next := profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv A
        strategy receiver input
      (.inr next.1, next.2)
  | .inr owner =>
      let next := profiledRawJointPostResolveFreshTargetRightOwnerNoRecv A
        strategy owner input
      (.inr next.1, next.2)

/-- Total process-two mirror. -/
noncomputable def profiledRawJointPostResolveFreshTwoBlindNoRecv
    (control : ProfiledRawJointPostResolveFreshTwoBlindControl A strategy)
    (input : In₂) :
    ProfiledRawJointPostResolveFreshTwoBlindControl A strategy × Out₂ :=
  match control with
  | .inl receiver =>
      let next := profiledRawJointPostResolveFreshTargetRightReceiverNoRecv A
        strategy receiver input
      (.inr next.1, next.2)
  | .inr owner =>
      let next := profiledRawJointPostResolveFreshTargetLeftOwnerNoRecv A
        strategy owner input
      (.inr next.1, next.2)

/-- The only unresolved receiver pair is the first/both root fork at one
right-close key; recurrent owners are related by equality. -/
inductive ProfiledRawJointPostResolveFreshOneBlind :
    ProfiledRawJointPostResolveFreshOneBlindControl A strategy →
      ProfiledRawJointPostResolveFreshOneBlindControl A strategy → Prop
  | root (key : ProfiledRawJointPostResolveRightFreshTarget A strategy) :
      ProfiledRawJointPostResolveFreshOneBlind
        (.inl
          (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy key
            ).openControl)
        (.inl
          (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy key
            ).closedControl)
  | recurrent
      (owner :
        ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy) :
      ProfiledRawJointPostResolveFreshOneBlind (.inr owner) (.inr owner)

/-- Process-two mirrored relation. -/
inductive ProfiledRawJointPostResolveFreshTwoBlind :
    ProfiledRawJointPostResolveFreshTwoBlindControl A strategy →
      ProfiledRawJointPostResolveFreshTwoBlindControl A strategy → Prop
  | root (key : ProfiledRawJointPostResolveLeftFreshTarget A strategy) :
      ProfiledRawJointPostResolveFreshTwoBlind
        (.inl
          (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy key
            ).openControl)
        (.inl
          (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy key
            ).closedControl)
  | recurrent
      (owner :
        ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy) :
      ProfiledRawJointPostResolveFreshTwoBlind (.inr owner) (.inr owner)

/-- Process-one root-fork output coherence and closure. -/
theorem profiledRawJointPostResolveFreshOneBlind_noRecv
    (left right : ProfiledRawJointPostResolveFreshOneBlindControl A strategy)
    (input : In₁)
    (hblind : ProfiledRawJointPostResolveFreshOneBlind A strategy left right) :
    (profiledRawJointPostResolveFreshOneBlindNoRecv A strategy left input).2 =
        (profiledRawJointPostResolveFreshOneBlindNoRecv A strategy right
          input).2 ∧
      ProfiledRawJointPostResolveFreshOneBlind A strategy
        (profiledRawJointPostResolveFreshOneBlindNoRecv A strategy left
          input).1
        (profiledRawJointPostResolveFreshOneBlindNoRecv A strategy right
          input).1 := by
  cases hblind with
  | root key =>
      simp only [profiledRawJointPostResolveFreshOneBlindNoRecv]
      rw [show
        profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv A strategy
            (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy
              key).openControl input =
          profiledRawJointPostResolveFreshTargetLeftReceiverNoRecv A strategy
            (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy
              key).closedControl input from
        profiledRawJointPostResolveRightFreshLeftReceiverFork_noRecv_eq A
          strategy key input]
      exact ⟨rfl, .recurrent _⟩
  | recurrent owner =>
      exact ⟨rfl, .recurrent _⟩

/-- Process-two root-fork output coherence and closure. -/
theorem profiledRawJointPostResolveFreshTwoBlind_noRecv
    (left right : ProfiledRawJointPostResolveFreshTwoBlindControl A strategy)
    (input : In₂)
    (hblind : ProfiledRawJointPostResolveFreshTwoBlind A strategy left right) :
    (profiledRawJointPostResolveFreshTwoBlindNoRecv A strategy left input).2 =
        (profiledRawJointPostResolveFreshTwoBlindNoRecv A strategy right
          input).2 ∧
      ProfiledRawJointPostResolveFreshTwoBlind A strategy
        (profiledRawJointPostResolveFreshTwoBlindNoRecv A strategy left
          input).1
        (profiledRawJointPostResolveFreshTwoBlindNoRecv A strategy right
          input).1 := by
  cases hblind with
  | root key =>
      simp only [profiledRawJointPostResolveFreshTwoBlindNoRecv]
      rw [show
        profiledRawJointPostResolveFreshTargetRightReceiverNoRecv A strategy
            (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy
              key).openControl input =
          profiledRawJointPostResolveFreshTargetRightReceiverNoRecv A strategy
            (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy
              key).closedControl input from
        profiledRawJointPostResolveLeftFreshRightReceiverFork_noRecv_eq A
          strategy key input]
      exact ⟨rfl, .recurrent _⟩
  | recurrent owner =>
      exact ⟨rfl, .recurrent _⟩

/-! ## Build the new fork from the previously staged key -/

/-- The delivered process-two staged state supplies the complete first/both
process-one receiver fork, not merely the old selected-row receiver. -/
noncomputable def profiledRawJointStrictLeftPostResolveStagedLeftReceiverFork?
    (state :
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy) :
    Option
      (FiniteDelayedFork
        (ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A
          strategy)) :=
  state.2.map fun root ↦
    profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy root.1

/-- Mirrored delivered fork. -/
noncomputable def profiledRawJointStrictRightPostResolveStagedRightReceiverFork?
    (state :
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy) :
    Option
      (FiniteDelayedFork
        (ProfiledRawJointPostResolveFreshTargetRightReceiverControl A
          strategy)) :=
  state.2.map fun root ↦
    profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy root.1

theorem profiledRawJointStrictLeftPostResolveStagedLeftReceiverFork?_eq_some
    (state :
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (root : ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (hroot : state.2 = some root) :
    profiledRawJointStrictLeftPostResolveStagedLeftReceiverFork? A strategy
        state =
      some
        (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy
          root.1) := by
  simp [profiledRawJointStrictLeftPostResolveStagedLeftReceiverFork?, hroot]

theorem profiledRawJointStrictRightPostResolveStagedRightReceiverFork?_eq_some
    (state :
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (root : ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (hroot : state.2 = some root) :
    profiledRawJointStrictRightPostResolveStagedRightReceiverFork? A strategy
        state =
      some
        (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy
          root.1) := by
  simp [profiledRawJointStrictRightPostResolveStagedRightReceiverFork?, hroot]

end

end DetParityAutomaton

end DistributedSynthesis
