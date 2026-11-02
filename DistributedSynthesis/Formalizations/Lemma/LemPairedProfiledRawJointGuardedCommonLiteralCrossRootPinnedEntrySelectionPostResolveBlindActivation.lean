/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveStagedTarget
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBlindForkInvariant

/-!
# Blind activation of a staged post-resolve target

After an informed post-resolve endpoint has staged a recurrent root, its next
local non-receive starts the owner at that root.  At a simultaneous close the
same endpoint may instead already be interpreted as that recurrent owner.
These are the open and exact-close candidates of the acknowledged carrier.

This file proves the important output-aware fact: the staged descriptor and
the recurrent owner take literally the same owner step.  Hence their outputs
are equal and their next controls coincide.  The result is the endpoint-local
blind no-receive law required by `ExactClosingBlindForkLaws`.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev LeftSenderState :=
  ProfiledRawJointStrictLeftPostResolveFiniteSenderState A

private abbrev RightSenderState :=
  ProfiledRawJointStrictRightPostResolveFiniteSenderState A

/-! ## Recurrent owner steps over the oriented target bank -/

/-- State-first local step for any left owner in the finite target bank. -/
noncomputable def profiledRawJointPostResolveFreshTargetLeftOwnerNoRecv
    (control :
      ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy)
    (input : In₂) :
    ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy × Out₂ :=
  match control with
  | ⟨key, owner⟩ =>
      let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy
        (profiledRawJointPostResolveFreshTargetSource A strategy key)
        (profiledRawJointPostResolveFreshTargetPolicy A strategy key)
        (profiledRawJointPostResolveFreshTargetControllerBank A strategy key)
        owner input
      (⟨key, next.2⟩, next.1)

/-- Mirrored state-first step for a right owner. -/
noncomputable def profiledRawJointPostResolveFreshTargetRightOwnerNoRecv
    (control :
      ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy)
    (input : In₁) :
    ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy × Out₁ :=
  match control with
  | ⟨key, owner⟩ =>
      let next := stepProfiledRawJointUnitRightPolicyOwner A strategy
        (profiledRawJointPostResolveFreshTargetSource A strategy key)
        (profiledRawJointPostResolveFreshTargetPolicy A strategy key)
        (profiledRawJointPostResolveFreshTargetControllerBank A strategy key)
        owner input
      (⟨key, next.2⟩, next.1)

/-! ## The two endpoint-local bridge controls -/

/-- Process two is either still an informed right-block descriptor with a
staged target, or is already the left owner selected by an exact close. -/
abbrev ProfiledRawJointStrictLeftPostResolveTwoBlindControl :=
  ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy ⊕
    ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy

/-- Process-one mirror. -/
abbrev ProfiledRawJointStrictRightPostResolveOneBlindControl :=
  ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy ⊕
    ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy

noncomputable instance :
    Fintype (ProfiledRawJointStrictLeftPostResolveTwoBlindControl A strategy) :=
  by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointStrictRightPostResolveOneBlindControl A strategy) :=
  by
  classical
  infer_instance

/-- A staged process-two descriptor starts its stored left owner.  Failure is
totalized by retaining the descriptor and emitting `default`; the blind
relation below contains only successful staged states. -/
noncomputable def profiledRawJointStrictLeftPostResolveTwoBlindNoRecv
    (control :
      ProfiledRawJointStrictLeftPostResolveTwoBlindControl A strategy)
    (input : In₂) :
    ProfiledRawJointStrictLeftPostResolveTwoBlindControl A strategy × Out₂ :=
  match control with
  | .inl state =>
      match state.2 with
      | none => (.inl state, default)
      | some root =>
          let next := profiledRawJointPostResolveFreshTargetLeftOwnerNoRecv A
            strategy ⟨.inl root.1, root.2.1⟩ input
          (.inr next.1, next.2)
  | .inr owner =>
      let next := profiledRawJointPostResolveFreshTargetLeftOwnerNoRecv A
        strategy owner input
      (.inr next.1, next.2)

/-- Mirrored staged activation. -/
noncomputable def profiledRawJointStrictRightPostResolveOneBlindNoRecv
    (control :
      ProfiledRawJointStrictRightPostResolveOneBlindControl A strategy)
    (input : In₁) :
    ProfiledRawJointStrictRightPostResolveOneBlindControl A strategy × Out₁ :=
  match control with
  | .inl state =>
      match state.2 with
      | none => (.inl state, default)
      | some root =>
          let next := profiledRawJointPostResolveFreshTargetRightOwnerNoRecv A
            strategy ⟨.inr root.1, root.2.1⟩ input
          (.inr next.1, next.2)
  | .inr owner =>
      let next := profiledRawJointPostResolveFreshTargetRightOwnerNoRecv A
        strategy owner input
      (.inr next.1, next.2)

/-! ## Exact blind relations -/

/-- The open descriptor and exact-close owner are related precisely when the
owner is the projection of the root stored in the descriptor.  Equality is
the recurrent closure case. -/
inductive ProfiledRawJointStrictLeftPostResolveTwoBlind :
    ProfiledRawJointStrictLeftPostResolveTwoBlindControl A strategy →
      ProfiledRawJointStrictLeftPostResolveTwoBlindControl A strategy → Prop
  | staged
      (state :
        ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
      (root : ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
      (hroot : state.2 = some root) :
      ProfiledRawJointStrictLeftPostResolveTwoBlind
        (.inl state) (.inr ⟨.inl root.1, root.2.1⟩)
  | recurrent
      (owner :
        ProfiledRawJointPostResolveFreshTargetLeftOwnerControl A strategy) :
      ProfiledRawJointStrictLeftPostResolveTwoBlind (.inr owner) (.inr owner)

/-- Mirrored process-one blind relation. -/
inductive ProfiledRawJointStrictRightPostResolveOneBlind :
    ProfiledRawJointStrictRightPostResolveOneBlindControl A strategy →
      ProfiledRawJointStrictRightPostResolveOneBlindControl A strategy → Prop
  | staged
      (state :
        ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
      (root : ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
      (hroot : state.2 = some root) :
      ProfiledRawJointStrictRightPostResolveOneBlind
        (.inl state) (.inr ⟨.inr root.1, root.2.1⟩)
  | recurrent
      (owner :
        ProfiledRawJointPostResolveFreshTargetRightOwnerControl A strategy) :
      ProfiledRawJointStrictRightPostResolveOneBlind (.inr owner) (.inr owner)

/-- The two interpretations of process two take one literally identical
owner step.  This proves both output equality and relation preservation. -/
theorem profiledRawJointStrictLeftPostResolveTwoBlind_noRecv
    (left right :
      ProfiledRawJointStrictLeftPostResolveTwoBlindControl A strategy)
    (input : In₂)
    (hblind : ProfiledRawJointStrictLeftPostResolveTwoBlind A strategy left
      right) :
    (profiledRawJointStrictLeftPostResolveTwoBlindNoRecv A strategy left
        input).2 =
        (profiledRawJointStrictLeftPostResolveTwoBlindNoRecv A strategy right
          input).2 ∧
      ProfiledRawJointStrictLeftPostResolveTwoBlind A strategy
        (profiledRawJointStrictLeftPostResolveTwoBlindNoRecv A strategy left
          input).1
        (profiledRawJointStrictLeftPostResolveTwoBlindNoRecv A strategy right
          input).1 := by
  cases hblind with
  | staged state root hroot =>
      simp only [profiledRawJointStrictLeftPostResolveTwoBlindNoRecv, hroot]
      exact ⟨trivial, .recurrent _⟩
  | recurrent owner =>
      exact ⟨rfl, .recurrent _⟩

/-- Mirrored blind no-receive law. -/
theorem profiledRawJointStrictRightPostResolveOneBlind_noRecv
    (left right :
      ProfiledRawJointStrictRightPostResolveOneBlindControl A strategy)
    (input : In₁)
    (hblind : ProfiledRawJointStrictRightPostResolveOneBlind A strategy left
      right) :
    (profiledRawJointStrictRightPostResolveOneBlindNoRecv A strategy left
        input).2 =
        (profiledRawJointStrictRightPostResolveOneBlindNoRecv A strategy right
          input).2 ∧
      ProfiledRawJointStrictRightPostResolveOneBlind A strategy
        (profiledRawJointStrictRightPostResolveOneBlindNoRecv A strategy left
          input).1
        (profiledRawJointStrictRightPostResolveOneBlindNoRecv A strategy right
          input).1 := by
  cases hblind with
  | staged state root hroot =>
      simp only [profiledRawJointStrictRightPostResolveOneBlindNoRecv, hroot]
      exact ⟨trivial, .recurrent _⟩
  | recurrent owner =>
      exact ⟨rfl, .recurrent _⟩

/-! ## Reachable dispatcher forks satisfy the blind relation -/

/-- The next staged descriptor and its exact recurrent owner projection are
the two blind-related process-two candidates created by a reachable
right-block receive. -/
theorem profiledRawJointStrictLeftPostResolveStagedDispatch_twoBlind
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool)
    (state : LeftSenderState A ×
      ProfiledRawJointStrictLeftPostResolveStagedReceiverState A strategy)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch (state.1, state.2.1))
    (current : In₂ × In₁) :
    let next := (profiledRawJointStrictLeftPostResolveStagedDispatch A strategy
      state current.1 current.2).nextReceiver
    ∃ root : ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy,
      next.2 = some root ∧
        ProfiledRawJointStrictLeftPostResolveTwoBlind A strategy
          (.inl next) (.inr ⟨.inl root.1, root.2.1⟩) := by
  dsimp only
  obtain ⟨root, hroot⟩ :=
    profiledRawJointStrictLeftPostResolveStagedDispatch_isSome A strategy hwin
      initial entry input branch state hstate current
  exact ⟨root, hroot, .staged _ root hroot⟩

/-- Mirrored reachable receive-created blind fork. -/
theorem profiledRawJointStrictRightPostResolveStagedDispatch_oneBlind
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool)
    (state : RightSenderState A ×
      ProfiledRawJointStrictRightPostResolveStagedReceiverState A strategy)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch (state.1, state.2.1))
    (current : In₁ × In₂) :
    let next :=
      (profiledRawJointStrictRightPostResolveStagedDispatch A strategy state
        current.1 current.2).nextReceiver
    ∃ root : ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy,
      next.2 = some root ∧
        ProfiledRawJointStrictRightPostResolveOneBlind A strategy
          (.inl next) (.inr ⟨.inr root.1, root.2.1⟩) := by
  dsimp only
  obtain ⟨root, hroot⟩ :=
    profiledRawJointStrictRightPostResolveStagedDispatch_isSome A strategy hwin
      initial entry input branch state hstate current
  exact ⟨root, hroot, .staged _ root hroot⟩

end

end DetParityAutomaton

end DistributedSynthesis
