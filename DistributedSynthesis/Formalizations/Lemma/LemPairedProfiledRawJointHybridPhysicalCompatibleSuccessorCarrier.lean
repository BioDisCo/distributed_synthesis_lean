/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream

/-!
# Sigma-packed acknowledged carrier for compatible successor keys

The preceding file attaches the exact next state of one fixed compatible
policy to every checked physical close.  Here that state becomes the
dependent key of the finite acknowledged carrier.

For a key `q`, the right (respectively left) shared-control fibre is the
finite control of the physical table literally installed in `q`'s current
annotation.  An absent table receives a one-point inert fibre; reachable live
cuts never use that case.  Blind evolution preserves `q` definitionally.
At a close, the crossed carrier is reforked at the state retained in the
target.  Thus annotation replacement is a finite key change, not a lookup
from the bare target and not an accumulating recursive payload.

The right/left distinction below is a proof-side typing of the two local
Mealy interfaces.  No executable map accepts a graph, hierarchy side, leader
bit, strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y s p c d w

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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev SuccessorTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
    initial

/-! ## State-indexed finite table-control fibres -/

/-- Right table control literally installed at `state`.  The inert fibre is
used only where that annotation component is absent. -/
noncomputable abbrev ProfiledRawJointHybridPhysicalCompatibleRightShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (_policy : CompatiblePolicy A strategy hwin initial)
    (_state : CompatibleState A strategy hwin initial) : Type _ :=
  PUnit ⊕
    (Σ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (move.memberController A false).Control)

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleRightShared A strategy hwin
        policy state) := by
  classical
  infer_instance

/-- Left fibre. -/
noncomputable abbrev ProfiledRawJointHybridPhysicalCompatibleLeftShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (_policy : CompatiblePolicy A strategy hwin initial)
    (_state : CompatibleState A strategy hwin initial) : Type _ :=
  PUnit ⊕
    (Σ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (move.memberController A false).Control)

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleLeftShared A strategy hwin
        policy state) := by
  classical
  infer_instance

/-- Initial shared control of the table installed at a right key. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleRightSharedInitial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    ProfiledRawJointHybridPhysicalCompatibleRightShared A strategy hwin
      policy state :=
  match state.1.2.1 with
  | none => .inl PUnit.unit
  | some move => .inr ⟨move,
        (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController
          A strategy hwin policy state move false).initial⟩

/-- Left initial control. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleLeftSharedInitial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    ProfiledRawJointHybridPhysicalCompatibleLeftShared A strategy hwin policy
      state :=
  match state.1.2.2 with
  | none => .inl PUnit.unit
  | some move => .inr ⟨move,
        (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController
          A strategy hwin policy state move false).initial⟩

/-! ## Key-preserving blind evolution -/

/-- Blind owner step in the right state-indexed fibre.  In the live branch it
is literally the sender step of the successor-decorated finite controller. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleRightSharedStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (shared : ProfiledRawJointHybridPhysicalCompatibleRightShared A strategy
      hwin policy state) (input : In₁) :
    ProfiledRawJointHybridPhysicalCompatibleRightShared A strategy hwin policy
        state ×
      Out₁ := by
  classical
  cases shared with
  | inl inert => exact (.inl inert, default)
  | inr installed =>
      let next := profiledRawJointRightPhysicalSiblingDeferredStep A
        installed.1 member installed.2 input
      exact (.inr ⟨installed.1, next.1⟩, next.2)

theorem profiledRawJointHybridPhysicalCompatibleRightSharedStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridPhysicalCompatibleRightSharedStep A strategy hwin
        policy state) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · intro shared input
    cases shared with
    | inl => rfl
    | inr installed =>
        exact (profiledRawJointRightPhysicalSiblingDeferredStep_laws A
          installed.1).outputEq installed.2 input
  · intro shared input
    cases shared with
    | inl => rfl
    | inr installed =>
        simpa only
          [profiledRawJointHybridPhysicalCompatibleRightSharedStep] using
          congrArg
            (fun control ↦
              (Sum.inr ⟨installed.1, control⟩ :
                ProfiledRawJointHybridPhysicalCompatibleRightShared A
                  strategy hwin policy state))
            ((profiledRawJointRightPhysicalSiblingDeferredStep_laws A
              installed.1).stateEq installed.2 input)

/-- Left owner step. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleLeftSharedStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (shared : ProfiledRawJointHybridPhysicalCompatibleLeftShared A strategy
      hwin policy state) (input : In₂) :
    ProfiledRawJointHybridPhysicalCompatibleLeftShared A strategy hwin policy
        state ×
      Out₂ := by
  classical
  cases shared with
  | inl inert => exact (.inl inert, default)
  | inr installed =>
      let next := profiledRawJointLeftPhysicalSiblingDeferredStep A
        installed.1 member installed.2 input
      exact (.inr ⟨installed.1, next.1⟩, next.2)

theorem profiledRawJointHybridPhysicalCompatibleLeftSharedStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridPhysicalCompatibleLeftSharedStep A strategy hwin
        policy state) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · intro shared input
    cases shared with
    | inl => rfl
    | inr installed =>
        exact (profiledRawJointLeftPhysicalSiblingDeferredStep_laws A
          installed.1).outputEq installed.2 input
  · intro shared input
    cases shared with
    | inl => rfl
    | inr installed =>
        simpa only
          [profiledRawJointHybridPhysicalCompatibleLeftSharedStep] using
          congrArg
            (fun control ↦
              (Sum.inr ⟨installed.1, control⟩ :
                ProfiledRawJointHybridPhysicalCompatibleLeftShared A strategy
                  hwin policy state))
            ((profiledRawJointLeftPhysicalSiblingDeferredStep_laws A
              installed.1).stateEq installed.2 input)

/-- In a live right fibre, the shared step is literally the sender step of
the successor-decorated controller. -/
theorem profiledRawJointHybridPhysicalCompatibleRightSharedStep_installed
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (member : Bool) (control : (move.memberController A false).Control)
    (input : In₁) :
    profiledRawJointHybridPhysicalCompatibleRightSharedStep A strategy hwin
        policy state member (.inr ⟨move, control⟩) input =
      let controller :=
        profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController
          A strategy hwin policy state move member
      (.inr ⟨move, controller.step control input⟩,
        (controller.labelOf control).1 input) := by
  rfl

/-- Left installed-fibre equation. -/
theorem profiledRawJointHybridPhysicalCompatibleLeftSharedStep_installed
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (member : Bool) (control : (move.memberController A false).Control)
    (input : In₂) :
    profiledRawJointHybridPhysicalCompatibleLeftSharedStep A strategy hwin
        policy state member (.inr ⟨move, control⟩) input =
      let controller :=
        profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController
          A strategy hwin policy state move member
      (.inr ⟨move, controller.step control input⟩,
        (controller.labelOf control).1 input) := by
  rfl

/-! ## Sigma-packed pending controls -/

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) (Payload : Type p) :=
  FiniteAcknowledgedDelayedCarrier.KeyedDeferredMemberControl
    (CompatibleState A strategy hwin initial)
    (ProfiledRawJointHybridPhysicalCompatibleRightShared A strategy hwin
      policy)
    Payload

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) (Payload : Type p) :=
  FiniteAcknowledgedDelayedCarrier.KeyedDeferredMemberControl
    (CompatibleState A strategy hwin initial)
    (ProfiledRawJointHybridPhysicalCompatibleLeftShared A strategy hwin
      policy)
    Payload

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Payload : Type p} [Fintype Payload] :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl A strategy
        hwin policy Payload) := by
  classical
  infer_instance

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Payload : Type p} [Fintype Payload] :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl A strategy
        hwin policy Payload) := by
  classical
  infer_instance

/-- Blind right evolution on the sigma control. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightDeferredNoRecv
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) {Payload : Type p} :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberNoRecv
    (Payload := Payload)
    (fun state ↦
      profiledRawJointHybridPhysicalCompatibleRightSharedStep A strategy hwin
        policy state)

/-- Blind left evolution. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftDeferredNoRecv
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) {Payload : Type p} :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberNoRecv
    (Payload := Payload)
    (fun state ↦
      profiledRawJointHybridPhysicalCompatibleLeftSharedStep A strategy hwin
        policy state)

/-- Blind right steps preserve the compatible-policy key definitionally. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightDeferredNoRecv_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) {Payload : Type p}
    (control :
      ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl A strategy
        hwin policy Payload)
    (input : In₁) :
    (profiledRawJointHybridPhysicalCompatibleRightDeferredNoRecv A strategy
      hwin policy control input).1.1.1 = control.1.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftDeferredNoRecv_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) {Payload : Type p}
    (control :
      ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl A strategy
        hwin policy Payload)
    (input : In₂) :
    (profiledRawJointHybridPhysicalCompatibleLeftDeferredNoRecv A strategy
      hwin policy control input).1.1.1 = control.1.1 :=
  rfl

/-- The sigma-packed right step satisfies the unresolved-member laws. -/
theorem profiledRawJointHybridPhysicalCompatibleRightDeferredStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
        (fun state ↦
          profiledRawJointHybridPhysicalCompatibleRightSharedStep A strategy
            hwin policy state)) := by
  exact FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep_laws _
    (fun state ↦
      profiledRawJointHybridPhysicalCompatibleRightSharedStep_laws A strategy
        hwin policy state)

theorem profiledRawJointHybridPhysicalCompatibleLeftDeferredStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
        (fun state ↦
          profiledRawJointHybridPhysicalCompatibleLeftSharedStep A strategy
            hwin policy state)) := by
  exact FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep_laws _
    (fun state ↦
      profiledRawJointHybridPhysicalCompatibleLeftSharedStep_laws A strategy
        hwin policy state)

/-! ## Exact close and acknowledged refork -/

variable {Payload : Type p}

/-- Canonical right pending fork at a specified compatible key. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleRightForkAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) (payload : Payload) :
    FiniteDelayedFork
      (ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl A strategy
        hwin policy Payload) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork state
    (profiledRawJointHybridPhysicalCompatibleRightSharedInitial A strategy hwin
      policy state)
    payload

/-- Left pending fork. -/
noncomputable def profiledRawJointHybridPhysicalCompatibleLeftForkAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) (payload : Payload) :
    FiniteDelayedFork
      (ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl A strategy
        hwin policy Payload) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork state
    (profiledRawJointHybridPhysicalCompatibleLeftSharedInitial A strategy hwin
      policy state)
    payload

@[simp] theorem profiledRawJointHybridPhysicalCompatibleRightForkAt_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) (payload : Payload)
    (member : Bool) :
    ((profiledRawJointHybridPhysicalCompatibleRightForkAt A strategy hwin
      policy state payload).candidate member).1.1 = state := by
  cases member <;> rfl

@[simp] theorem profiledRawJointHybridPhysicalCompatibleLeftForkAt_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) (payload : Payload)
    (member : Bool) :
    ((profiledRawJointHybridPhysicalCompatibleLeftForkAt A strategy hwin
      policy state payload).candidate member).1.1 = state := by
  cases member <;> rfl

/-- If the right table is present in the key, a fresh fork installs exactly
that move and the decorated controller's initial control. -/
theorem profiledRawJointHybridPhysicalCompatibleRightForkAt_installed
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (payload : Payload) (member : Bool) :
    ((profiledRawJointHybridPhysicalCompatibleRightForkAt A strategy hwin
      policy state payload).candidate member).1.2.2 =
      .inr ⟨move,
        (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController
          A strategy hwin policy state move false).initial⟩ := by
  cases member <;>
    simp [profiledRawJointHybridPhysicalCompatibleRightForkAt,
      profiledRawJointHybridPhysicalCompatibleRightSharedInitial, hmove,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork,
      FiniteDelayedFork.candidate]

/-- Left installed-table mirror. -/
theorem profiledRawJointHybridPhysicalCompatibleLeftForkAt_installed
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (payload : Payload) (member : Bool) :
    ((profiledRawJointHybridPhysicalCompatibleLeftForkAt A strategy hwin
      policy state payload).candidate member).1.2.2 =
      .inr ⟨move,
        (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController
          A strategy hwin policy state move false).initial⟩ := by
  cases member <;>
    simp [profiledRawJointHybridPhysicalCompatibleLeftForkAt,
      profiledRawJointHybridPhysicalCompatibleLeftSharedInitial, hmove,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork,
      FiniteDelayedFork.candidate]

/-- A right physical close installs a left pending fork at exactly the state
retained by that same row's target. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload) :
    FiniteDelayedFork
      (ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl A strategy
        hwin policy Payload) :=
  profiledRawJointHybridPhysicalCompatibleLeftForkAt A strategy hwin policy
    (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
      hwin target)
    payload

/-- Left physical close installs the right carrier. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload) :
    FiniteDelayedFork
      (ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl A strategy
        hwin policy Payload) :=
  profiledRawJointHybridPhysicalCompatibleRightForkAt A strategy hwin policy
    (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
      hwin target)
    payload

/-- Exact retained-key theorem at a right close. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTarget_transition
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload)
    (hkey : ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1)
    (member : Bool) :
    let candidate :=
      (profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTarget A strategy
        hwin policy target payload).candidate member
    candidate.1.1 =
        profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target ∧
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state candidate.1.1 target.1 := by
  dsimp only
  have htarget :=
    profiledRawJointHybridPhysicalCompatibleLeftForkAt_key A strategy hwin
      policy
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)
      payload member
  exact ⟨htarget, htarget ▸ hkey⟩

/-- Left-close mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTarget_transition
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload)
    (hkey : ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1)
    (member : Bool) :
    let candidate :=
      (profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTarget A strategy
        hwin policy target payload).candidate member
    candidate.1.1 =
        profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target ∧
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state candidate.1.1 target.1 := by
  dsimp only
  have htarget :=
    profiledRawJointHybridPhysicalCompatibleRightForkAt_key A strategy hwin
      policy
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)
      payload member
  exact ⟨htarget, htarget ▸ hkey⟩

/-- Reforking at a right close installs precisely the target-keyed left fork
and the generic acknowledgement computed from the two delivered relays. -/
theorem
    profiledRawJointHybridPhysicalCompatible_reforkLeftAtRightTarget_current
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Control : Type c} {Delivered : Type d}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload) :
    (FiniteAcknowledgedDelayedCarrier.refork own partner
      (profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTarget A strategy
        hwin policy target payload)).current =
      .fork (FiniteAcknowledgedDelayedCarrier.freshId own partner)
        (profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTarget A
          strategy hwin policy target payload) :=
  rfl

/-- Reforking at a left close. -/
theorem
    profiledRawJointHybridPhysicalCompatible_reforkRightAtLeftTarget_current
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Control : Type c} {Delivered : Type d}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload) :
    (FiniteAcknowledgedDelayedCarrier.refork own partner
      (profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTarget A strategy
        hwin policy target payload)).current =
      .fork (FiniteAcknowledgedDelayedCarrier.freshId own partner)
      (profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTarget A
          strategy hwin policy target payload) :=
  rfl

/-- Compatible key exposed by one candidate of the crossed left fork.  The
explicit codomain hides the irrelevant universe of the rest of the pending
control from later cut-indexed structures. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTargetKey
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload)
    (member : Bool) : CompatibleState A strategy hwin initial :=
  let fork : FiniteDelayedFork
      (ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl.{u, v, x,
        y, s, p, max u v x y s} A strategy hwin policy Payload) :=
    profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTarget.{u, v, x,
      y, s, p, max u v x y s} A strategy hwin policy target payload
  (fork.candidate member).1.1

/-- Right-fork mirror key projection. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTargetKey
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload)
    (member : Bool) : CompatibleState A strategy hwin initial :=
  let fork : FiniteDelayedFork
      (ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl.{u, v, x,
        y, s, p, max u v x y s} A strategy hwin policy Payload) :=
    profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTarget.{u, v, x,
      y, s, p, max u v x y s} A strategy hwin policy target payload
  (fork.candidate member).1.1

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTargetKey_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload)
    (member : Bool) :
    profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTargetKey A strategy
        hwin policy target payload member =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target := by
  exact profiledRawJointHybridPhysicalCompatibleLeftForkAt_key A strategy hwin
    policy
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)
      payload member

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTargetKey_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial) (payload : Payload)
    (member : Bool) :
    profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTargetKey A strategy
        hwin policy target payload member =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target := by
  exact profiledRawJointHybridPhysicalCompatibleRightForkAt_key A strategy
    hwin policy
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)
      payload member

/-! ## Cut-indexed carrier trace -/

/-- Recurrent carrier audit after the separate exact common-root exit.

The generic cut-stream consumer asks directly that `state (n+1)` equal the
retained target key.  A concrete acknowledged implementation instead reaches
that key as one candidate of the freshly installed crossed fork.  The
`carrier_next` field records exactly that local fact.  The theorem below
turns it into the consumer's `next_state` equation using the two literal fork
key lemmas above.

The common-to-one-sided exit remains explicit and is not disguised as a
recurrent sibling-table step. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (Payload : Type p)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  initial_code :
    (policy.run []).1.1 =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  initial_live :
    profiledRawJointHybridCurrentSlots A initialSide (policy.run []).1.1 () =
      some initialRoot
  exitTarget : SuccessorTarget A strategy hwin initial
  exitRoot : ProfiledRawJointThreadRoot A
  exit_at :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run []) exitTarget
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide 1)
        exitRoot
  state : Nat → CompatibleState A strategy hwin initial
  state_zero :
    state 0 =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin exitTarget
  target : Nat → SuccessorTarget A strategy hwin initial
  rootAt : Nat → ProfiledRawJointThreadRoot A
  target_at : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (state n) (target n)
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2))
        (rootAt n)
  member : Nat → Bool
  payload : Nat → Payload
  /-- The following compatible key is read from the actual candidate of the
  freshly installed crossed fork.  Which fork is used is determined only in
  this proof-side audit by the carried lineage side; neither endpoint is
  passed that side. -/
  carrier_next : ∀ n : Nat,
    state (n + 1) =
      match profiledRawJointHybridPhysicalCompatibleSideAfter initialSide
          (n + 2) with
      | .left =>
          profiledRawJointHybridPhysicalCompatibleLeftForkAtRightTargetKey A
            strategy hwin policy (target n) (payload n) (member n)
      | .right =>
          profiledRawJointHybridPhysicalCompatibleRightForkAtLeftTargetKey A
            strategy hwin policy (target n) (payload n) (member n)
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  exit_blockMin :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts 0 =
      profiledRawJointThreadRootPriority A exitRoot
  recurrent_blockMin : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts (k + 1) =
      profiledRawJointThreadRootPriority A (rootAt k)

namespace
    ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {Payload : Type p}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- The fork-selected next key is literally the target key. -/
theorem next_state
    (tail :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail A
        strategy hwin policy Payload G outputOne outputTwo env)
    (n : Nat) :
    tail.state (n + 1) =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (tail.target n) := by
  rw [tail.carrier_next n]
  cases hside : profiledRawJointHybridPhysicalCompatibleSideAfter
      tail.initialSide (n + 2) with
  | left => simp
  | right => simp

/-- Forget only the concrete fork presentation.  The result is the exact
initial-exit cut tail consumed by the coherent path/alignment theorem. -/
noncomputable def toSuccessorCutTail
    (tail :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail A
        strategy hwin policy Payload G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit A
      strategy hwin policy G outputOne outputTwo env where
  initial_code := tail.initial_code
  initialSide := tail.initialSide
  initialRoot := tail.initialRoot
  initial_live := tail.initial_live
  exitTarget := tail.exitTarget
  exitRoot := tail.exitRoot
  exit_at := tail.exit_at
  state := tail.state
  state_zero := tail.state_zero
  target := tail.target
  rootAt := tail.rootAt
  target_at := tail.target_at
  next_state := tail.next_state A strategy hwin
  start := tail.start
  cuts := tail.cuts
  cuts_strictMono := tail.cuts_strictMono
  cuts_zero := tail.cuts_zero
  exit_blockMin := tail.exit_blockMin
  recurrent_blockMin := tail.recurrent_blockMin

/-- End-to-end acceptance of any finite-machine trace satisfying the concrete
acknowledged carrier cut audit. -/
theorem accepts
    (tail :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail A
        strategy hwin policy Payload G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (tail.toSuccessorCutTail A strategy hwin).accepts A strategy hwin

end
  ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail

end

end DetParityAutomaton

end DistributedSynthesis
