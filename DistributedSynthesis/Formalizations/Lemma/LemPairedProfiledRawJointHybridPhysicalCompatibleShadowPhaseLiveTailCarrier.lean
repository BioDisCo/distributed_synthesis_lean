/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingPhaseLiveOverlay
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailDecoration

/-!
# Finite state-indexed carriers in one delayed-tag tail fibre

For a fixed delivered tag, the changing key is the state of that tag's
ordinary re-rooted policy.  A right or left shared carrier stores exactly the
finite physical sibling move installed in the key and the finite sender
control of its decorated table.  Blind evolution preserves the tail key
definitionally and satisfies the unresolved-member laws.

These types are the concrete dynamic core of one tag fibre.  The outer bank
will sigma-pack them over the finite tag type.  No executable function below
takes a graph, orientation, leader bit, strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y s p

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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-! ## State-indexed physical owner controls -/

/-- Right-table sender state literally installed at a tail key.  The one-point
summand totalizes absent annotations. -/
noncomputable abbrev ProfiledRawJointHybridShadowPhaseLiveTailRightShared
    (_tag : Tag A strategy hwin)
    (_state : TailState A strategy hwin _tag) : Type _ :=
  PUnit ⊕
    (Σ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (move.memberController A false).Control)

noncomputable instance
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailRightShared A strategy hwin tag
        state) := by
  classical
  infer_instance

/-- Left-table mirror. -/
noncomputable abbrev ProfiledRawJointHybridShadowPhaseLiveTailLeftShared
    (_tag : Tag A strategy hwin)
    (_state : TailState A strategy hwin _tag) : Type _ :=
  PUnit ⊕
    (Σ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (move.memberController A false).Control)

noncomputable instance
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailLeftShared A strategy hwin tag
        state) := by
  classical
  infer_instance

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightShared A strategy hwin tag
      state :=
  match state.1.2.1 with
  | none => .inl PUnit.unit
  | some move => .inr ⟨move,
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController
        A strategy hwin state move false).initial⟩

noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftShared A strategy hwin tag
      state :=
  match state.1.2.2 with
  | none => .inl PUnit.unit
  | some move => .inr ⟨move,
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
        strategy hwin state move false).initial⟩

/-! ## Key-preserving blind evolution -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightSharedStep
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (member : Bool)
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailRightShared A strategy
      hwin tag state) (input : In₁) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightShared A strategy hwin tag
        state × Out₁ := by
  classical
  cases shared with
  | inl inert => exact (.inl inert, default)
  | inr installed =>
      let next := profiledRawJointRightPhysicalSiblingDeferredStep A
        installed.1 member installed.2 input
      exact (.inr ⟨installed.1, next.1⟩, next.2)

theorem profiledRawJointHybridShadowPhaseLiveTailRightSharedStep_laws
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy hwin
        tag state) := by
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
          [profiledRawJointHybridShadowPhaseLiveTailRightSharedStep] using
          congrArg
            (fun control ↦
              (Sum.inr ⟨installed.1, control⟩ :
                ProfiledRawJointHybridShadowPhaseLiveTailRightShared A strategy
                  hwin tag state))
            ((profiledRawJointRightPhysicalSiblingDeferredStep_laws A
              installed.1).stateEq installed.2 input)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (member : Bool)
    (shared : ProfiledRawJointHybridShadowPhaseLiveTailLeftShared A strategy
      hwin tag state) (input : In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftShared A strategy hwin tag
        state × Out₂ := by
  classical
  cases shared with
  | inl inert => exact (.inl inert, default)
  | inr installed =>
      let next := profiledRawJointLeftPhysicalSiblingDeferredStep A
        installed.1 member installed.2 input
      exact (.inr ⟨installed.1, next.1⟩, next.2)

theorem profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep_laws
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin
        tag state) := by
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
          [profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep] using
          congrArg
            (fun control ↦
              (Sum.inr ⟨installed.1, control⟩ :
                ProfiledRawJointHybridShadowPhaseLiveTailLeftShared A strategy
                  hwin tag state))
            ((profiledRawJointLeftPhysicalSiblingDeferredStep_laws A
              installed.1).stateEq installed.2 input)

/-- In a live fibre, the right shared step is the sender step of the
tail-decorated table. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRightSharedStep_installed
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (member : Bool) (control : (move.memberController A false).Control)
    (input : In₁) :
    profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy hwin
        tag state member (.inr ⟨move, control⟩) input =
      let controller :=
        profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController
          A strategy hwin state move member
      (.inr ⟨move, controller.step control input⟩,
        (controller.labelOf control).1 input) := by
  rfl

theorem profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep_installed
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (member : Bool) (control : (move.memberController A false).Control)
    (input : In₂) :
    profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin tag
        state member (.inr ⟨move, control⟩) input =
      let controller :=
        profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
          strategy hwin state move member
      (.inr ⟨move, controller.step control input⟩,
        (controller.labelOf control).1 input) := by
  rfl

/-! ## Sigma-packed dynamic tail keys -/

noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailRightDeferredControl
    (tag : Tag A strategy hwin) (Payload : Type p) :=
  FiniteAcknowledgedDelayedCarrier.KeyedDeferredMemberControl
    (TailState A strategy hwin tag)
    (ProfiledRawJointHybridShadowPhaseLiveTailRightShared A strategy hwin tag)
    Payload

noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailLeftDeferredControl
    (tag : Tag A strategy hwin) (Payload : Type p) :=
  FiniteAcknowledgedDelayedCarrier.KeyedDeferredMemberControl
    (TailState A strategy hwin tag)
    (ProfiledRawJointHybridShadowPhaseLiveTailLeftShared A strategy hwin tag)
    Payload

noncomputable instance (tag : Tag A strategy hwin)
    {Payload : Type p} [Fintype Payload] :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailRightDeferredControl A strategy
        hwin tag Payload) := by
  classical
  infer_instance

noncomputable instance (tag : Tag A strategy hwin)
    {Payload : Type p} [Fintype Payload] :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailLeftDeferredControl A strategy
        hwin tag Payload) := by
  classical
  infer_instance

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailRightDeferredNoRecv
    (tag : Tag A strategy hwin) {Payload : Type p} :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberNoRecv
    (Payload := Payload)
    (fun state ↦
      profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy hwin
        tag state)

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLeftDeferredNoRecv
    (tag : Tag A strategy hwin) {Payload : Type p} :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberNoRecv
    (Payload := Payload)
    (fun state ↦
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin
        tag state)

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailRightDeferredNoRecv_key
    (tag : Tag A strategy hwin) {Payload : Type p}
    (control :
      ProfiledRawJointHybridShadowPhaseLiveTailRightDeferredControl A strategy
        hwin tag Payload)
    (input : In₁) :
    (profiledRawJointHybridShadowPhaseLiveTailRightDeferredNoRecv A strategy
      hwin tag control input).1.1.1 = control.1.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailLeftDeferredNoRecv_key
    (tag : Tag A strategy hwin) {Payload : Type p}
    (control :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftDeferredControl A strategy
        hwin tag Payload)
    (input : In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailLeftDeferredNoRecv A strategy
      hwin tag control input).1.1.1 = control.1.1 :=
  rfl

theorem profiledRawJointHybridShadowPhaseLiveTailRightDeferredStep_laws
    (tag : Tag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
        (fun state ↦
          profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy
            hwin tag state)) := by
  exact FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep_laws _
    (fun state ↦
      profiledRawJointHybridShadowPhaseLiveTailRightSharedStep_laws A strategy
        hwin tag state)

theorem profiledRawJointHybridShadowPhaseLiveTailLeftDeferredStep_laws
    (tag : Tag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
        (fun state ↦
          profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy
            hwin tag state)) := by
  exact FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep_laws _
    (fun state ↦
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep_laws A strategy
        hwin tag state)

/-! ## Exact fresh forks at retained successor keys -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightForkAt
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    {Payload : Type p} (payload : Payload) :
    FiniteDelayedFork
      (ProfiledRawJointHybridShadowPhaseLiveTailRightDeferredControl A strategy
        hwin tag Payload) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork state
    (profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial A strategy hwin
      tag state)
    payload

noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftForkAt
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    {Payload : Type p} (payload : Payload) :
    FiniteDelayedFork
      (ProfiledRawJointHybridShadowPhaseLiveTailLeftDeferredControl A strategy
        hwin tag Payload) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork state
    (profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial A strategy hwin
      tag state)
    payload

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailRightForkAt_key
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    {Payload : Type p} (payload : Payload) (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailRightForkAt A strategy hwin tag
      state payload).candidate member).1.1 = state := by
  cases member <;> rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailLeftForkAt_key
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    {Payload : Type p} (payload : Payload) (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailLeftForkAt A strategy hwin tag
      state payload).candidate member).1.1 = state := by
  cases member <;> rfl

theorem profiledRawJointHybridShadowPhaseLiveTailRightForkAt_installed
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) {Payload : Type p}
    (payload : Payload) (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailRightForkAt A strategy hwin tag
      state payload).candidate member).1.2.2 =
      .inr ⟨move,
        (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController
          A strategy hwin state move false).initial⟩ := by
  cases member <;>
    simp [profiledRawJointHybridShadowPhaseLiveTailRightForkAt,
      profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial, hmove,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork,
      FiniteDelayedFork.candidate]

theorem profiledRawJointHybridShadowPhaseLiveTailLeftForkAt_installed
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) {Payload : Type p}
    (payload : Payload) (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailLeftForkAt A strategy hwin tag
      state payload).candidate member).1.2.2 =
      .inr ⟨move,
        (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
          strategy hwin state move false).initial⟩ := by
  cases member <;>
    simp [profiledRawJointHybridShadowPhaseLiveTailLeftForkAt,
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial, hmove,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork,
      FiniteDelayedFork.candidate]

end

end DetParityAutomaton

end DistributedSynthesis
