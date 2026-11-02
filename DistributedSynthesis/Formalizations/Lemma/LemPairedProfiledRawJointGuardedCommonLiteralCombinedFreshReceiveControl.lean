/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralLeftReceiverBranchSelection
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredFreshReceive
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessCarrier

/-!
# Combined finite control installed by one fresh receive

A fresh occurrence has two independent roles.  The blind endpoint must keep
the false/true members of one shared sender table, while its local control
must also retain both possible receiver roots for the opposite seam.  Those
receiver roots have the same fresh key but intentionally different rows and
anchors: strict/open is `first,false`, and simultaneous/closed is
`both,true`.

This file gives the concrete finite carrier for that information.  Process
one stores its leader-free freshness coordinate, the left-seam sender, and
both right-seam receiver roots; process two stores the exact mirror.  The
freshness phase bit is essential at a strict-side switch: it says whether the
endpoint's own finite policy copy or the delivered partner copy is current,
without revealing which endpoint is the strict leader.  The receiver states
already contain their own latest-stage options, so the only separate payload
is the stage option belonging to the blind sender.  No stage is duplicated.

Recurrent controls remain parameters here.  The definitions therefore feed
the concrete endpoint handlers without prematurely choosing their recurrent
product.  No executable map receives a graph, orientation, hierarchy side,
leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y s r₁ r₂

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

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev State :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev RightShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev LeftShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy hwin
    package

private abbrev RightStage (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

private abbrev LeftStage (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

private abbrev RightReceiver (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev FreshTwo :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
    initial

/-! ## Minimal finite shared states -/

/-- Process one's fresh shared state: leader-free freshness, the left blind
sender, and the two right receiver branches at the same occurrence. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared
    (package : Package A strategy hwin initial) :=
  FreshOne A strategy hwin (initial := initial) ×
    (LeftShared A strategy hwin package × FiniteDelayedFork
      (RightReceiver A strategy hwin package))

/-- Process two's exact mirror. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared
    (package : Package A strategy hwin initial) :=
  FreshTwo A strategy hwin (initial := initial) ×
    (RightShared A strategy hwin package × FiniteDelayedFork
      (LeftReceiver A strategy hwin package))

/-- Only the blind left sender's latest exact stage is not already stored in
process one's receiver pair. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload
    (package : Package A strategy hwin initial) :=
  Option (LeftStage A strategy hwin package)

/-- Process-two mirror payload. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload
    (package : Package A strategy hwin initial) :=
  Option (RightStage A strategy hwin package)

noncomputable instance literalCombinedFreshOneSharedFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy
        hwin package) := by
  classical
  infer_instance

noncomputable instance literalCombinedFreshTwoSharedFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy
        hwin package) := by
  classical
  infer_instance

noncomputable instance literalCombinedFreshOnePayloadFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
        hwin package) := by
  classical
  infer_instance

noncomputable instance literalCombinedFreshTwoPayloadFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
        hwin package) := by
  classical
  infer_instance

/-! ## Same-key fresh constructors -/

/-- Install process one's local freshness state, left sender, and both right
receiver interpretations at one exact seam key. -/
noncomputable def literalCrossCombinedFreshOneSharedAt
    (package : Package A strategy hwin initial)
    (fresh : FreshOne A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) :
    ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
      package :=
  (fresh,
    package.literalLeftSeamStagedSenderInitial A strategy hwin key,
    ⟨package.literalRightSeamStagedReceiverInitial A strategy hwin key
        .first false,
      package.literalRightSeamStagedReceiverInitial A strategy hwin key .both
        true⟩)

/-- Process-two mirror at an explicitly supplied freshness state and key. -/
noncomputable def literalCrossCombinedFreshTwoSharedAt
    (package : Package A strategy hwin initial)
    (fresh : FreshTwo A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) :
    ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
      package :=
  (fresh,
    package.literalRightSeamStagedSenderInitial A strategy hwin key,
    ⟨package.literalLeftSeamStagedReceiverInitial A strategy hwin key
        .first false,
      package.literalLeftSeamStagedReceiverInitial A strategy hwin key .both
        true⟩)

/-- The simultaneous fresh process-one shared value.  Its freshness copy is
the literal child state, whereas the seam key retains the predecessor and
input selecting that child. -/
noncomputable def successorLiteralCrossCombinedFreshOneShared
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
      package :=
  let source := package.policy.successor state incoming
  let key : Key A strategy hwin package := (source, blockInput)
  let fresh : FreshOne A strategy hwin (initial := initial) :=
    (package.policy.successor source blockInput, true)
  package.literalCrossCombinedFreshOneSharedAt A strategy hwin fresh key

/-- Fresh process-two simultaneous mirror. -/
noncomputable def successorLiteralCrossCombinedFreshTwoShared
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
      package :=
  let source := package.policy.successor state incoming
  let key : Key A strategy hwin package := (source, blockInput)
  let fresh : FreshTwo A strategy hwin (initial := initial) :=
    (package.policy.successor source blockInput, false)
  package.literalCrossCombinedFreshTwoSharedAt A strategy hwin fresh key

@[simp] theorem successorLiteralCrossCombinedFreshOneShared_freshness
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshOneShared A strategy hwin state
      incoming blockInput).1 =
      (package.policy.successor
        (package.policy.successor state incoming) blockInput, true) :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshTwoShared_freshness
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin state
      incoming blockInput).1 =
      (package.policy.successor
        (package.policy.successor state incoming) blockInput, false) :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshOneShared_sender_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshOneShared A strategy hwin state
      incoming blockInput).2.1.1 =
      package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
        blockInput :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshTwoShared_sender_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin state
      incoming blockInput).2.1.1 =
      package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
        blockInput :=
  rfl

/-- Select the right receiver interpretation stored by process one. -/
def literalCombinedFreshOneReceiver
    (package : Package A strategy hwin initial)
    (member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy
        hwin package) : RightReceiver A strategy hwin package :=
  shared.2.2.candidate member

/-- Select the left receiver interpretation stored by process two. -/
def literalCombinedFreshTwoReceiver
    (package : Package A strategy hwin initial)
    (member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy
        hwin package) : LeftReceiver A strategy hwin package :=
  shared.2.2.candidate member

@[simp] theorem successorLiteralCrossCombinedFreshOneReceiver_false
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.successorLiteralCrossCombinedFreshOneShared A strategy hwin
          state incoming blockInput) =
      package.literalRightSeamStrictOpenReceiverRoot A strategy hwin state
        incoming blockInput :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshOneReceiver_true
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    package.literalCombinedFreshOneReceiver A strategy hwin true
        (package.successorLiteralCrossCombinedFreshOneShared A strategy hwin
          state incoming blockInput) =
      package.literalRightSeamClosedReceiverRoot A strategy hwin state incoming
        blockInput :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshTwoReceiver_false
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin
          state incoming blockInput) =
      package.literalLeftSeamStrictOpenReceiverRoot A strategy hwin state
        incoming blockInput :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshTwoReceiver_true
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    package.literalCombinedFreshTwoReceiver A strategy hwin true
        (package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin
          state incoming blockInput) =
      package.literalLeftSeamClosedReceiverRoot A strategy hwin state incoming
        blockInput :=
  rfl

/-! ## Bridge to the existing operational branch records -/

/-- The strict-right operational poststate is definitionally the false
receiver selected from process one's combined shared value. -/
@[simp] theorem successorLiteralCrossStrictOpenReceive_receiver_eq_combined
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossStrictOpenReceive A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor).2 =
      package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.successorLiteralCrossCombinedFreshOneShared A strategy hwin
          state incoming blockInput) :=
  rfl

/-- The simultaneous right poststate is the true receiver stored beside it. -/
@[simp] theorem successorLiteralCrossClosedReceive_receiver_eq_combined
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossClosedReceive A strategy hwin state incoming
      blockInput oldRightAnchor oldLeftAnchor).2 =
      package.literalCombinedFreshOneReceiver A strategy hwin true
        (package.successorLiteralCrossCombinedFreshOneShared A strategy hwin
          state incoming blockInput) :=
  rfl

/-- Mirror strict poststate bridge. -/
@[simp] theorem successorLiteralCrossLeftStrictOpenReceive_receiver_eq_combined
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossLeftStrictOpenReceive A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor).2 =
      package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin
          state incoming blockInput) :=
  rfl

/-- Mirror simultaneous poststate bridge. -/
@[simp] theorem successorLiteralCrossLeftClosedReceive_receiver_eq_combined
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossLeftClosedReceive A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor).2 =
      package.literalCombinedFreshTwoReceiver A strategy hwin true
        (package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin
          state incoming blockInput) :=
  rfl

/-! ## Blind shared transitions -/

/-- Process one's no-receive transition advances the left-seam sender and
retains both right receiver branches.  It does not inspect the unresolved
member. -/
noncomputable def literalCombinedFreshOnePendingStep
    (package : Package A strategy hwin initial)
    (_member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy
        hwin package)
    (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
        package × Out₁ :=
  let nextFresh := decoratedFreshnessNoRecvOne A strategy hwin shared.1 input
  let nextSender := package.literalLeftSeamStagedSenderNoRecv A strategy hwin
    shared.2.1 input
  ((nextFresh, nextSender.2, shared.2.2), nextSender.1)

/-- Process-two mirror no-receive transition. -/
noncomputable def literalCombinedFreshTwoPendingStep
    (package : Package A strategy hwin initial)
    (_member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy
        hwin package)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
        package × Out₂ :=
  let nextFresh := decoratedFreshnessNoRecvTwo A strategy hwin shared.1 input
  let nextSender := package.literalRightSeamStagedSenderNoRecv A strategy hwin
    shared.2.1 input
  ((nextFresh, nextSender.2, shared.2.2), nextSender.1)

/-- Member-independence is definitional for process one. -/
theorem literalCombinedFreshOnePendingStepLaws
    (package : Package A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (package.literalCombinedFreshOnePendingStep A strategy hwin) where
  outputEq := by
    intro shared input
    rfl
  stateEq := by
    intro shared input
    rfl

/-- Member-independence is definitional for process two. -/
theorem literalCombinedFreshTwoPendingStepLaws
    (package : Package A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) where
  outputEq := by
    intro shared input
    rfl
  stateEq := by
    intro shared input
    rfl

@[simp] theorem literalCombinedFreshOnePendingStep_receivers
    (package : Package A strategy hwin initial)
    (member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy
        hwin package)
    (input : In₁) :
    (package.literalCombinedFreshOnePendingStep A strategy hwin member shared
      input).1.2.2 = shared.2.2 :=
  rfl

@[simp] theorem literalCombinedFreshTwoPendingStep_receivers
    (package : Package A strategy hwin initial)
    (member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy
        hwin package)
    (input : In₂) :
    (package.literalCombinedFreshTwoPendingStep A strategy hwin member shared
      input).1.2.2 = shared.2.2 :=
  rfl

@[simp] theorem literalCombinedFreshOnePendingStep_freshness
    (package : Package A strategy hwin initial)
    (member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy
        hwin package)
    (input : In₁) :
    (package.literalCombinedFreshOnePendingStep A strategy hwin member shared
      input).1.1 =
      decoratedFreshnessNoRecvOne A strategy hwin shared.1 input :=
  rfl

@[simp] theorem literalCombinedFreshTwoPendingStep_freshness
    (package : Package A strategy hwin initial)
    (member : Bool)
    (shared :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy
        hwin package)
    (input : In₂) :
    (package.literalCombinedFreshTwoPendingStep A strategy hwin member shared
      input).1.1 =
      decoratedFreshnessNoRecvTwo A strategy hwin shared.1 input :=
  rfl

/-! ## Pending/recurrent endpoint controls and canonical fresh forks -/

/-- Unified process-one control, parametrized only by its later recurrent
phase. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl
    (package : Package A strategy hwin initial) (RecurrentOne : Type r₁) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
      package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)
    RecurrentOne

/-- Unified process-two mirror control. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl
    (package : Package A strategy hwin initial) (RecurrentTwo : Type r₂) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
      package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)
    RecurrentTwo

noncomputable instance literalCombinedFreshOneControlFintype
    (package : Package A strategy hwin initial) (RecurrentOne : Type r₁)
    [Fintype RecurrentOne] :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy
        hwin package RecurrentOne) := by
  classical
  infer_instance

noncomputable instance literalCombinedFreshTwoControlFintype
    (package : Package A strategy hwin initial) (RecurrentTwo : Type r₂)
    [Fintype RecurrentTwo] :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy
        hwin package RecurrentTwo) := by
  classical
  infer_instance

/-- Install process one's new unresolved occurrence. -/
noncomputable def successorLiteralCrossCombinedFreshOneFork
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy
        hwin package RecurrentOne) :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
    (Recurrent := RecurrentOne)
    (package.successorLiteralCrossCombinedFreshOneShared A strategy hwin state
      incoming blockInput)
    (none :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
        hwin package)

/-- Process-two mirror fork. -/
noncomputable def successorLiteralCrossCombinedFreshTwoFork
    (package : Package A strategy hwin initial)
    (RecurrentTwo : Type r₂)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy
        hwin package RecurrentTwo) :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
    (Recurrent := RecurrentTwo)
    (package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin state
      incoming blockInput)
    (none :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
        hwin package)

@[simp] theorem successorLiteralCrossCombinedFreshOneFork_open
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshOneFork A strategy hwin
      RecurrentOne state incoming blockInput).openControl =
      (.inl
        (false,
          package.successorLiteralCrossCombinedFreshOneShared A strategy hwin
            state incoming blockInput,
          (none :
            ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
              strategy hwin package)) :
        ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy
          hwin package RecurrentOne) :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshOneFork_closed
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshOneFork A strategy hwin
      RecurrentOne state incoming blockInput).closedControl =
      (.inl
        (true,
          package.successorLiteralCrossCombinedFreshOneShared A strategy hwin
            state incoming blockInput,
          (none :
            ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
              strategy hwin package)) :
        ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy
          hwin package RecurrentOne) :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshTwoFork_open
    (package : Package A strategy hwin initial)
    (RecurrentTwo : Type r₂)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshTwoFork A strategy hwin
      RecurrentTwo state incoming blockInput).openControl =
      (.inl
        (false,
          package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin
            state incoming blockInput,
          (none :
            ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
              strategy hwin package)) :
        ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy
          hwin package RecurrentTwo) :=
  rfl

@[simp] theorem successorLiteralCrossCombinedFreshTwoFork_closed
    (package : Package A strategy hwin initial)
    (RecurrentTwo : Type r₂)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossCombinedFreshTwoFork A strategy hwin
      RecurrentTwo state incoming blockInput).closedControl =
      (.inl
        (true,
          package.successorLiteralCrossCombinedFreshTwoShared A strategy hwin
            state incoming blockInput,
          (none :
            ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
              strategy hwin package)) :
        ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy
          hwin package RecurrentTwo) :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
