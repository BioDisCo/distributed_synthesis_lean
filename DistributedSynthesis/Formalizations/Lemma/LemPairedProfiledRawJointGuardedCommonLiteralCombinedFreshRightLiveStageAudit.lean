/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveOneHandler
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveTwoHandler
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedStagedFront

/-!
# Right live-stage audit for the combined fresh control

This file tests the current combined pending maps at the first physical
right reversal.  The honest finite data contain a live right receiver stage
at process one and its synchronized right sender at process two.  The checked
staged-reversal theorem says that the physical event must execute one matched
recurrent step and enter the two recurrent endpoint controls.

The current generic pending maps instead keep both endpoints in the pending
summand.  The constructor mismatch is proved below independently of any
possible output equality.  The remaining output comparison is named
explicitly: it compares the current left-table projections with the right
live-stage projections and is not supplied by the existing seam laws.

This is an interface audit, not a counterexample to finite-state synthesis.
The local freshness phase already tells each endpoint whether its current
receive/no-receive event is a same-side continuation or a switch.  A repaired
handler may dispatch on that stored local phase; it still needs no graph,
orientation, hierarchy side, leader bit, history, or view.
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

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev FreshTwo :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
    initial

private abbrev LeftSender (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy hwin
    package

private abbrev RightSender (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev RightReceiver (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev RightStage (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

private abbrev LeftStage (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

private abbrev RightOne (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
    package

private abbrev RightTwo (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
    package

private abbrev OneShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePayload (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy hwin
    package

private abbrev TwoPayload (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy hwin
    package

private abbrev OnePending (package : Package A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package) (OnePayload A strategy hwin package)

private abbrev TwoPending (package : Package A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package) (TwoPayload A strategy hwin package)

private abbrev OneControl (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package (RightOne A strategy hwin package)

private abbrev TwoControl (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package (RightTwo A strategy hwin package)

/-! ## A synchronized live right-stage test state -/

/-- Put the same live right receiver in both proof-side member slots.  This
removes member selection from the audit: whichever old member is selected,
the locally stored right stage is exactly `receiver`. -/
def literalCombinedFreshRightAuditOneShared
    (package : Package A strategy hwin initial)
    (fresh : FreshOne A strategy hwin (initial := initial))
    (leftSender : LeftSender A strategy hwin package)
    (receiver : RightReceiver A strategy hwin package) :
    OneShared A strategy hwin package :=
  (fresh, leftSender, ⟨receiver, receiver⟩)

/-- Install the synchronized right sender in process two.  Its left receiver
fork is retained only because the old combined carrier stores both seam
orientations simultaneously. -/
def literalCombinedFreshRightAuditTwoShared
    (package : Package A strategy hwin initial)
    (fresh : FreshTwo A strategy hwin (initial := initial))
    (sender : RightSender A strategy hwin package)
    (leftFork : FiniteDelayedFork (LeftReceiver A strategy hwin package)) :
    TwoShared A strategy hwin package :=
  (fresh, sender, leftFork)

def literalCombinedFreshRightAuditOnePending
    (package : Package A strategy hwin initial)
    (member : Bool) (fresh : FreshOne A strategy hwin (initial := initial))
    (leftSender : LeftSender A strategy hwin package)
    (receiver : RightReceiver A strategy hwin package)
    (payload : OnePayload A strategy hwin package) :
    OnePending A strategy hwin package :=
  (member,
    package.literalCombinedFreshRightAuditOneShared A strategy hwin fresh
      leftSender receiver,
    payload)

def literalCombinedFreshRightAuditTwoPending
    (package : Package A strategy hwin initial)
    (member : Bool) (fresh : FreshTwo A strategy hwin (initial := initial))
    (sender : RightSender A strategy hwin package)
    (leftFork : FiniteDelayedFork (LeftReceiver A strategy hwin package))
    (stage : RightStage A strategy hwin package) :
    TwoPending A strategy hwin package :=
  (member,
    package.literalCombinedFreshRightAuditTwoShared A strategy hwin fresh
      sender leftFork,
    (some stage : TwoPayload A strategy hwin package))

/-! ## The current pending maps -/

/-- The current generic no-receive map on process one.  The recurrent step is
irrelevant on the pending test state but is kept as a parameter so this is the
actual sum-level executable map. -/
noncomputable def literalCombinedFreshRightAuditCurrentNoRecvOne
    (package : Package A strategy hwin initial)
    (recurrentStep : RightOne A strategy hwin package → In₁ →
      RightOne A strategy hwin package × Out₁)
    (pending : OnePending A strategy hwin package) (input : In₁) :
    OneControl A strategy hwin package × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (package.literalCombinedFreshOnePendingStep A strategy hwin)
    recurrentStep (.inl pending) input

/-- The current pending/pending process-two receive, projected to its ordinary
open continuation. -/
noncomputable def literalCombinedFreshRightAuditCurrentRecvTwo
    (package : Package A strategy hwin initial)
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    TwoControl A strategy hwin package × Out₂ :=
  let result := package.literalCombinedFreshPendingRecvForkTwo A strategy hwin
    (RightTwo A strategy hwin package) two own one delivered
  (result.1.openControl, result.2)

/-! ## What the audit proves -/

/-- The exact staged maps themselves form the checked recurrent pair.  This
is the semantic reference used by the audit. -/
theorem literalCombinedFreshRightAudit_exact_reference
    (package : Package A strategy hwin initial)
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package)
    (stage : RightStage A strategy hwin package)
    (hstage : receiver.2.2.2 = some stage)
    (input : In₁ × In₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    package.literalRightSeamStagedReversalNoRecvOne A strategy hwin receiver
        input.1 =
        ((package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
          input.1).2,
          (package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
            input.1).1) ∧
      package.literalRightSeamStagedReversalRecvTwo A strategy hwin sender
          input.2 receiver input.1 =
        ((package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
          input.2 matched.1 input.1).2,
          (package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
            input.2 matched.1 input.1).1) :=
  package.literalRightSeamStagedReversal_exact_pair A strategy hwin receiver
    sender stage hstage input

/-- Regardless of the live stage, the current process-one pending map remains
in the pending summand. -/
@[simp] theorem literalCombinedFreshRightAuditCurrentNoRecvOne_is_pending
    (package : Package A strategy hwin initial)
    (recurrentStep : RightOne A strategy hwin package → In₁ →
      RightOne A strategy hwin package × Out₁)
    (pending : OnePending A strategy hwin package) (input : In₁) :
    (package.literalCombinedFreshRightAuditCurrentNoRecvOne A strategy hwin
      recurrentStep pending input).1 =
      .inl
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (package.literalCombinedFreshOnePendingStep A strategy hwin)
          pending input).1 :=
  rfl

/-- The current process-two pending receive likewise installs another pending
fork instead of the live right recurrent receiver. -/
theorem literalCombinedFreshRightAuditCurrentRecvTwo_is_pending
    (package : Package A strategy hwin initial)
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    ∃ pending : TwoPending A strategy hwin package,
      (package.literalCombinedFreshRightAuditCurrentRecvTwo A strategy hwin
        two own one delivered).1 = (.inl pending : TwoControl A strategy hwin
          package) := by
  refine ⟨(false,
    package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1 own
      one.2.1 delivered,
    (none : TwoPayload A strategy hwin package)), ?_⟩
  rfl

/-- Full agreement with the checked right recurrent process-one transition is
impossible already at the sum constructor, independently of the two physical
outputs. -/
theorem literalCombinedFreshRightAuditCurrentNoRecvOne_ne_exact
    (package : Package A strategy hwin initial)
    (recurrentStep : RightOne A strategy hwin package → In₁ →
      RightOne A strategy hwin package × Out₁)
    (pending : OnePending A strategy hwin package)
    (receiver : RightReceiver A strategy hwin package) (input : In₁) :
    package.literalCombinedFreshRightAuditCurrentNoRecvOne A strategy hwin
        recurrentStep pending input ≠
      (.inr
          (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
            receiver input).2,
        (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
          receiver input).1) := by
  intro h
  have := congrArg (fun result ↦ result.1) h
  change Sum.inl _ = Sum.inr _ at this
  cases this

/-- The mirror endpoint has the same constructor mismatch on the same right
reversal. -/
theorem literalCombinedFreshRightAuditCurrentRecvTwo_ne_exact
    (package : Package A strategy hwin initial)
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁)
    (sender : RightSender A strategy hwin package)
    (receiver : RightReceiver A strategy hwin package) :
    package.literalCombinedFreshRightAuditCurrentRecvTwo A strategy hwin two
        own one delivered ≠
      (.inr
          (package.literalRightSeamStagedReversalRecvTwo A strategy hwin
            sender own receiver delivered).2,
        (package.literalRightSeamStagedReversalRecvTwo A strategy hwin sender
          own receiver delivered).1) := by
  intro h
  rcases package.literalCombinedFreshRightAuditCurrentRecvTwo_is_pending A
    strategy hwin two own one delivered with ⟨pending, hpending⟩
  have hcontrol :
      (package.literalCombinedFreshRightAuditCurrentRecvTwo A strategy hwin
        two own one delivered).1 =
        .inr (package.literalRightSeamStagedReversalRecvTwo A strategy hwin
          sender own receiver delivered).2 := by
    simpa only [Prod.fst] using congrArg (fun result ↦ result.1) h
  rw [hpending] at hcontrol
  cases hcontrol

/-- The exact residual left after exposing the constructor mismatch.  These
are the two additional physical-output equations a phase-unaware pending map
would need in order to mimic the live right reversal. -/
def LiteralCombinedFreshRightLiveStageOutputCompatible
    (package : Package A strategy hwin initial)
    (recurrentStep : RightOne A strategy hwin package → In₁ →
      RightOne A strategy hwin package × Out₁)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package)
    (input : In₁ × In₂) : Prop :=
  (package.literalCombinedFreshRightAuditCurrentNoRecvOne A strategy hwin
      recurrentStep one input.1).2 =
      (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin receiver
        input.1).1 ∧
    (package.literalCombinedFreshRightAuditCurrentRecvTwo A strategy hwin two
      input.2 one input.1).2 =
      (package.literalRightSeamStagedReversalRecvTwo A strategy hwin sender
        input.2 receiver input.1).1

/-- Even assuming the residual output equations, the current pair cannot be
the exact live-stage pair because both current controls remain pending. -/
theorem literalCombinedFreshRightAudit_not_exact_pair
    (package : Package A strategy hwin initial)
    (recurrentStep : RightOne A strategy hwin package → In₁ →
      RightOne A strategy hwin package × Out₁)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package)
    (input : In₁ × In₂) :
    ¬ (package.literalCombinedFreshRightAuditCurrentNoRecvOne A strategy
          hwin recurrentStep one input.1 =
          (.inr
              (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
                receiver input.1).2,
            (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
              receiver input.1).1) ∧
        package.literalCombinedFreshRightAuditCurrentRecvTwo A strategy hwin
          two input.2 one input.1 =
          (.inr
              (package.literalRightSeamStagedReversalRecvTwo A strategy hwin
                sender input.2 receiver input.1).2,
            (package.literalRightSeamStagedReversalRecvTwo A strategy hwin
              sender input.2 receiver input.1).1)) := by
  intro h
  exact package.literalCombinedFreshRightAuditCurrentNoRecvOne_ne_exact A
    strategy hwin recurrentStep one receiver input.1 h.1

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
