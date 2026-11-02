/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveControl
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessReceiveSource

/-!
# Total process-two receive handler for the combined fresh control

For a pending/pending receive, process two resolves its old member only to
choose the old left-seam receiver and its physical output.  The new occurrence
is indexed instead by the leader-free freshness carrier: the receiver uses
its own current finite policy copy or the delivered partner copy according to
its local phase bit, advances that copy exactly once, and installs one new
false/true pending fork.

The pending/recurrent and recurrent cases are supplied as endpoint-local
handler parameters.  They keep the definition total without pretending that
a recurrent partner carries the fresh pending coordinate.  No executable map
receives a graph, orientation, leader bit, history, or semantic view.
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

private abbrev OneControl
    (package : Package A strategy hwin initial) (RecurrentOne : Type r₁) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package RecurrentOne

private abbrev TwoControl
    (package : Package A strategy hwin initial) (RecurrentTwo : Type r₂) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package RecurrentTwo

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

/-! ## Old selected output -/

/-- The old seam key stored in process two's right sender coordinate.  It is
useful for the old receiver invariant, but it is deliberately *not* used as
the parent of a fresh occurrence after an alternating hierarchy switch. -/
def literalCombinedFreshTwoStoredKey
    (package : Package A strategy hwin initial)
    (shared : TwoShared A strategy hwin package) :
    Key A strategy hwin package :=
  shared.2.1.1

/-- Select and advance the old left receiver, then read its actual
`informedBoth` coordinate.  The old member chooses which proof-side monitor
is physically current. -/
noncomputable def literalCombinedFreshTwoPendingReceiveOutput
    (package : Package A strategy hwin initial)
    (member : Bool) (shared : TwoShared A strategy hwin package)
    (own : In₂) (delivered : In₁) : Out₂ :=
  let receiver := package.literalCombinedFreshTwoReceiver A strategy hwin
    member shared
  let result := package.literalLeftSeamStagedReceiverRecv A strategy hwin
    receiver own delivered
  if member then
    profiledRawJointTargetRightReceiverBothPhysicalOutput result.1.2.2
  else
    profiledRawJointTargetRightReceiverBothPhysicalOutput result.1.2.1

@[simp] theorem literalCombinedFreshTwoPendingReceiveOutput_false
    (package : Package A strategy hwin initial)
    (shared : TwoShared A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    package.literalCombinedFreshTwoPendingReceiveOutput A strategy hwin false
        shared own delivered =
      profiledRawJointTargetRightReceiverBothPhysicalOutput
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin
          (package.literalCombinedFreshTwoReceiver A strategy hwin false
            shared) own delivered).1.2.1 :=
  rfl

@[simp] theorem literalCombinedFreshTwoPendingReceiveOutput_true
    (package : Package A strategy hwin initial)
    (shared : TwoShared A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    package.literalCombinedFreshTwoPendingReceiveOutput A strategy hwin true
        shared own delivered =
      profiledRawJointTargetRightReceiverBothPhysicalOutput
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin
          (package.literalCombinedFreshTwoReceiver A strategy hwin true
            shared) own delivered).1.2.2 :=
  rfl

/-! ## Leader-free source and fresh shared value -/

/-- The local finite source used by process two at a receive.  The phase is
read from its own stored freshness coordinate; the alternative copy is in the
delivered process-one control. -/
def literalCombinedFreshTwoReceiveSource
    (package : Package A strategy hwin initial)
    (twoShared : TwoShared A strategy hwin package)
    (oneShared : OneShared A strategy hwin package) :
    State A strategy hwin (initial := initial) :=
  decoratedFreshnessRecvTwoSource A strategy hwin twoShared.1 oneShared.1

/-- The new process-two shared control.  Its key retains the selected source
and current block input, while its freshness coordinate is exactly the one
successor of that source.  Keeping these distinct prevents a double advance. -/
noncomputable def literalCombinedFreshTwoReceiveShared
    (package : Package A strategy hwin initial)
    (twoShared : TwoShared A strategy hwin package) (own : In₂)
    (oneShared : OneShared A strategy hwin package) (delivered : In₁) :
    TwoShared A strategy hwin package :=
  let source := package.literalCombinedFreshTwoReceiveSource A strategy hwin
    twoShared oneShared
  let fresh := decoratedFreshnessRecvTwo A strategy hwin package twoShared.1
    own oneShared.1 delivered
  package.literalCrossCombinedFreshTwoSharedAt A strategy hwin fresh
    (source, (delivered, own))

@[simp] theorem literalCombinedFreshTwoReceiveShared_freshness
    (package : Package A strategy hwin initial)
    (twoShared : TwoShared A strategy hwin package) (own : In₂)
    (oneShared : OneShared A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshTwoReceiveShared A strategy hwin twoShared
      own oneShared delivered).1 =
      decoratedFreshnessRecvTwo A strategy hwin package twoShared.1 own
        oneShared.1 delivered :=
  rfl

@[simp] theorem literalCombinedFreshTwoReceiveShared_sender_key
    (package : Package A strategy hwin initial)
    (twoShared : TwoShared A strategy hwin package) (own : In₂)
    (oneShared : OneShared A strategy hwin package) (delivered : In₁) :
    (package.literalCombinedFreshTwoReceiveShared A strategy hwin twoShared
      own oneShared delivered).2.1.1 =
      (package.literalCombinedFreshTwoReceiveSource A strategy hwin twoShared
        oneShared, (delivered, own)) :=
  rfl

/-- The dangerous `left,left,right` switch, stated at the concrete handler
boundary.  Even when the two seam tables were built from arbitrary old keys,
the new process-two sender key takes its parent from process one's delivered
freshness copy after the two left rounds. -/
theorem literalCombinedFreshTwo_left_left_right_sender_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input₀ input₁ input₂ : In₁ × In₂)
    (oneOldKey twoOldKey : Key A strategy hwin package) :
    let start := decoratedFreshnessBothInitial A strategy hwin state
    let after₀ := decoratedFreshnessLocalStep A strategy hwin package
      start.1 start.2 input₀ .left
    let after₁ := decoratedFreshnessLocalStep A strategy hwin package
      after₀.1 after₀.2 input₁ .left
    let oneShared := package.literalCrossCombinedFreshOneSharedAt A strategy
      hwin after₁.1 oneOldKey
    let twoShared := package.literalCrossCombinedFreshTwoSharedAt A strategy
      hwin after₁.2 twoOldKey
    (package.literalCombinedFreshTwoReceiveShared A strategy hwin twoShared
      input₂.2 oneShared input₂.1).2.1.1 = (after₁.1.1, input₂) := by
  rfl

/-! ## Pending and total receive forks -/

/-- Resolve the old pending member for the current output, and install the
next occurrence-specific pending fork from both locally available freshness
coordinates. -/
noncomputable def literalCombinedFreshPendingRecvForkTwo
    (package : Package A strategy hwin initial)
    (RecurrentTwo : Type r₂)
    (twoPending : TwoPending A strategy hwin package) (own : In₂)
    (onePending : OnePending A strategy hwin package) (delivered : In₁) :
    FiniteDelayedFork (TwoControl A strategy hwin package RecurrentTwo) ×
      Out₂ :=
  let nextShared := package.literalCombinedFreshTwoReceiveShared A strategy
    hwin twoPending.2.1 own onePending.2.1 delivered
  (FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
      (Recurrent := RecurrentTwo) nextShared
      (none : TwoPayload A strategy hwin package),
    package.literalCombinedFreshTwoPendingReceiveOutput A strategy hwin
      twoPending.1 twoPending.2.1 own delivered)

/-- Handler for a pending local state whose delivered partner is already
recurrent.  Such a partner does not carry the fresh pending coordinate, so
the later recurrent product supplies this mixed transition explicitly. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂) :=
  TwoPending A strategy hwin package → In₂ → RecurrentOne → In₁ →
    FiniteDelayedFork (TwoControl A strategy hwin package RecurrentTwo) × Out₂

/-- Handler for a recurrent local state. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂) :=
  RecurrentTwo → In₂ → OneControl A strategy hwin package RecurrentOne → In₁ →
    FiniteDelayedFork (TwoControl A strategy hwin package RecurrentTwo) × Out₂

/-- Total receive-fork handler.  The exact fresh construction is used only
when both endpoints still carry the same pending occurrence. -/
noncomputable def literalCombinedFreshRecvForkTwo
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (pendingMixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
        A strategy hwin package RecurrentOne RecurrentTwo)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo A
        strategy hwin package RecurrentOne RecurrentTwo)
    (two : TwoControl A strategy hwin package RecurrentTwo) (own : In₂)
    (one : OneControl A strategy hwin package RecurrentOne)
    (delivered : In₁) :
    FiniteDelayedFork (TwoControl A strategy hwin package RecurrentTwo) ×
      Out₂ :=
  match two, one with
  | .inl twoPending, .inl onePending =>
      package.literalCombinedFreshPendingRecvForkTwo A strategy hwin
        RecurrentTwo twoPending own onePending delivered
  | .inl twoPending, .inr oneRecurrent =>
      pendingMixedRecv twoPending own oneRecurrent delivered
  | .inr twoRecurrent, oneControl =>
      recurrentRecv twoRecurrent own oneControl delivered

/-- Ordinary receive selects the open (false) continuation of the new fork. -/
noncomputable def literalCombinedFreshOpenRecvTwo
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (pendingMixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
        A strategy hwin package RecurrentOne RecurrentTwo)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo A
        strategy hwin package RecurrentOne RecurrentTwo)
    (two : TwoControl A strategy hwin package RecurrentTwo) (own : In₂)
    (one : OneControl A strategy hwin package RecurrentOne)
    (delivered : In₁) :
    TwoControl A strategy hwin package RecurrentTwo × Out₂ :=
  let result := package.literalCombinedFreshRecvForkTwo A strategy hwin
    RecurrentOne RecurrentTwo pendingMixedRecv recurrentRecv two own one
      delivered
  (result.1.openControl, result.2)

/-- Exact-close projection paired later with process one's closed control. -/
noncomputable def literalCombinedFreshClosedRecvTwo
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (pendingMixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
        A strategy hwin package RecurrentOne RecurrentTwo)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo A
        strategy hwin package RecurrentOne RecurrentTwo)
    (two : TwoControl A strategy hwin package RecurrentTwo) (own : In₂)
    (one : OneControl A strategy hwin package RecurrentOne)
    (delivered : In₁) :
    TwoControl A strategy hwin package RecurrentTwo :=
  (package.literalCombinedFreshRecvForkTwo A strategy hwin RecurrentOne
    RecurrentTwo pendingMixedRecv recurrentRecv two own one delivered).1.closedControl

/-! ## Exact fresh equations on the pending/pending branch -/

@[simp] theorem literalCombinedFreshRecvForkTwo_pending_pending
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (pendingMixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
        A strategy hwin package RecurrentOne RecurrentTwo)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo A
        strategy hwin package RecurrentOne RecurrentTwo)
    (twoPending : TwoPending A strategy hwin package)
    (onePending : OnePending A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    package.literalCombinedFreshRecvForkTwo A strategy hwin RecurrentOne
        RecurrentTwo pendingMixedRecv recurrentRecv (.inl twoPending) own
          (.inl onePending) delivered =
      package.literalCombinedFreshPendingRecvForkTwo A strategy hwin
        RecurrentTwo twoPending own onePending delivered :=
  rfl

@[simp] theorem literalCombinedFreshOpenRecvTwo_pending_pending_control
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (pendingMixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
        A strategy hwin package RecurrentOne RecurrentTwo)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo A
        strategy hwin package RecurrentOne RecurrentTwo)
    (twoPending : TwoPending A strategy hwin package)
    (onePending : OnePending A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalCombinedFreshOpenRecvTwo A strategy hwin RecurrentOne
      RecurrentTwo pendingMixedRecv recurrentRecv (.inl twoPending) own
        (.inl onePending) delivered).1 =
      (.inl
        (false,
          package.literalCombinedFreshTwoReceiveShared A strategy hwin
            twoPending.2.1 own onePending.2.1 delivered,
          (none : TwoPayload A strategy hwin package)) :
        TwoControl A strategy hwin package RecurrentTwo) :=
  rfl

@[simp] theorem literalCombinedFreshClosedRecvTwo_pending_pending_control
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (pendingMixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
        A strategy hwin package RecurrentOne RecurrentTwo)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo A
        strategy hwin package RecurrentOne RecurrentTwo)
    (twoPending : TwoPending A strategy hwin package)
    (onePending : OnePending A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    package.literalCombinedFreshClosedRecvTwo A strategy hwin RecurrentOne
        RecurrentTwo pendingMixedRecv recurrentRecv (.inl twoPending) own
          (.inl onePending) delivered =
      (.inl
        (true,
          package.literalCombinedFreshTwoReceiveShared A strategy hwin
            twoPending.2.1 own onePending.2.1 delivered,
          (none : TwoPayload A strategy hwin package)) :
        TwoControl A strategy hwin package RecurrentTwo) :=
  rfl

@[simp] theorem literalCombinedFreshOpenRecvTwo_pending_pending_output
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (pendingMixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshPendingMixedRecvForkTwo
        A strategy hwin package RecurrentOne RecurrentTwo)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkTwo A
        strategy hwin package RecurrentOne RecurrentTwo)
    (twoPending : TwoPending A strategy hwin package)
    (onePending : OnePending A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalCombinedFreshOpenRecvTwo A strategy hwin RecurrentOne
      RecurrentTwo pendingMixedRecv recurrentRecv (.inl twoPending) own
        (.inl onePending) delivered).2 =
      package.literalCombinedFreshTwoPendingReceiveOutput A strategy hwin
        twoPending.1 twoPending.2.1 own delivered :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
