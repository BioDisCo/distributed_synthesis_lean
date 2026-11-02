/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveControl
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessReceiveSource
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessSwitchRegression

/-!
# Process-one handler for a combined fresh receive

Process one stores two independent pieces of finite control.  Its left-seam
sender supplies a blind no-receive, while its right-seam receiver fork stores
the two possible interpretations of the old occurrence.  A receive selects
that old receiver with the old member bit, advances it, and emits the matching
heterogeneous output coordinate.  It then discards the old occurrence and
constructs one canonical false/true fork for the new occurrence.

The shared state also carries the finite freshness control.  On a receive,
process one locally selects the current pre-round policy copy from its own
freshness state and the delivered process-two freshness state.  This matters
at a hierarchy switch: after `right,right,left`, process one's old key is
stale and the delivered process-two copy must be used.  The new key stores
that selected source and the current input pair, while the new freshness copy
stores exactly one successor of it.  Thus the handler remains endpoint-local:
it takes only stored finite controls and locally available inputs.  It does
not receive a graph, orientation, hierarchy side, leader bit, history, or
view.

The recurrent receive case is a parameter.  This keeps the map total without
choosing the later recurrent product prematurely; all exact equations below
concern the pending case used by the fresh receive invariant.
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

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev FreshTwo :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
    initial

private abbrev OneShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev OnePayload (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
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

private abbrev OneControl
    (package : Package A strategy hwin initial) (RecurrentOne : Type r₁) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package RecurrentOne

private abbrev TwoControl
    (package : Package A strategy hwin initial) (RecurrentTwo : Type r₂) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package RecurrentTwo

private abbrev RightReceiverOutput
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A strategy
    hwin package

/-! ## Blind process-one projections -/

/- The combined-control module owns the shared pending step and its
member-independence proof.  The following two equations expose its executable
sender and physical output to the endpoint handler. -/

@[simp] theorem literalCombinedFreshOnePendingStep_sender
    (package : Package A strategy hwin initial)
    (member : Bool) (shared : OneShared A strategy hwin package)
    (input : In₁) :
    (package.literalCombinedFreshOnePendingStep A strategy hwin member shared
      input).1.2.1 =
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin shared.2.1
        input).2 :=
  rfl

@[simp] theorem literalCombinedFreshOnePendingStep_output
    (package : Package A strategy hwin initial)
    (member : Bool) (shared : OneShared A strategy hwin package)
    (input : In₁) :
    (package.literalCombinedFreshOnePendingStep A strategy hwin member shared
      input).2 =
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin shared.2.1
        input).1 :=
  rfl

/-! ## Selecting the old receiver's physical coordinate -/

/-- Read the physical process-one output from the heterogeneous product at
the old member.  The unused product coordinate is never emitted. -/
noncomputable def literalCombinedFreshOneSelectedPhysicalOutput
    (package : Package A strategy hwin initial)
    (member : Bool) (output : RightReceiverOutput A strategy hwin package) :
    Out₁ :=
  match member with
  | false => profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.1
  | true => profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.2

@[simp] theorem literalCombinedFreshOneSelectedPhysicalOutput_false
    (package : Package A strategy hwin initial)
    (output : RightReceiverOutput A strategy hwin package) :
    package.literalCombinedFreshOneSelectedPhysicalOutput A strategy hwin
        false output =
      profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.1 :=
  rfl

@[simp] theorem literalCombinedFreshOneSelectedPhysicalOutput_true
    (package : Package A strategy hwin initial)
    (output : RightReceiverOutput A strategy hwin package) :
    package.literalCombinedFreshOneSelectedPhysicalOutput A strategy hwin
        true output =
      profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.2 :=
  rfl

/-- The key stored by process one's blind sender is the one local finite key
used to freshen the next occurrence. -/
def literalCombinedFreshOneStoredKey
    (package : Package A strategy hwin initial)
    (shared : OneShared A strategy hwin package) : Key A strategy hwin package :=
  shared.2.1.1

/-! ## Pending receive and canonical re-encapsulation -/

/-- The pre-round policy copy selected by process one's local phase bit.
When process one is a stale right sender this is the delivered process-two
copy; otherwise it is process one's own copy. -/
def literalCombinedFreshOneReceiveSource
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package)
    (two : TwoShared A strategy hwin package) :
    State A strategy hwin (initial := initial) :=
  decoratedFreshnessRecvOneSource A strategy hwin one.1 two.1

/-- The new local freshness state is exactly one successor of the selected
pre-round source. -/
def literalCombinedFreshOneReceiveFreshness
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package) (own : In₁)
    (two : TwoShared A strategy hwin package) (delivered : In₂) :
    FreshOne A strategy hwin (initial := initial) :=
  decoratedFreshnessRecvOne A strategy hwin package one.1 own two.1 delivered

/-- The seam key retains the pre-round source and current input pair.  It is
deliberately not reconstructed from the already-advanced freshness state. -/
def literalCombinedFreshOneReceiveKey
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package) (own : In₁)
    (two : TwoShared A strategy hwin package) (delivered : In₂) :
    Key A strategy hwin package :=
  (package.literalCombinedFreshOneReceiveSource A strategy hwin one two,
    (own, delivered))

@[simp] theorem literalCombinedFreshOneReceiveFreshness_state
    (package : Package A strategy hwin initial)
    (one : OneShared A strategy hwin package) (own : In₁)
    (two : TwoShared A strategy hwin package) (delivered : In₂) :
    (package.literalCombinedFreshOneReceiveFreshness A strategy hwin one own
      two delivered).1 =
      package.policy.successor
        (package.literalCombinedFreshOneReceiveSource A strategy hwin one two)
        (own, delivered) :=
  rfl

/-- Resolve the old right receiver, emit its selected physical coordinate,
and replace the old occurrence by the canonical new false/true fork.  The old
payload is intentionally discarded: the new stage starts at `none`. -/
noncomputable def literalCombinedFreshOnePendingRecvFork
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁)
    (pending : OnePending A strategy hwin package)
    (other : TwoPending A strategy hwin package)
    (own : In₁) (delivered : In₂) :
    FiniteDelayedFork (OneControl A strategy hwin package RecurrentOne) ×
      Out₁ :=
  let member := pending.1
  let shared := pending.2.1
  let oldReceiver :=
    package.literalCombinedFreshOneReceiver A strategy hwin member shared
  let oldResult := package.literalRightSeamStagedReceiverRecv A strategy hwin
    oldReceiver own delivered
  let otherShared := other.2.1
  let fresh := package.literalCombinedFreshOneReceiveFreshness A strategy hwin
    shared own otherShared delivered
  let key := package.literalCombinedFreshOneReceiveKey A strategy hwin shared
    own otherShared delivered
  let nextShared := package.literalCrossCombinedFreshOneSharedAt A strategy
    hwin fresh key
  (FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
      (Recurrent := RecurrentOne) nextShared
      (none : OnePayload A strategy hwin package),
    package.literalCombinedFreshOneSelectedPhysicalOutput A strategy hwin
      member oldResult.1)

@[simp] theorem literalCombinedFreshOnePendingRecvFork_fork
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁)
    (pending : OnePending A strategy hwin package)
    (other : TwoPending A strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalCombinedFreshOnePendingRecvFork A strategy hwin
      RecurrentOne pending other own delivered).1 =
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
        (Recurrent := RecurrentOne)
        (package.literalCrossCombinedFreshOneSharedAt A strategy hwin
          (package.literalCombinedFreshOneReceiveFreshness A strategy hwin
            pending.2.1 own other.2.1 delivered)
          (package.literalCombinedFreshOneReceiveKey A strategy hwin
            pending.2.1 own other.2.1 delivered))
        (none : OnePayload A strategy hwin package) :=
  rfl

/-- Definitional current-output equation.  The later trace invariant is
responsible for identifying this stored old receiver with the semantic
`nextPairAt` occurrence; the executable map itself performs only this local
projection. -/
@[simp] theorem literalCombinedFreshOnePendingRecvFork_output
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁)
    (pending : OnePending A strategy hwin package)
    (other : TwoPending A strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalCombinedFreshOnePendingRecvFork A strategy hwin
      RecurrentOne pending other own delivered).2 =
      package.literalCombinedFreshOneSelectedPhysicalOutput A strategy hwin
        pending.1
        (package.literalRightSeamStagedReceiverRecv A strategy hwin
          (package.literalCombinedFreshOneReceiver A strategy hwin pending.1
            pending.2.1) own delivered).1 :=
  rfl

/-! ## Total endpoint-local receive map -/

/-- A recurrent implementation supplies its own receive fork.  Keeping this
case parametric makes the combined handler total without assuming a concrete
recurrent product. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂) :=
  RecurrentOne → In₁ → TwoControl A strategy hwin package RecurrentTwo →
    In₂ → FiniteDelayedFork
      (OneControl A strategy hwin package RecurrentOne) × Out₁

/-- The off-invariant mixed mode (process one pending, process two already
recurrent) is totalized parametrically.  No fabricated freshness value is
allowed into the exact pending/pending path. -/
abbrev ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂) :=
  OnePending A strategy hwin package → In₁ → RecurrentTwo → In₂ →
    FiniteDelayedFork (OneControl A strategy hwin package RecurrentOne) ×
      Out₁

/-- Total process-one receive fork: pending states use the exact construction
above, and recurrent states delegate to the supplied recurrent handler. -/
noncomputable def literalCombinedFreshRecvForkOne
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (mixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (one : OneControl A strategy hwin package RecurrentOne) (own : In₁)
    (two : TwoControl A strategy hwin package RecurrentTwo) (delivered : In₂) :
    FiniteDelayedFork (OneControl A strategy hwin package RecurrentOne) ×
      Out₁ :=
  match one, two with
  | .inl pending, .inl other =>
      package.literalCombinedFreshOnePendingRecvFork A strategy hwin
        RecurrentOne pending other own delivered
  | .inl pending, .inr recurrent =>
      mixedRecv pending own recurrent delivered
  | .inr recurrent, two => recurrentRecv recurrent own two delivered

/-- Open branch used by the ordinary process-one receive handler. -/
noncomputable def literalCombinedFreshOpenRecvOne
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (mixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (one : OneControl A strategy hwin package RecurrentOne) (own : In₁)
    (two : TwoControl A strategy hwin package RecurrentTwo) (delivered : In₂) :
    OneControl A strategy hwin package RecurrentOne × Out₁ :=
  let result := package.literalCombinedFreshRecvForkOne A strategy hwin
    RecurrentOne RecurrentTwo recurrentRecv mixedRecv one own two delivered
  (result.1.openControl, result.2)

/-- Process-one projection of the joint exact close.  The later joint module
combines this with the mirror closed projection computed from the same pair
of local inputs. -/
noncomputable def literalCombinedFreshCloseOne
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (mixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (one : OneControl A strategy hwin package RecurrentOne) (own : In₁)
    (two : TwoControl A strategy hwin package RecurrentTwo) (delivered : In₂) :
    OneControl A strategy hwin package RecurrentOne :=
  (package.literalCombinedFreshRecvForkOne A strategy hwin RecurrentOne
    RecurrentTwo recurrentRecv mixedRecv one own two delivered).1.closedControl

/-! ## Exact pending branch equations -/

@[simp] theorem literalCombinedFreshOpenRecvOne_pending_state
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (mixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (pending : OnePending A strategy hwin package)
    (other : TwoPending A strategy hwin package)
    (own : In₁)
    (delivered : In₂) :
    (package.literalCombinedFreshOpenRecvOne A strategy hwin RecurrentOne
      RecurrentTwo recurrentRecv mixedRecv (.inl pending) own (.inl other)
        delivered).1 =
      (.inl
        (false,
          package.literalCrossCombinedFreshOneSharedAt A strategy hwin
            (package.literalCombinedFreshOneReceiveFreshness A strategy hwin
              pending.2.1 own other.2.1 delivered)
            (package.literalCombinedFreshOneReceiveKey A strategy hwin
              pending.2.1 own other.2.1 delivered),
          (none : OnePayload A strategy hwin package)) :
        OneControl A strategy hwin package RecurrentOne) :=
  rfl

@[simp] theorem literalCombinedFreshCloseOne_pending_state
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (mixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (pending : OnePending A strategy hwin package)
    (other : TwoPending A strategy hwin package)
    (own : In₁)
    (delivered : In₂) :
    package.literalCombinedFreshCloseOne A strategy hwin RecurrentOne
        RecurrentTwo recurrentRecv mixedRecv (.inl pending) own (.inl other)
          delivered =
      (.inl
        (true,
          package.literalCrossCombinedFreshOneSharedAt A strategy hwin
            (package.literalCombinedFreshOneReceiveFreshness A strategy hwin
              pending.2.1 own other.2.1 delivered)
            (package.literalCombinedFreshOneReceiveKey A strategy hwin
              pending.2.1 own other.2.1 delivered),
          (none : OnePayload A strategy hwin package)) :
        OneControl A strategy hwin package RecurrentOne) :=
  rfl

@[simp] theorem literalCombinedFreshOpenRecvOne_pending_output
    (package : Package A strategy hwin initial)
    (RecurrentOne : Type r₁) (RecurrentTwo : Type r₂)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (mixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne A
        strategy hwin package RecurrentOne RecurrentTwo)
    (pending : OnePending A strategy hwin package)
    (other : TwoPending A strategy hwin package)
    (own : In₁)
    (delivered : In₂) :
    (package.literalCombinedFreshOpenRecvOne A strategy hwin RecurrentOne
      RecurrentTwo recurrentRecv mixedRecv (.inl pending) own (.inl other)
        delivered).2 =
      package.literalCombinedFreshOneSelectedPhysicalOutput A strategy hwin
        pending.1
        (package.literalRightSeamStagedReceiverRecv A strategy hwin
          (package.literalCombinedFreshOneReceiver A strategy hwin pending.1
            pending.2.1) own delivered).1 :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
