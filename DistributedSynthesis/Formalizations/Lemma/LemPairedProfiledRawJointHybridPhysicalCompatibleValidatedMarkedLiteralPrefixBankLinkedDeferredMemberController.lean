/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedRetainedCarrier

/-!
# Resolver-free deferred-member controller for the linked retained bank

The payload-linked retained carrier stores the exact marked-bank child selected
by the old acknowledged entry row.  Consequently the deferred-member wrapper
does not need an arbitrary finite resolver.  At a receive it advances the one
shared linked relay and packages two locally computable interpretations:

* the open interpretation is the row-linked strict child and uses the `.first`
  anchors `(false, false)`;
* the closed interpretation is the simultaneous child of the current parent
  and uses the `.both` anchors `(true, true)`.

Both candidates store the same pair of tags and the same advanced relay.  The
two tags need not have equal children: equating the left and right strict
receiver payloads at a simultaneous receive would be false in general.  Blind
evolution never inspects either the hidden member or the payload, so the
dangerous pair law nevertheless holds at arbitrary depth by the generic
deferred-member construction.

No transition receives a graph, hierarchy side, orientation, leader bit,
strict-leader bit, semantic source, history, or view.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

/-! ## Exact child payload and canonical next-entry anchors -/

/-- The two possible installations of the same row-selected exact child. -/
abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload :=
  RetainedTag A strategy hwin × RetainedTag A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

/-- Select the tag belonging to the acknowledged member. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload.tag
    (payload : Payload A strategy hwin) (member : Bool) :
    RetainedTag A strategy hwin :=
  if member then payload.2 else payload.1

/-- `.first` is the false anchor at both endpoint tables. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFirstAnchors :
    Bool × Bool :=
  (false, false)

/-- `.both` is the true anchor at both endpoint tables. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredBothAnchors :
    Bool × Bool :=
  (true, true)

/-- Package the strict/open and simultaneous/closed children at their
respective next-entry rows. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChildren
    (openChild closedChild : BankControl A strategy hwin) :
    Payload A strategy hwin :=
  ((openChild,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFirstAnchors),
    (closedChild,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredBothAnchors))

/-- Initial totalization uses the root child in both slots.  The first real
receive replaces this payload before either slot can be semantically read. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
    (child : BankControl A strategy hwin) : Payload A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChildren
    A strategy hwin child child

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild_open_child
    (child : BankControl A strategy hwin) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin child).tag A strategy hwin false).1 = child :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild_closed_child
    (child : BankControl A strategy hwin) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin child).tag A strategy hwin true).1 = child :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild_open_anchors
    (child : BankControl A strategy hwin) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin child).tag A strategy hwin false).2 = (false, false) :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild_closed_anchors
    (child : BankControl A strategy hwin) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin child).tag A strategy hwin true).2 = (true, true) :=
  rfl

/-! ## Deferred controls -/

private abbrev OnePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (LinkedOne A strategy hwin) (Payload A strategy hwin)

private abbrev TwoPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (LinkedTwo A strategy hwin) (Payload A strategy hwin)

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOneControlFintype :
    Fintype (OneControl A strategy hwin) := by
  infer_instance

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTwoControlFintype :
    Fintype (TwoControl A strategy hwin) := by
  infer_instance

/-! ## Resolve the preceding member only when the next receive arrives -/

/-- Install a delivered tag in the linked retained carrier. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall
    (tag : RetainedTag A strategy hwin) :
    LinkedOne A strategy hwin × LinkedTwo A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
    A strategy hwin tag.1 tag.2.1 tag.2.2

/-- An open member continues the shared advanced relay; a closed member
installs the exact stored child at its `.both` anchors. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
    (fallback : LinkedOne A strategy hwin)
    (control : OneControl A strategy hwin) : LinkedOne A strategy hwin :=
  match control with
  | .inl pending =>
      if pending.1 then
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall
          A strategy hwin (pending.2.2.tag A strategy hwin true)).1
      else pending.2.1
  | .inr _ => fallback

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
    (fallback : LinkedTwo A strategy hwin)
    (control : TwoControl A strategy hwin) : LinkedTwo A strategy hwin :=
  match control with
  | .inl pending =>
      if pending.1 then
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall
          A strategy hwin (pending.2.2.tag A strategy hwin true)).2
      else pending.2.1
  | .inr _ => fallback

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open
    (fallback shared : LinkedOne A strategy hwin)
    (payload : Payload A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback
        (.inl (false, shared, payload) : OneControl A strategy hwin) = shared :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open
    (fallback shared : LinkedTwo A strategy hwin)
    (payload : Payload A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback
        (.inl (false, shared, payload) : TwoControl A strategy hwin) = shared :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_closed_child
    (fallback shared : LinkedOne A strategy hwin)
    (payload : Payload A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback
        (.inl (true, shared, payload) : OneControl A strategy hwin)).child A
          strategy hwin =
      (payload.tag A strategy hwin true).1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_closed_child
    (fallback shared : LinkedTwo A strategy hwin)
    (payload : Payload A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback
        (.inl (true, shared, payload) : TwoControl A strategy hwin)).child A
          strategy hwin =
      (payload.tag A strategy hwin true).1 :=
  rfl

/-! ## The locally selected authoritative parent -/

/-- Process one's linked receive imports the partner relay after a blind
round and retains its own relay after a preceding receive.  The parent bank
coordinate must follow exactly the same authority choice. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin) :
    BankControl A strategy hwin :=
  if one.2.1 then one.child A strategy hwin else two.child A strategy hwin

/-- Process-two mirror of the receive-time authority choice. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin) :
    BankControl A strategy hwin :=
  if two.2.1 then two.child A strategy hwin else one.child A strategy hwin

/-- When both local receive flags agree, their retained bank coordinates must
agree.  With unequal flags, both parent selectors automatically choose the
endpoint which received in the preceding strict round. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityCompatible
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin) :
    Prop :=
  one.2.1 = two.2.1 →
    one.child A strategy hwin = two.child A strategy hwin

/-- Pure four-case pair test: authority compatibility is exactly sufficient
for the two endpoint-local parent selections to coincide. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParents_eq_of_authorityCompatible
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityCompatible
        A strategy hwin one two) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
        A strategy hwin one two := by
  unfold
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityCompatible
    at hcompatible
  cases hone : one.2.1 <;> cases htwo : two.2.1
  · have hc := hcompatible (by simp [hone, htwo])
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
      hone, htwo] using hc.symm
  · simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
      hone, htwo]
  · simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
      hone, htwo]
  · have hc := hcompatible (by simp [hone, htwo])
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
      hone, htwo] using hc

/-! ## Member-independent blind evolution -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne
    (_member : Bool) (shared : LinkedOne A strategy hwin) (input : In₁) :
    LinkedOne A strategy hwin × Out₁ :=
  let next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne
      A strategy hwin shared input
  (next, next.1)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo
    (_member : Bool) (shared : LinkedTwo A strategy hwin) (input : In₂) :
    LinkedTwo A strategy hwin × Out₂ :=
  let next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo
      A strategy hwin shared input
  (next, next.1)

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne
        A strategy hwin) where
  outputEq := by intros; rfl
  stateEq := by intros; rfl

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo
        A strategy hwin) where
  outputEq := by intros; rfl
  stateEq := by intros; rfl

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
    (_ : PUnit.{1}) (_ : In₁) : PUnit.{1} × Out₁ :=
  (PUnit.unit, default)

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
    (_ : PUnit.{1}) (_ : In₂) : PUnit.{1} × Out₂ :=
  (PUnit.unit, default)

/-! ## Resolver-free receive data -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne A
    strategy hwin
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one) own
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two) delivered

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo A
    strategy hwin
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two) own
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one) delivered

/-- The receive output itself supplies the next exact child. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin × Payload A strategy hwin :=
  let received :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne
      A strategy hwin fallback one own two delivered
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
      A strategy hwin selectedOne selectedTwo
  let closedChild :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin parent (.simultaneous (own, delivered))
  (received,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChildren
      A strategy hwin (received.child A strategy hwin) closedChild)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin × Payload A strategy hwin :=
  let received :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo
      A strategy hwin fallback two own one delivered
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two
  let parent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
      A strategy hwin selectedOne selectedTwo
  let closedChild :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin parent (.simultaneous (delivered, own))
  (received,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChildren
      A strategy hwin (received.child A strategy hwin) closedChild)

/-- The process-one open tag contains exactly the child extracted from the
linked strict receiver target. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_open_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback one own two delivered).2.tag A strategy hwin
        false).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne
        A strategy hwin fallback one own two delivered).child A strategy
          hwin :=
  rfl

/-- Process-two open exact-child equation. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_open_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
      A strategy hwin fallback two own one delivered).2.tag A strategy hwin
        false).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo
        A strategy hwin fallback two own one delivered).child A strategy
          hwin :=
  rfl

/-- The process-one closed tag is the genuine simultaneous successor of its
selected current parent, not its left-strict receiver payload. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_closed_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback one own two delivered).2.tag A strategy hwin
        true).1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two))
        (.simultaneous (own, delivered)) :=
  rfl

/-- Process-two simultaneous-child mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_closed_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
      A strategy hwin fallback two own one delivered).2.tag A strategy hwin
        true).1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two))
        (.simultaneous (delivered, own)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_payload_anchors
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback one own two delivered).2.tag A strategy hwin
        false).2,
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
        A strategy hwin fallback one own two delivered).2.tag A strategy hwin
          true).2) = ((false, false), (true, true)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_payload_anchors
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
      A strategy hwin fallback two own one delivered).2.tag A strategy hwin
        false).2,
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
        A strategy hwin fallback two own one delivered).2.tag A strategy hwin
      true).2) = ((false, false), (true, true)) :=
  rfl

/-! ## The simultaneous pair test -/

/-- The exact precondition for the two endpoints to compute one common
simultaneous successor.  It compares their selected *current parents*, not the
left- and right-strict children emitted by the two linked receivers. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin) :
    Prop :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two) =
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two)

/-- The stable child-authority invariant on the receive-normalized controls. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedAuthorityCompatible
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin) :
    Prop :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityCompatible
    A strategy hwin
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two)

/-- Child authority implies equality of the two parent values actually used
by the linked receiver computations. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedAuthorityCompatible
        A strategy hwin fallback one two) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
      A strategy hwin fallback one two :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParents_eq_of_authorityCompatible
    A strategy hwin _ _ hcompatible

/-- Relation required of a simultaneous close: the true payloads select one
common bank child.  Equality of the false strict payloads is deliberately not
part of this relation and is generally false. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClosedPayloadsAgree
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin) :
    Prop :=
  match one, two with
  | .inl onePending, .inl twoPending =>
      (onePending.2.2.tag A strategy hwin true).1 =
        (twoPending.2.2.tag A strategy hwin true).1
  | _, _ => False

/-- Equal selected parents make the independently computed close payloads
equal, because both apply the same `.simultaneous (inputOne,inputTwo)` bank
transition. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFresh_closed_children_eq
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hparents :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
        A strategy hwin fallback one two) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback one inputOne two inputTwo).2.tag A strategy hwin
        true).1) =
      (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
        A strategy hwin fallback two inputTwo one inputOne).2.tag A strategy
          hwin true).1) := by
  unfold
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
    at hparents
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_closed_child,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_closed_child,
    hparents]

/-! The same equality stated on the actual canonical BOTH handler. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose_payloadsAgree
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hparents :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
        A strategy hwin fallback one two) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClosedPayloadsAgree
      A strategy hwin
      (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
          A strategy hwin fallback)
        one inputOne two inputTwo).1
      (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
          A strategy hwin fallback)
        one inputOne two inputTwo).2 := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFresh_closed_children_eq
      A strategy hwin fallback one inputOne two inputTwo hparents

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) : Out₁ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne
    A strategy hwin fallback one own two delivered).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) : Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo
    A strategy hwin fallback two own one delivered).1

/-! ## Canonical handlers and the structural dangerous-pair theorem -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne :
    OneControl A strategy hwin → In₁ → OneControl A strategy hwin × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
      (Out₁ := Out₁))

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo :
    TwoControl A strategy hwin → In₂ → TwoControl A strategy hwin × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
      (Out₂ := Out₂))

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputOne
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputTwo
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
      A strategy hwin fallback)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecvForkOne_eq
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
        A strategy hwin fallback)
      one own two delivered).1 =
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
        (Recurrent := PUnit.{1})
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
          A strategy hwin fallback one own two delivered).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
          A strategy hwin fallback one own two delivered).2 :=
  rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecvForkTwo_eq
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
        A strategy hwin fallback)
      two own one delivered).1 =
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
        (Recurrent := PUnit.{1})
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
          A strategy hwin fallback two own one delivered).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
          A strategy hwin fallback two own one delivered).2 :=
  rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecvForkOne_blind
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
          A strategy hwin fallback)
        one own two delivered).1.openControl
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
          A strategy hwin fallback)
        one own two delivered).1.closedControl := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecvForkOne_eq]
  exact FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork_blind _ _

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecvForkTwo_blind
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
          A strategy hwin fallback)
        two own one delivered).1.openControl
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
          A strategy hwin fallback)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
          A strategy hwin fallback)
        two own one delivered).1.closedControl := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecvForkTwo_eq]
  exact FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork_blind _ _

/-! ## Pending-only controller packages -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
    (initialTag : RetainedTag A strategy hwin) :
    LinkedOne A strategy hwin × LinkedTwo A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall A
    strategy hwin initialTag

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
    (initialTag : RetainedTag A strategy hwin) : OnePending A strategy hwin :=
  (false,
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag).1,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin initialTag.1)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
    (initialTag : RetainedTag A strategy hwin) : TwoPending A strategy hwin :=
  (false,
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag).2,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin initialTag.1)

/-! ## The decisive selected-pair relation -/

/-- Both semantic controls are pending, and their receive-normalized linked
states satisfy the finite child-authority invariant. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin) :
    Prop :=
  FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending one two ∧
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedAuthorityCompatible
      A strategy hwin fallback one two

/-- After a pending process-one blind step, member resolution can either keep
the advanced shared carrier or install the stored closed tag; both choices
have local receive flag `false`. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_noRecv_lastRecv
    (fallback : LinkedOne A strategy hwin)
    (pending : OnePending A strategy hwin) (input : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
        A strategy hwin (.inl pending) input).1).2.1 = false := by
  rcases pending with ⟨member, shared, payload⟩
  cases member <;> rfl

/-- Process-two mirror of the blind-step flag normalization. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_noRecv_lastRecv
    (fallback : LinkedTwo A strategy hwin)
    (pending : TwoPending A strategy hwin) (input : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
        A strategy hwin (.inl pending) input).1).2.1 = false := by
  rcases pending with ⟨member, shared, payload⟩
  cases member <;> rfl

/-- A canonical open receive selects its freshly received process-one shared
carrier, whose local receive flag is `true`. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_openRecv_lastRecv
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
        A strategy hwin fallback one inputOne two inputTwo).1).2.1 = true :=
  rfl

/-- Process-two mirror of the fresh receive flag equation. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_openRecv_lastRecv
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (one : OneControl A strategy hwin) (inputOne : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
        A strategy hwin fallback two inputTwo one inputOne).1).2.1 = true :=
  rfl

/-- The selected child-authority relation is closed under all three physical
round shapes.  Unequal receive flags make both strict cases vacuous.  In the
simultaneous case the two closed payloads use the common authoritative parent
and therefore install one equal `.simultaneous` child. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRelationLaws
    (initialTag : RetainedTag A strategy hwin) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelationLaws
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
          A strategy hwin initialTag) : OneControl A strategy hwin)
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
          A strategy hwin initialTag) : TwoControl A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
        A strategy hwin fallback)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
        A strategy hwin fallback) := by
  dsimp only
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  refine {
    initial := ?_
    strictRight := ?_
    strictLeft := ?_
    both := ?_ }
  · refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro _hflags
    rfl
  · intro one inputOne two inputTwo hrel
    rcases hrel with ⟨hpending, _hauthority⟩
    cases one with
    | inr recurrent => exact False.elim hpending.1
    | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        intro hflags
        have : False := by
          simpa only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_noRecv_lastRecv,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_openRecv_lastRecv,
            Bool.false_eq_true] using hflags
        exact this.elim
  · intro one inputOne two inputTwo hrel
    rcases hrel with ⟨hpending, _hauthority⟩
    cases one with
    | inr recurrent => exact False.elim hpending.1
    | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        intro hflags
        have : False := by
          simpa only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_openRecv_lastRecv,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_noRecv_lastRecv,
            Bool.true_eq_false] using hflags
        exact this.elim
  · intro one inputOne two inputTwo hrel
    rcases hrel with ⟨hpending, hauthority⟩
    cases one with
    | inr recurrent => exact False.elim hpending.1
    | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
        refine ⟨⟨trivial, trivial⟩, ?_⟩
        intro _hflags
        exact
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFresh_closed_children_eq
            A strategy hwin fallback (.inl onePending) inputOne
              (.inl twoPending) inputTwo
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
                A strategy hwin fallback (.inl onePending) (.inl twoPending)
                  hauthority)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredForkLaws
    (initialTag : RetainedTag A strategy hwin) :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredExactClosingForkLaws
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne_laws
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
      (Out₁ := Out₁))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo_laws
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
      (Out₂ := Out₂))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputTwo
      A strategy hwin fallback)

/-- The same canonical fork package, now carrying the decisive child-authority
relation rather than the trivial relation.  Fresh re-encapsulation is
definitionally independent of the relation; all mathematical content is in
`profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRelationLaws`.
-/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityForkLaws
    (initialTag : RetainedTag A strategy hwin) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    FiniteAcknowledgedDelayedCarrier.DeferredExactClosingForkLaws
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
          A strategy hwin initialTag) : OneControl A strategy hwin)
      (.inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
          A strategy hwin initialTag) : TwoControl A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
        (Out₁ := Out₁))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
        (Out₂ := Out₂))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
        A strategy hwin fallback)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
        A strategy hwin fallback) := by
  dsimp only
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  exact {
    relation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRelationLaws
        A strategy hwin initialTag
    pendingOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne_laws
        A strategy hwin
    pendingTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo_laws
        A strategy hwin
    receive := {
      one := by
        intro one inputOne two inputTwo _hrel
        exact ⟨
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
            A strategy hwin fallback one inputOne two inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
            A strategy hwin fallback one inputOne two inputTwo).2,
          rfl, rfl⟩
      two := by
        intro one inputOne two inputTwo _hrel
        exact ⟨
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
            A strategy hwin fallback two inputTwo one inputOne).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
            A strategy hwin fallback two inputTwo one inputOne).2,
          rfl, rfl⟩ } }

/-- Child authority, pending-only reachability, and blind fork compatibility
are preserved jointly by the executable acknowledged controller. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityBlindForkLaws
    (initialTag : RetainedTag A strategy hwin) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityForkLaws
    A strategy hwin initialTag).toExactClosingBlindForkLaws

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingForkLaws
    (initialTag : RetainedTag A strategy hwin) :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredPendingExactClosingForkLaws
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
      (Out₁ := Out₁))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
      (Out₂ := Out₂))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOutputTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
      A strategy hwin initialTag)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
      A strategy hwin initialTag)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne_laws
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo_laws
      A strategy hwin)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredBlindForkLaws
    (initialTag : RetainedTag A strategy hwin) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredForkLaws
    A strategy hwin initialTag).toExactClosingBlindForkLaws

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredMealyController
    (initialTag : RetainedTag A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredController
    (initialTag : RetainedTag A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredMealyController
    A strategy hwin initialTag).mooreize

/-! ## The authority invariant along the canonical semantic and physical traces -/

/-- The four local pair tests lift to every finite prefix of the canonical
semantic run.  In particular, the dangerous simultaneous case is no longer a
one-step experiment: every BOTH round is reached from a pair satisfying the
authority premise needed to compute one common closed bank child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairTrace_invariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    ∀ n,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
        A strategy hwin fallback
        (FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
          (.inl
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
              A strategy hwin initialTag) : OneControl A strategy hwin)
          (.inl
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
              A strategy hwin initialTag) : TwoControl A strategy hwin)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
            A strategy hwin)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
            A strategy hwin)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
            A strategy hwin fallback)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
            A strategy hwin fallback)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
            A strategy hwin fallback) env n).1
        (FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
          (.inl
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
              A strategy hwin initialTag) : OneControl A strategy hwin)
          (.inl
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
              A strategy hwin initialTag) : TwoControl A strategy hwin)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
            A strategy hwin)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
            A strategy hwin)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
            A strategy hwin fallback)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
            A strategy hwin fallback)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
            A strategy hwin fallback) env n).2 := by
  dsimp only
  let laws :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRelationLaws
      A strategy hwin initialTag
  intro n
  induction n with
  | zero => exact laws.initial
  | succ n ih =>
      rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
      split <;> rename_i hgraph
      · exact laws.strictRight _ _ _ _ ih
      · exact laws.strictLeft _ _ _ _ ih
      · exact laws.both _ _ _ _ ih

/-- The acknowledged executable controller has exactly the outputs of the
canonical authority-compatible semantic run.  This is the runtime form of
the dangerous pair test: unresolved fork identifiers and arbitrarily long
blind stretches are discharged by the generic acknowledged-carrier layer. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredMealyTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredMealyController
      A strategy hwin initialTag).LiteralCrossMealyTraceInvariant env := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let initialOne : OneControl A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag)
  let initialTwo : TwoControl A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag)
  let noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
      A strategy hwin
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
      A strategy hwin
  let openRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
      A strategy hwin fallback
  let openRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
      A strategy hwin fallback
  let close :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
      A strategy hwin fallback
  let Rel : OneControl A strategy hwin → TwoControl A strategy hwin → Prop :=
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback
  let Selected :=
    FiniteAcknowledgedDelayedCarrier.ExactClosingCanonicalSelected initialOne
      initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let expectedOne :=
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne initialOne
      initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let expectedTwo :=
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo initialOne
      initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close env
  let traceLaws :=
    FiniteAcknowledgedDelayedCarrier.exactClosingCanonicalSelectedTraceLaws
      initialOne initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close
        env Rel
  exact
    FiniteAcknowledgedDelayedCarrier.ExactClosingSelectedTraceLaws.toMealyTraceInvariant
      (initialOne := initialOne) (initialTwo := initialTwo)
      (noRecvOne := noRecvOne) (noRecvTwo := noRecvTwo)
      (openRecvOne := openRecvOne) (openRecvTwo := openRecvTwo)
      (close := close) (Rel := Rel)
      (BlindOne := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (BlindTwo := FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind)
      (Selected := Selected) (env := env)
      (expectedOutputOne := expectedOne) (expectedOutputTwo := expectedTwo)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityBlindForkLaws
        A strategy hwin initialTag)
      traceLaws

/-- Moore-facing authority-compatible trace invariant. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredController
      A strategy hwin initialTag).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredMealyTraceInvariant
    A strategy hwin initialTag env).toMooreTraceInvariant _

/-- The physical output word is the canonical authority-compatible reference
word, with the acknowledgement implementation erased extensionally. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceWord_eq_referenceWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredController
        A strategy hwin initialTag
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceInvariant
        A strategy hwin initialTag env).referenceWord controller := by
  dsimp only
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceInvariant
      A strategy hwin initialTag env).globalMachineTraceWord_eq_referenceWord _

end

end DetParityAutomaton

end DistributedSynthesis
