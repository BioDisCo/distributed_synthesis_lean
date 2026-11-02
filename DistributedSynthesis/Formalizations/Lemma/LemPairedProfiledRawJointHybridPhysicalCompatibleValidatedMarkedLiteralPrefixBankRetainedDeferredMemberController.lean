/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedReinstallation

/-!
# Deferred-member controller for the retained marked bank

This is the corrected executable wrapper around the retained literal carrier.
A receive is locally ambiguous between an interior strict round and a
simultaneous close.  The controller does not immediately fork an advanced
parent relay against a freshly restarted child.  Instead both candidates
store

* the same advanced parent relay;
* the same finite pair of exact tags for the one current child, with the two
  possible next-entry anchors; and
* one hidden member bit (`false` for open, `true` for closed).

Blind no-receive rounds advance the one shared parent relay and retain the
payload.  Hence arbitrary blind-depth output coherence is definitional.  At
the next receive the acknowledgement has resolved the old member.  The open
member continues the retained relay, while the closed member activates its
stored exact child before processing that new receive.

This is precisely the receive-time normalization discipline of
`DeferredMemberControl`.  It avoids the false equation between an advanced
parent control and a fresh child control.  The only model-specific executable
input is a finite function computing the next exact-child payload from the
two locally available controls and inputs.  No transition receives a graph,
orientation, hierarchy side, leader bit, strict-leader bit, history, or view.
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

private abbrev RetainedOne :=
  ProfiledRawJointHybridLiteralPrefixRetainedOneControl A

private abbrev RetainedTwo :=
  ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A

/-! ## One shared finite activation payload -/

/-- Both exact tags are stored before the new graph member is known.  The old
acknowledged entry row has already selected their common current child; the
new member varies only the anchors used to initialize the next entry.  We
retain the pair type so this timing constraint can be stated and proved by
the concrete resolver rather than hidden definitionally. -/
abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPayload :=
  RetainedTag A strategy hwin × RetainedTag A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPayload
    A strategy hwin

/-- Interpret a shared payload under its already stored member bit. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPayload.tag
  (payload : Payload A strategy hwin) (member : Bool) :
    RetainedTag A strategy hwin :=
  if member then payload.2 else payload.1

/-- At the initial root both interpretations use the given initial anchors. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInitialDeferredPayload
    (tag : RetainedTag A strategy hwin) : Payload A strategy hwin :=
  (tag, tag)

private abbrev OnePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl (RetainedOne A)
    (Payload A strategy hwin)

private abbrev TwoPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl (RetainedTwo A)
    (Payload A strategy hwin)

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent (RetainedOne A)
    (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent (RetainedTwo A)
    (Payload A strategy hwin) PUnit.{1}

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOneControlFintype :
    Fintype (OneControl A strategy hwin) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredTwoControlFintype :
    Fintype (TwoControl A strategy hwin) := by
  classical
  infer_instance

/-! ## Receive-time normalization of the preceding member -/

/-- The tag selected by the preceding acknowledged ambiguity.  It is finite
local data even when the open member continues a non-root relay. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTagOne
    (fallback : RetainedTag A strategy hwin)
    (control : OneControl A strategy hwin) : RetainedTag A strategy hwin :=
  match control with
  | .inl pending => pending.2.2.tag A strategy hwin pending.1
  | .inr _ => fallback

/-- Process-two tag selection. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTagTwo
    (fallback : RetainedTag A strategy hwin)
    (control : TwoControl A strategy hwin) : RetainedTag A strategy hwin :=
  match control with
  | .inl pending => pending.2.2.tag A strategy hwin pending.1
  | .inr _ => fallback

/-- Normalize process one's preceding member at the next receive.  An open
member continues the shared advanced parent; a closed member activates the
stored child. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne
    (fallback : RetainedOne A) (control : OneControl A strategy hwin) :
    RetainedOne A :=
  match control with
  | .inl pending =>
      if pending.1 then
        (pending.2.2.tag A strategy hwin true).initial A strategy hwin |>.1
      else pending.2.1
  | .inr _ => fallback

/-- Process-two receive-time normalization. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo
    (fallback : RetainedTwo A) (control : TwoControl A strategy hwin) :
    RetainedTwo A :=
  match control with
  | .inl pending =>
      if pending.1 then
        (pending.2.2.tag A strategy hwin true).initial A strategy hwin |>.2
      else pending.2.1
  | .inr _ => fallback

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne_open
    (fallback shared : RetainedOne A) (payload : Payload A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne
        A strategy hwin fallback
        (.inl (false, shared, payload) : OneControl A strategy hwin) = shared :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo_open
    (fallback shared : RetainedTwo A) (payload : Payload A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo
        A strategy hwin fallback
        (.inl (false, shared, payload) : TwoControl A strategy hwin) = shared :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne_closed
    (fallback shared : RetainedOne A) (payload : Payload A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne
        A strategy hwin fallback
        (.inl (true, shared, payload) : OneControl A strategy hwin) =
      ((payload.tag A strategy hwin true).initial A strategy hwin).1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo_closed
    (fallback shared : RetainedTwo A) (payload : Payload A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo
        A strategy hwin fallback
        (.inl (true, shared, payload) : TwoControl A strategy hwin) =
      ((payload.tag A strategy hwin true).initial A strategy hwin).2 :=
  rfl

/-! ## The one model-specific finite lookup -/

/-- Compute both exact tags for the ambiguity created by the current receive.
The old acknowledged entry row determines one exact current child; the first
and second components carry that same child with the open and closed
next-entry anchors, respectively.  The arguments are precisely the selected
finite tag/control pairs and the two current inputs available after delivery.
There is no graph argument. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredResolver
    where
  onePayload :
    RetainedTag A strategy hwin → RetainedOne A → In₁ →
      RetainedTag A strategy hwin → RetainedTwo A → In₂ →
        Payload A strategy hwin
  twoPayload :
    RetainedTag A strategy hwin → RetainedTwo A → In₂ →
      RetainedTag A strategy hwin → RetainedOne A → In₁ →
        Payload A strategy hwin

private abbrev Resolver :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredResolver
    A strategy hwin

/-! ## Member-independent blind steps -/

/-- Blind process-one evolution ignores the hidden member and advances the
one shared retained relay. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne
    (_member : Bool) (shared : RetainedOne A) (input : In₁) :
    RetainedOne A × Out₁ :=
  let next := profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A shared input
  (next, next.1)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo
    (_member : Bool) (shared : RetainedTwo A) (input : In₂) :
    RetainedTwo A × Out₂ :=
  let next := profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A shared input
  (next, next.1)

/-- The dangerous pair test is definitional: the member is never consulted. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne
        A) where
  outputEq := by intros; rfl
  stateEq := by intros; rfl

/-- Process-two dangerous pair test. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo
        A) where
  outputEq := by intros; rfl
  stateEq := by intros; rfl

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepOne
    (_ : PUnit.{1}) (_ : In₁) : PUnit.{1} × Out₁ :=
  (PUnit.unit, default)

def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepTwo
    (_ : PUnit.{1}) (_ : In₂) : PUnit.{1} × Out₂ :=
  (PUnit.unit, default)

/-! ## Exact receive data -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredReceivedOne
    (initialTag : RetainedTag A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) : RetainedOne A :=
  profiledRawJointHybridLiteralPrefixRetainedRecvOne A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne
      A strategy hwin (initialTag.initial A strategy hwin).1 one) own
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo
      A strategy hwin (initialTag.initial A strategy hwin).2 two) delivered

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredReceivedTwo
    (initialTag : RetainedTag A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) : RetainedTwo A :=
  profiledRawJointHybridLiteralPrefixRetainedRecvTwo A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo
      A strategy hwin (initialTag.initial A strategy hwin).2 two) own
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne
      A strategy hwin (initialTag.initial A strategy hwin).1 one) delivered

/-- Fresh process-one shared relay and exact-child payload. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshOne
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    RetainedOne A × Payload A strategy hwin :=
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne
      A strategy hwin (initialTag.initial A strategy hwin).1 one
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo
      A strategy hwin (initialTag.initial A strategy hwin).2 two
  let tagOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTagOne
      A strategy hwin initialTag one
  let tagTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTagTwo
      A strategy hwin initialTag two
  (profiledRawJointHybridLiteralPrefixRetainedRecvOne A selectedOne own
      selectedTwo delivered,
    resolver.onePayload tagOne selectedOne own tagTwo selectedTwo delivered)

/-- Fresh process-two data. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshTwo
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    RetainedTwo A × Payload A strategy hwin :=
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTwo
      A strategy hwin (initialTag.initial A strategy hwin).2 two
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedOne
      A strategy hwin (initialTag.initial A strategy hwin).1 one
  let tagTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTagTwo
      A strategy hwin initialTag two
  let tagOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredSelectedTagOne
      A strategy hwin initialTag one
  (profiledRawJointHybridLiteralPrefixRetainedRecvTwo A selectedTwo own
      selectedOne delivered,
    resolver.twoPayload tagTwo selectedTwo own tagOne selectedOne delivered)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputOne
    (initialTag : RetainedTag A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) : Out₁ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredReceivedOne
    A strategy hwin initialTag one own two delivered).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputTwo
    (initialTag : RetainedTag A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) : Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredReceivedTwo
    A strategy hwin initialTag two own one delivered).1

/-! ## Canonical exact-closing handlers -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredNoRecvOne :
    OneControl A strategy hwin → In₁ →
      OneControl A strategy hwin × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepOne
      (Out₁ := Out₁))

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredNoRecvTwo :
    TwoControl A strategy hwin → In₂ →
      TwoControl A strategy hwin × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepTwo
      (Out₂ := Out₂))

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvOne
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshOne
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputOne
      A strategy hwin initialTag)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvTwo
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshTwo
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputTwo
      A strategy hwin initialTag)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshOne
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshTwo
      A strategy hwin initialTag resolver)

/-! ## The dangerous receive pair is now structural -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecvForkOne_eq
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvOne
        A strategy hwin initialTag resolver)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
        A strategy hwin initialTag resolver)
      one own two delivered).1 =
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
        (Recurrent := PUnit.{1})
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshOne
          A strategy hwin initialTag resolver one own two delivered).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshOne
          A strategy hwin initialTag resolver one own two delivered).2 :=
  rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecvForkTwo_eq
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvTwo
        A strategy hwin initialTag resolver)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
        A strategy hwin initialTag resolver)
      two own one delivered).1 =
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork
        (Recurrent := PUnit.{1})
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshTwo
          A strategy hwin initialTag resolver two own one delivered).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshTwo
          A strategy hwin initialTag resolver two own one delivered).2 :=
  rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecvForkOne_blind
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvOne
          A strategy hwin initialTag resolver)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
          A strategy hwin initialTag resolver)
        one own two delivered).1.openControl
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvOne
          A strategy hwin initialTag resolver)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
          A strategy hwin initialTag resolver)
        one own two delivered).1.closedControl := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecvForkOne_eq]
  exact FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork_blind _ _

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecvForkTwo_blind
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrentBlind
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvTwo
          A strategy hwin initialTag resolver)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
          A strategy hwin initialTag resolver)
        two own one delivered).1.openControl
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvTwo
          A strategy hwin initialTag resolver)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
          A strategy hwin initialTag resolver)
        two own one delivered).1.closedControl := by
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecvForkTwo_eq]
  exact FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentFork_blind _ _

/-! ## Complete finite controller and blind-fork laws -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialOne
    (initialTag : RetainedTag A strategy hwin) : OnePending A strategy hwin :=
  (false, (initialTag.initial A strategy hwin).1,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInitialDeferredPayload
      A strategy hwin initialTag)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialTwo
    (initialTag : RetainedTag A strategy hwin) : TwoPending A strategy hwin :=
  (false, (initialTag.initial A strategy hwin).2,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInitialDeferredPayload
      A strategy hwin initialTag)

/-- One-arrow generic law package.  No parent/child control equality is an
assumption: blind coherence follows solely from the shared deferred member. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredForkLaws
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredExactClosingForkLaws
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne_laws
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepOne
      (Out₁ := Out₁))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo_laws
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepTwo
      (Out₂ := Out₂))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshOne
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshTwo
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputOne
      A strategy hwin initialTag)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputTwo
      A strategy hwin initialTag)

/-- Stronger one-arrow package: every live and dormant interpretation of the
actual acknowledgement relays remains in the deferred-table summand.  Thus
the recurrent `PUnit` branch is only totalization data and is unreachable in
the canonical run. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingForkLaws
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredPendingExactClosingForkLaws
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepOne
      (Out₁ := Out₁))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredRecurrentStepTwo
      (Out₂ := Out₂))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshOne
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredFreshTwo
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputOne
      A strategy hwin initialTag)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOutputTwo
      A strategy hwin initialTag)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialOne
      A strategy hwin initialTag)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialTwo
      A strategy hwin initialTag)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepOne_laws
      A)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredPendingStepTwo_laws
      A)

/-- The exact law bundle consumed by the acknowledged trace theorem.  Its
blind relations compare only the shared deferred state and payload; the two
member bits may differ. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredBlindForkLaws
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredForkLaws
    A strategy hwin initialTag resolver).toExactClosingBlindForkLaws

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredMealyController
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredNoRecvOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredNoRecvTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvOne
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvTwo
      A strategy hwin initialTag resolver)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
      A strategy hwin initialTag resolver)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredController
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredMealyController
    A strategy hwin initialTag resolver).mooreize

/-! ## Relay bookkeeping is completely discharged -/

/-- The acknowledged executable controller has exactly the outputs of its
canonical selected deferred-member run.  This statement is unconditional in
the resolver: semantic correctness of the resolver's returned tags is a
separate readback theorem, not a blind-fork premise. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredMealyTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredMealyController
      A strategy hwin initialTag resolver).LiteralCrossMealyTraceInvariant
        env := by
  let initialOne : OneControl A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialOne
        A strategy hwin initialTag)
  let initialTwo : TwoControl A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredInitialTwo
        A strategy hwin initialTag)
  let noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredNoRecvOne
      A strategy hwin
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredNoRecvTwo
      A strategy hwin
  let openRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvOne
      A strategy hwin initialTag resolver
  let openRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredOpenRecvTwo
      A strategy hwin initialTag resolver
  let close :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredClose
      A strategy hwin initialTag resolver
  let Rel : OneControl A strategy hwin → TwoControl A strategy hwin → Prop :=
    fun _ _ ↦ True
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredBlindForkLaws
        A strategy hwin initialTag resolver)
      traceLaws

/-- Moore-facing form used by the physical readback layer. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredController
      A strategy hwin initialTag resolver).LiteralCrossGraphTraceInvariant
        env :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredMealyTraceInvariant
    A strategy hwin initialTag resolver env).toMooreTraceInvariant _

/-- Hence the physical controller's word is its canonical selected reference
word, with all occurrence IDs, acknowledgements, and unresolved members
already eliminated. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredTraceWord_eq_referenceWord
    (initialTag : RetainedTag A strategy hwin)
    (resolver : Resolver A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredController
        A strategy hwin initialTag resolver
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredTraceInvariant
        A strategy hwin initialTag resolver env).referenceWord controller := by
  dsimp only
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedDeferredTraceInvariant
      A strategy hwin initialTag resolver env
      ).globalMachineTraceWord_eq_referenceWord _

end

end DetParityAutomaton

end DistributedSynthesis
