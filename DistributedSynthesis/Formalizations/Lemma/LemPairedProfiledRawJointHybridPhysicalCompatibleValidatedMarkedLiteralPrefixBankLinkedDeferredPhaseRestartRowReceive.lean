/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController

/-!
# Row-aware receives for the phase-restarted linked controller

The phase-restart controller already chooses the correct relay: it continues
the locally active occurrence and rebuilds at the delivered provisional child
on an orientation switch.  Its experimental receive map freezes the target
row at `.first`, which is sufficient for the persistent-strict suffix but is
not the retained-carrier row rule needed at a later simultaneous close.

This module changes only that row coordinate.  A receive after a local receive
uses `.both`; a receive after a blind round uses `.first`.  The choice is the
endpoint's stored `lastRecv` bit and therefore reveals no graph letter.  The
four theorems below prove the exact strict child selected in the continuing
and switching cases.  They are the local transition facts needed before the
same-occurrence simultaneous-output packet can be attached.
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

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev OldRightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev OldLeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

/-! ## Local row-aware receive maps -/

/-- Process one's phase-restarted receive with the retained local row rule. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin :=
  let row : PairedEntryRow := if state.2.1 then .both else .first
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
      A strategy hwin state partner
  let receiver :=
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A base.2.2 own
      delivered
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay
      A strategy hwin state partner (own, delivered)
  let child :=
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
      (receiver.1.target row).1
  (pairedLeftInformedForRow row receiver.1.physical,
    (true, (relay, child)))

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin :=
  let row : PairedEntryRow := if state.2.1 then .both else .first
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
      A strategy hwin partner state
  let receiver :=
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A base.1.2 own
      delivered
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay
      A strategy hwin partner state (delivered, own)
  let child :=
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
      (receiver.1.target row).1
  (pairedRightInformedForRow row receiver.1.physical,
    (true, (relay, child)))

/-! ## Continuing occurrences use the retained `.both` row -/

/-- On a continuing right phase, the row-aware receive selects the exact
`.both` strict child of the fixed epoch occurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo_same_child_eq
    (epochBase : BankControl A strategy hwin)
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁)
    (hsame : state.2.1 = true)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin epochBase state.2.2.1.1.1 state.2.2.1.1.2) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin epochBase
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) .both semanticPast
                  semanticInput)) := by
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hpair.payload_exists A strategy hwin (own, delivered) .both
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false => simp at hsame
  | true =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child,
        ↓reduceIte] using hpayload

/-- Continuing-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne_same_child_eq
    (epochBase : BankControl A strategy hwin)
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂)
    (hsame : state.2.1 = true)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin epochBase state.2.2.1.2.1 state.2.2.1.2.2) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin epochBase
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) .both semanticPast
                  semanticInput)) := by
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hpair.payload_exists A strategy hwin (own, delivered) .both
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false => simp at hsame
  | true =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child,
        ↓reduceIte] using hpayload

/-! ## Rebuilt occurrences use the fresh `.first` row -/

/-- At a left-to-right switch, the row-aware receive rebuilds at the
delivered provisional child and selects its exact `.first` strict child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo_switch_child_eq
    (state : LinkedTwo A strategy hwin) (own : In₂)
    (partner : LinkedOne A strategy hwin) (delivered : In₁)
    (hswitch : state.2.1 = false)
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin (partner.child A strategy hwin))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (partner.child A strategy hwin).2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : ((partner.child A strategy hwin).literal A strategy hwin).1 =
      some oldMove) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (partner.child A strategy hwin)
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) .first semanticPast
                  semanticInput)) := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (partner.child A strategy hwin) false false
  have hroot :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin (partner.child A strategy hwin) root.1.1 root.1.2 :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_rightPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hroot.payload_exists A strategy hwin (own, delivered) .first
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child,
        Bool.false_eq_true, ↓reduceIte] using hpayload
  | true => simp at hswitch

/-- Right-to-left switch mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne_switch_child_eq
    (state : LinkedOne A strategy hwin) (own : In₁)
    (partner : LinkedTwo A strategy hwin) (delivered : In₂)
    (hswitch : state.2.1 = false)
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin (partner.child A strategy hwin))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (partner.child A strategy hwin).2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : ((partner.child A strategy hwin).literal A strategy hwin).2 =
      some oldMove) :
    ∃ semanticPast semanticInput,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne
        A strategy hwin state own partner delivered).child A strategy hwin =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (partner.child A strategy hwin)
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) .first semanticPast
                  semanticInput)) := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (partner.child A strategy hwin) false false
  have hroot :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin (partner.child A strategy hwin) root.2.1 root.2.2 :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_leftPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hroot.payload_exists A strategy hwin (own, delivered) .first
  refine ⟨semanticPast, semanticInput, ?_⟩
  rcases state with ⟨out, flag, relay, storedChild⟩
  cases flag with
  | false =>
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child,
        Bool.false_eq_true, ↓reduceIte] using hpayload
  | true => simp at hswitch

/-! ## Acknowledged row-aware receive shell -/

/-- Resolve the two delivered controls and execute process one's row-aware
phase-restarted receive. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvOne
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one) own
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two) delivered

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRecvTwo
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two) own
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one) delivered

/-- The open member stores the exact row-aware strict child; the closed member
stores the simultaneous child of process one's selected authoritative parent. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    LinkedOne A strategy hwin × Payload A strategy hwin :=
  let received :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne
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

/-- Process-two fresh pair. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    LinkedTwo A strategy hwin × Payload A strategy hwin :=
  let received :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo
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

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOutputOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) : Out₁ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne
    A strategy hwin fallback one own two delivered).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOutputTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) : Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo
    A strategy hwin fallback two own one delivered).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOutputOne
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOutputTwo
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
      A strategy hwin fallback)

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne_open_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
      A strategy hwin fallback one own two delivered).2.tag A strategy hwin
        false).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne
        A strategy hwin fallback one own two delivered).child A strategy
          hwin :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo_open_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
      A strategy hwin fallback two own one delivered).2.tag A strategy hwin
        false).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo
        A strategy hwin fallback two own one delivered).child A strategy
          hwin :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne_closed_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (own : In₁)
    (two : TwoControl A strategy hwin) (delivered : In₂) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
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

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo_closed_child
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (own : In₂)
    (one : OneControl A strategy hwin) (delivered : In₁) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
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

/-- The row change affects only the open strict child.  Closed candidates
still install one common simultaneous bank child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFresh_closed_children_eq
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hparents :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
        A strategy hwin fallback one two) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
      A strategy hwin fallback one inputOne two inputTwo).2.tag A strategy
        hwin true).1) =
      (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
        A strategy hwin fallback two inputTwo one inputOne).2.tag A strategy
          hwin true).1) := by
  unfold
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
    at hparents
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne_closed_child,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo_closed_child,
    hparents]

/-- Finite executable acknowledged controller using the repaired row-aware
receives. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowMealyController
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
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
      A strategy hwin fallback)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowController
    (initialTag : RetainedTag A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowMealyController
    A strategy hwin initialTag).mooreize

/-! ## Three-case invariant -/

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOne_openRecv_lastRecv
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
        A strategy hwin fallback one inputOne two inputTwo).1).2.1 = true :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwo_openRecv_lastRecv
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (one : OneControl A strategy hwin) (inputOne : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
        A strategy hwin fallback two inputTwo one inputOne).1).2.1 = true :=
  rfl

/-- Pendingness and common child authority are preserved by every graph
letter for the row-aware controller. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRelationLaws
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwo_openRecv_lastRecv,
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOne_openRecv_lastRecv,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwo_noRecv_lastRecv,
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
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFresh_closed_children_eq
            A strategy hwin fallback (.inl onePending) inputOne
              (.inl twoPending) inputTwo
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
                A strategy hwin fallback (.inl onePending) (.inl twoPending)
                  hauthority)

/-- Canonical proof-side semantic controls of the row-aware controller. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
      A strategy hwin fallback) env n

/-- Every prefix of the row-aware semantic trace retains pending controls and
the exact common-child authority needed by a simultaneous close. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
          A strategy hwin initialTag env n).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
          A strategy hwin initialTag env n).2 := by
  dsimp only
  let laws :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRelationLaws
      A strategy hwin initialTag
  induction n with
  | zero => exact laws.initial
  | succ n ih =>
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
      split <;> rename_i hgraph
      · exact laws.strictRight _ _ _ _ ih
      · exact laws.strictLeft _ _ _ _ ih
      · exact laws.both _ _ _ _ ih

/-- Exact receive-phase bits after one row-aware semantic step.  A receiver
uses `.first` after a blind round and `.both` after a local receive. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_succ_selected_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
        A strategy hwin initialTag env (n + 1)
    let selectedOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 next.1
    let selectedTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 next.2
    match (env n).graph with
    | .right => selectedOne.2.1 = false ∧ selectedTwo.2.1 = true
    | .left => selectedOne.2.1 = true ∧ selectedTwo.2.1 = false
    | .both => selectedOne.2.1 = false ∧ selectedTwo.2.1 = false := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let current :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hnext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
          A strategy hwin initialTag env (n + 1) =
        match (env n).graph with
        | .right =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                A strategy hwin current.1 (env n).inputOne).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
                A strategy hwin fallback current.2 (env n).inputTwo current.1
                  (env n).inputOne).1)
        | .left =>
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
                A strategy hwin fallback current.1 (env n).inputOne current.2
                  (env n).inputTwo).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                A strategy hwin current.2 (env n).inputTwo).1)
        | .both =>
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
              A strategy hwin fallback current.1 (env n).inputOne current.2
                (env n).inputTwo := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
    rfl
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  change FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending
    current.1 current.2 at hpending
  cases hone : current.1 with
  | inr recurrent => exact False.elim (by simpa [hone] using hpending.1)
  | inl onePending =>
    cases htwo : current.2 with
    | inr recurrent => exact False.elim (by simpa [htwo] using hpending.2)
    | inl twoPending =>
      cases hgraph : (env n).graph with
      | right =>
          rw [hnext, hgraph, hone, htwo]
          exact ⟨
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv
              A strategy hwin fallback.1 onePending (env n).inputOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwo_openRecv_lastRecv
              A strategy hwin fallback (.inl twoPending) (env n).inputTwo
                (.inl onePending) (env n).inputOne⟩
      | left =>
          rw [hnext, hgraph, hone, htwo]
          exact ⟨
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOne_openRecv_lastRecv
              A strategy hwin fallback (.inl onePending) (env n).inputOne
                (.inl twoPending) (env n).inputTwo,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwo_noRecv_lastRecv
              A strategy hwin fallback.2 twoPending (env n).inputTwo⟩
      | both =>
          rw [hnext, hgraph, hone, htwo]
          exact ⟨rfl, rfl⟩

/-- Both selected phase bits start false. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_zero_selected_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
        A strategy hwin initialTag env 0
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 initial.1).2.1 = false ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 initial.2).2.1 = false := by
  exact ⟨rfl, rfl⟩

/-! ## Executable acknowledged trace -/

/-- Canonical fresh re-encapsulation together with the row-aware authority
relation. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowAuthorityForkLaws
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepOne
        (Out₁ := Out₁))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo
        A strategy hwin)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRecurrentStepTwo
        (Out₂ := Out₂))
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
        A strategy hwin fallback)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
        A strategy hwin fallback)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
        A strategy hwin fallback) := by
  dsimp only
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  exact {
    relation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRelationLaws
        A strategy hwin initialTag
    pendingOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepOne_laws
        A strategy hwin
    pendingTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPendingStepTwo_laws
        A strategy hwin
    receive := {
      one := by
        intro one inputOne two inputTwo _hrel
        exact ⟨
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
            A strategy hwin fallback one inputOne two inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
            A strategy hwin fallback one inputOne two inputTwo).2,
          rfl, rfl⟩
      two := by
        intro one inputOne two inputTwo _hrel
        exact ⟨
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
            A strategy hwin fallback two inputTwo one inputOne).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
            A strategy hwin fallback two inputTwo one inputOne).2,
          rfl, rfl⟩ } }

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowAuthorityBlindForkLaws
    (initialTag : RetainedTag A strategy hwin) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowAuthorityForkLaws
    A strategy hwin initialTag).toExactClosingBlindForkLaws

/-- The finite Mealy implementation has exactly the canonical row-aware
semantic outputs. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowMealyTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowMealyController
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
      A strategy hwin
  let noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
      A strategy hwin
  let openRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
      A strategy hwin fallback
  let openRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
      A strategy hwin fallback
  let close :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
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
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowAuthorityBlindForkLaws
        A strategy hwin initialTag)
      traceLaws

/-- Moore-facing row-aware trace invariant. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowTraceInvariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowController
      A strategy hwin initialTag).LiteralCrossGraphTraceInvariant env :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowMealyTraceInvariant
    A strategy hwin initialTag env).toMooreTraceInvariant _

/-- Physical row-aware trace word equals its canonical semantic reference. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowTraceWord_eq_referenceWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowController
        A strategy hwin initialTag
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowTraceInvariant
        A strategy hwin initialTag env).referenceWord controller := by
  dsimp only
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowTraceInvariant
      A strategy hwin initialTag env).globalMachineTraceWord_eq_referenceWord _

end

end DetParityAutomaton

end DistributedSynthesis
