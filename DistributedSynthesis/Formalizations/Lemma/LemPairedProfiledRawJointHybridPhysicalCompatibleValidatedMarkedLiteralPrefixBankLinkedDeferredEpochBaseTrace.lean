/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredLiveStepSpec

/-!
# Epoch-base provenance of the linked deferred trace

A strict receive advances one literal table; it does not reinstall that table
at the provisional bank child returned by the receive.  Consequently the
selected relay remains rooted at the base of the current epoch.  Only a
simultaneous close installs a new root.

This file records the selected relay explicitly and proves the part needed by
eventually homogeneous tails: along a strict-right (respectively strict-left)
suffix, an exact pair-at-prefix witness is preserved at one fixed epoch base.
This is the corrected replacement for the non-inductive, parent-rooted
premise.
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

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev OnePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (LinkedOne A strategy hwin) (Payload A strategy hwin)

private abbrev TwoPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (LinkedTwo A strategy hwin) (Payload A strategy hwin)

private abbrev DeferredOne :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev DeferredTwo :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

/-! ## The selected complete relay -/

/-- Complete relay selected by process two's receive-time authority rule. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRelay
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : DeferredOne A strategy hwin)
    (two : DeferredTwo A strategy hwin) : LinkedRelay A strategy hwin :=
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two
  if selectedTwo.2.1 then selectedTwo.2.2.1 else selectedOne.2.2.1

/-- Complete relay selected by process one's mirror authority rule. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRelay
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : DeferredOne A strategy hwin)
    (two : DeferredTwo A strategy hwin) : LinkedRelay A strategy hwin :=
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 one
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 two
  if selectedOne.2.1 then selectedOne.2.2.1 else selectedTwo.2.2.1

/-- On a strict-right round, the receiver-selected complete relay advances
exactly once from the previously selected complete relay. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRelay_strictRight
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OnePending A strategy hwin) (two : TwoPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRelay
        A strategy hwin fallback
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
            A strategy hwin (.inl one) input.1).1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
            A strategy hwin fallback (.inl two) input.2 (.inl one)
              input.1).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRelay
            A strategy hwin fallback (.inl one) (.inl two)) input := by
  rcases one with ⟨memberOne, sharedOne, payloadOne⟩
  rcases two with ⟨memberTwo, sharedTwo, payloadTwo⟩
  cases memberOne <;> cases memberTwo <;> rfl

/-- Strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRelay_strictLeft
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OnePending A strategy hwin) (two : TwoPending A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRelay
        A strategy hwin fallback
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
            A strategy hwin fallback (.inl one) input.1 (.inl two)
              input.2).1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
            A strategy hwin (.inl two) input.2).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRelay
            A strategy hwin fallback (.inl one) (.inl two)) input := by
  rcases one with ⟨memberOne, sharedOne, payloadOne⟩
  rcases two with ⟨memberTwo, sharedTwo, payloadTwo⟩
  cases memberOne <;> cases memberTwo <;> rfl

/-! ## Fixed-base pair preservation -/

/-- One strict-right round preserves the right pair-at-prefix invariant at
the same epoch base. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightPairAtPrefix_strictRight
    (epochBase : BankControl A strategy hwin)
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OnePending A strategy hwin) (two : TwoPending A strategy hwin)
    (input : In₁ × In₂)
    (hpair :
      let relay :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRelay
          A strategy hwin fallback (.inl one) (.inl two)
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin epochBase relay.1.1 relay.1.2) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRelay
        A strategy hwin fallback
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
            A strategy hwin (.inl one) input.1).1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
            A strategy hwin fallback (.inl two) input.2 (.inl one)
              input.1).1
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin epochBase relay.1.1 relay.1.2 := by
  dsimp only at hpair ⊢
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRelay_strictRight
      A strategy hwin]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hpair.step A strategy hwin (input.2, input.1)

/-- One strict-left round preserves the left pair at the same epoch base. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftPairAtPrefix_strictLeft
    (epochBase : BankControl A strategy hwin)
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OnePending A strategy hwin) (two : TwoPending A strategy hwin)
    (input : In₁ × In₂)
    (hpair :
      let relay :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRelay
          A strategy hwin fallback (.inl one) (.inl two)
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin epochBase relay.2.1 relay.2.2) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRelay
        A strategy hwin fallback
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
            A strategy hwin fallback (.inl one) input.1 (.inl two)
              input.2).1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
            A strategy hwin (.inl two) input.2).1
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin epochBase relay.2.1 relay.2.2 := by
  dsimp only at hpair ⊢
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRelay_strictLeft
      A strategy hwin]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hpair.step A strategy hwin input

/-! ## Fail-fast reversal adapter

The current carrier advances both tables of the selected old relay.  Hence a
right-to-left reversal does not, merely by advancing that relay, retarget the
left table from the old block base to the provisional right child.  The local
repair is the same one used by the older phase-live controller: the endpoint
which has not received in the preceding round recognizes the switch from its
own `lastRecv` bit, rebuilds at the delivered partner's stored child, and then
advances that fresh pair once.  A repeated orientation continues the locally
retained table.

The following definitions are an experimental adapter only; the stable
controller is deliberately not mutated here. -/

private abbrev OldRightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev OldLeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

/-- Fresh complete linked relay at one provisional child. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
    (state : BankControl A strategy hwin) (rightAnchor leftAnchor : Bool) :
    LinkedRelay A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
    A strategy hwin (state.linkedRightMove A strategy hwin)
      (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor

/-- Process two's local base choice for a right receive.  A preceding right
receive continues the retained block.  Otherwise the delivered process-one
child starts the new right block. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin) :
    LinkedRelay A strategy hwin :=
  if two.2.1 then two.2.2.1
  else
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (one.child A strategy hwin) false false

/-- Process-one/left mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin) :
    LinkedRelay A strategy hwin :=
  if one.2.1 then one.2.2.1
  else
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (two.child A strategy hwin) false false

/-- Complete relay retained after the phase-sensitive right receive. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (input : In₁ × In₂) : LinkedRelay A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
        A strategy hwin one two) input

/-- Complete relay retained after the mirror receive. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (input : In₁ × In₂) : LinkedRelay A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
        A strategy hwin one two) input

/-- On the switch branch, process two's ordinary parent is exactly the
delivered process-one provisional child used by the restart. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo_eq_childOne_of_restart
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hswitch : two.2.1 = false) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
        A strategy hwin one two =
      one.child A strategy hwin := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
    hswitch]

/-- Left switch mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne_eq_childTwo_of_restart
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hswitch : one.2.1 = false) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin one two =
      two.child A strategy hwin := by
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    hswitch]

/-- A fresh right restart is an exact root pair whenever the provisional
child has a live right lane. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_rightPairAtPrefix
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove)
    (rightAnchor leftAnchor : Bool) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state rightAnchor leftAnchor
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin state relay.1.1 relay.1.2 := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay]
    using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_rightPairAtPrefix
        A strategy hwin hreachable code hcode oldMove hmove rightAnchor
          leftAnchor)

/-- Fresh left restart mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_leftPairAtPrefix
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove)
    (rightAnchor leftAnchor : Bool) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state rightAnchor leftAnchor
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin state relay.2.1 relay.2.2 := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay]
    using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_leftPairAtPrefix
        A strategy hwin hreachable code hcode oldMove hmove rightAnchor
          leftAnchor)

/-- The switch branch really yields an exact right pair at the delivered
provisional child after the current input is consumed. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay_switch_pairAtPrefix
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hswitch : two.2.1 = false)
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin (one.child A strategy hwin))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (one.child A strategy hwin).2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : ((one.child A strategy hwin).literal A strategy hwin).1 =
      some oldMove)
    (input : In₁ × In₂) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay
        A strategy hwin one two input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin (one.child A strategy hwin) relay.1.1 relay.1.2 := by
  dsimp only
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_rightPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    hswitch]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hroot.step A strategy hwin (input.2, input.1)

/-- Left reversal mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay_switch_pairAtPrefix
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hswitch : one.2.1 = false)
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin (two.child A strategy hwin))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : (two.child A strategy hwin).2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : ((two.child A strategy hwin).literal A strategy hwin).2 =
      some oldMove)
    (input : In₁ × In₂) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay
        A strategy hwin one two input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin (two.child A strategy hwin) relay.2.1 relay.2.2 := by
  dsimp only
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_leftPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove false false
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    hswitch]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hroot.step A strategy hwin input

/-- On a repeated right round, the experimental adapter preserves the
existing epoch-base witness. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay_same_pairAtPrefix
    (epochBase : BankControl A strategy hwin)
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hsame : two.2.1 = true) (input : In₁ × In₂)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin epochBase two.2.2.1.1.1 two.2.2.1.1.2) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay
        A strategy hwin one two input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin epochBase relay.1.1 relay.1.2 := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase,
    hsame]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hpair.step A strategy hwin (input.2, input.1)

/-- Repeated-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay_same_pairAtPrefix
    (epochBase : BankControl A strategy hwin)
    (one : LinkedOne A strategy hwin) (two : LinkedTwo A strategy hwin)
    (hsame : one.2.1 = true) (input : In₁ × In₂)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin epochBase one.2.2.1.2.1 one.2.2.1.2.2) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay
        A strategy hwin one two input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin epochBase relay.2.1 relay.2.2 := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftRelay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase,
    hsame]
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hpair.step A strategy hwin input

end

end DetParityAutomaton

end DistributedSynthesis
