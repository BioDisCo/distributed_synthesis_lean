/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController

/-!
# The preserved entry row of a full-restart occurrence

The linked finite-table receiver already stores an `anchor : Bool`.  That
anchor is installed with the occurrence and is preserved by every receive.
It is therefore the semantic entry row of the whole occurrence; the separate
`lastRecv` bit is only a phase/restart detector.

This module exposes that row and records its preservation by receiver and
complete-relay steps.  In particular, a restarted strict occurrence remains
on `.first`, while a closed occurrence installed with true anchors remains on
`.both`.
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

/-- Convert the table anchor into its semantic paired-entry row. -/
def profiledRawJointHybridFullRestartEntryRow (anchor : Bool) :
    PairedEntryRow :=
  if anchor then .both else .first

@[simp] theorem profiledRawJointHybridFullRestartEntryRow_false :
    profiledRawJointHybridFullRestartEntryRow false = .first := by
  rfl

@[simp] theorem profiledRawJointHybridFullRestartEntryRow_true :
    profiledRawJointHybridFullRestartEntryRow true = .both := by
  rfl

/-- The semantic row stored by a right receiver table. -/
def profiledRawJointRightFinitePayloadLiteralPrefixReceiverRow
    {Payload : Type p} [Fintype Payload]
    (receiver :
      ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A Payload) :
    PairedEntryRow :=
  profiledRawJointHybridFullRestartEntryRow receiver.2.1

/-- Left-receiver mirror. -/
def profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRow
    {Payload : Type p} [Fintype Payload]
    (receiver :
      ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A Payload) :
    PairedEntryRow :=
  profiledRawJointHybridFullRestartEntryRow receiver.2.1

@[simp] theorem
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial_row
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointRightFinitePayloadLiteralPrefixMove A Payload)
    (anchor : Bool) :
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRow A
        (profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
          anchor) =
      profiledRawJointHybridFullRestartEntryRow anchor := by
  rfl

@[simp] theorem
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial_row
    {Payload : Type p} [Fintype Payload]
    (move : ProfiledRawJointLeftFinitePayloadLiteralPrefixMove A Payload)
    (anchor : Bool) :
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRow A
        (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
          anchor) =
      profiledRawJointHybridFullRestartEntryRow anchor := by
  rfl

/-- A right receive cannot change the occurrence's entry row. -/
@[simp] theorem
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv_row
    {Payload : Type p} [Fintype Payload]
    (receiver :
      ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A Payload)
    (own : In₂) (delivered : In₁) :
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRow A
        (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
          receiver own delivered).2 =
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverRow A receiver := by
  rfl

/-- Left-receiver mirror. -/
@[simp] theorem
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv_row
    {Payload : Type p} [Fintype Payload]
    (receiver :
      ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A Payload)
    (own : In₁) (delivered : In₂) :
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRow A
        (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A receiver
          own delivered).2 =
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRow A receiver := by
  rfl

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

/-- Right occurrence row stored by a complete linked relay. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
    (relay : LinkedRelay A strategy hwin) : PairedEntryRow :=
  profiledRawJointRightFinitePayloadLiteralPrefixReceiverRow A relay.1.2

/-- Left occurrence row stored by a complete linked relay. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
    (relay : LinkedRelay A strategy hwin) : PairedEntryRow :=
  profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRow A relay.2.2

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial_rightRow
    (rightMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
        strategy hwin)
    (leftMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
        strategy hwin)
    (rightAnchor leftAnchor : Bool) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
          A strategy hwin rightMove leftMove rightAnchor leftAnchor) =
      profiledRawJointHybridFullRestartEntryRow rightAnchor := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial_leftRow
    (rightMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
        strategy hwin)
    (leftMove :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
        strategy hwin)
    (rightAnchor leftAnchor : Bool) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
          A strategy hwin rightMove leftMove rightAnchor leftAnchor) =
      profiledRawJointHybridFullRestartEntryRow leftAnchor := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance_rightRow
    (relay : LinkedRelay A strategy hwin) (input : In₁ × In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
          A strategy hwin relay input) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin relay := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance_leftRow
    (relay : LinkedRelay A strategy hwin) (input : In₁ × In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
          A strategy hwin relay input) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin relay := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_rightRow
    (state : BankControl A strategy hwin) (rightAnchor leftAnchor : Bool) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayRightRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
          A strategy hwin state rightAnchor leftAnchor) =
      profiledRawJointHybridFullRestartEntryRow rightAnchor := by
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay_leftRow
    (state : BankControl A strategy hwin) (rightAnchor leftAnchor : Bool) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRelayLeftRow
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
          A strategy hwin state rightAnchor leftAnchor) =
      profiledRawJointHybridFullRestartEntryRow leftAnchor := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
