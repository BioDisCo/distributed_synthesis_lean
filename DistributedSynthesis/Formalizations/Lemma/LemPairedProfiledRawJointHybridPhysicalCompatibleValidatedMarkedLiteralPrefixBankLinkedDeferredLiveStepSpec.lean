/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredMemberController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedLiveLane
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityTrace

/-!
# Exact live-step specifications for the linked deferred bank

This file joins the two independently checked parts of the construction:

* a live proof-generated linked table returns an exact marked-bank child after
  every finite retained prefix;
* the deferred open/closed selector installs exactly the child stored in the
  corresponding finite tag.

The specifications expose both the strict/open child and the simultaneous
closed child.  They do not identify the generally different strict children
computed by the two receiving endpoints.  The selected parent is proved equal
to the supplied reachable bank state before the simultaneous child is formed.

All orientations, semantic prefixes, and directions below are proof-side
witnesses.  The executable controls contain only finite linked states, the
acknowledgement bit, and the finite child payload.
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

private abbrev DeferredOne :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev DeferredTwo :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev OldRightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev OldLeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

/-! ## Canonical synchronized controls at an arbitrary retained prefix -/

/-- A proof-side synchronized process-one linked control.  The Boolean is the
endpoint's locally remembered receive bit. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne
    (state : BankControl A strategy hwin)
    (relay : LinkedRelay A strategy hwin) (lastRecv : Bool) :
    LinkedOne A strategy hwin :=
  (default, (lastRecv, (relay, state)))

/-- Process-two synchronized control. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo
    (state : BankControl A strategy hwin)
    (relay : LinkedRelay A strategy hwin) (lastRecv : Bool) :
    LinkedTwo A strategy hwin :=
  (default, (lastRecv, (relay, state)))

/-- Pending process-one wrapper whose open member selects the synchronized
linked control. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne
    (state : BankControl A strategy hwin)
    (relay : LinkedRelay A strategy hwin) (lastRecv : Bool) :
    DeferredOne A strategy hwin :=
  .inl
    (false,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne
        A strategy hwin state relay lastRecv,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
        A strategy hwin state)

/-- Pending process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo
    (state : BankControl A strategy hwin)
    (relay : LinkedRelay A strategy hwin) (lastRecv : Bool) :
    DeferredTwo A strategy hwin :=
  .inl
    (false,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo
        A strategy hwin state relay lastRecv,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
        A strategy hwin state)

/-- The acknowledged row selected by a local retained bit. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow
    (lastRecv : Bool) : PairedEntryRow :=
  if lastRecv then .both else .first

/-! ## Downstream specifications -/

/-- Everything needed downstream from one right-oriented live receive.
`fresh` is the process-two fresh pair.  Its false member installs the exact
strict child extracted from the linked table; its true member installs the
simultaneous child of the selected parent. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightLiveStepSpec
    (state parent : BankControl A strategy hwin)
    (fresh : LinkedTwo A strategy hwin × Payload A strategy hwin)
    (input : In₁ × In₂) (row : PairedEntryRow) where
  semanticPast : List (In₂ × In₁)
  semanticInput : In₂ × In₁
  selectedParent_eq : parent = state
  openChild_eq :
    (fresh.2.tag A strategy hwin false).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row semanticPast
                semanticInput))
  openChild_reachable :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (fresh.2.tag A strategy hwin false).1
  closedChild_eq :
    (fresh.2.tag A strategy hwin true).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin parent (.simultaneous input)
  closedChild_reachable :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (fresh.2.tag A strategy hwin true).1
  selectedOpen_child_eq :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fresh.1
        (.inl (false, fresh.1, fresh.2) : DeferredTwo A strategy hwin)).child A
          strategy hwin =
      (fresh.2.tag A strategy hwin false).1
  selectedClosed_child_eq :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fresh.1
        (.inl (true, fresh.1, fresh.2) : DeferredTwo A strategy hwin)).child A
          strategy hwin =
      (fresh.2.tag A strategy hwin true).1

/-- Left-oriented mirror. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftLiveStepSpec
    (state parent : BankControl A strategy hwin)
    (fresh : LinkedOne A strategy hwin × Payload A strategy hwin)
    (input : In₁ × In₂) (row : PairedEntryRow) where
  semanticPast : List (In₁ × In₂)
  semanticInput : In₁ × In₂
  selectedParent_eq : parent = state
  openChild_eq :
    (fresh.2.tag A strategy hwin false).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row semanticPast
                semanticInput))
  openChild_reachable :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (fresh.2.tag A strategy hwin false).1
  closedChild_eq :
    (fresh.2.tag A strategy hwin true).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin parent (.simultaneous input)
  closedChild_reachable :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (fresh.2.tag A strategy hwin true).1
  selectedOpen_child_eq :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fresh.1
        (.inl (false, fresh.1, fresh.2) : DeferredOne A strategy hwin)).child A
          strategy hwin =
      (fresh.2.tag A strategy hwin false).1
  selectedClosed_child_eq :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fresh.1
        (.inl (true, fresh.1, fresh.2) : DeferredOne A strategy hwin)).child A
          strategy hwin =
      (fresh.2.tag A strategy hwin true).1

/-! ## The first receive after an arbitrary local blind prefix -/

/-- Iterate process one's retained linked state through a finite no-receive
prefix. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne
    (shared : LinkedOne A strategy hwin) : List In₁ → LinkedOne A strategy hwin
  | [] => shared
  | input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne
          A strategy hwin shared input) inputs

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo
    (shared : LinkedTwo A strategy hwin) : List In₂ → LinkedTwo A strategy hwin
  | [] => shared
  | input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo
          A strategy hwin shared input) inputs

/-- Iterate the actual outer acknowledged process-one control over the same
blind prefix. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne
    (control : DeferredOne A strategy hwin) : List In₁ → DeferredOne A strategy hwin
  | [] => control
  | input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
          A strategy hwin control input).1 inputs

/-- Outer process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo
    (control : DeferredTwo A strategy hwin) : List In₂ → DeferredTwo A strategy hwin
  | [] => control
  | input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
          A strategy hwin control input).1 inputs

/-- The outer no-receive run preserves the pending member and payload and
advances exactly the shared linked state. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne_pending
    (member : Bool) (shared : LinkedOne A strategy hwin)
    (payload : Payload A strategy hwin) (inputs : List In₁) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne
        A strategy hwin
          (.inl (member, shared, payload) : DeferredOne A strategy hwin)
          inputs =
      .inl
        (member,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne
            A strategy hwin shared inputs,
          payload) := by
  induction inputs generalizing shared with
  | nil => rfl
  | cons input inputs ih =>
      simp only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne,
        FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne]
      exact ih _

/-- Process-two pending shape. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo_pending
    (member : Bool) (shared : LinkedTwo A strategy hwin)
    (payload : Payload A strategy hwin) (inputs : List In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo
        A strategy hwin
          (.inl (member, shared, payload) : DeferredTwo A strategy hwin)
          inputs =
      .inl
        (member,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo
            A strategy hwin shared inputs,
          payload) := by
  induction inputs generalizing shared with
  | nil => rfl
  | cons input inputs ih =>
      simp only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo,
        FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPendingStepTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo]
      exact ih _

/-- Blind evolution preserves the exact child stored in process one's linked
state. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne_child
    (shared : LinkedOne A strategy hwin) (inputs : List In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne
      A strategy hwin shared inputs).child A strategy hwin =
        shared.child A strategy hwin := by
  induction inputs generalizing shared with
  | nil => rfl
  | cons input inputs ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne]
      rw [ih]
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne_child
          A strategy hwin shared input

/-- Process-two child preservation. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo_child
    (shared : LinkedTwo A strategy hwin) (inputs : List In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo
      A strategy hwin shared inputs).child A strategy hwin =
        shared.child A strategy hwin := by
  induction inputs generalizing shared with
  | nil => rfl
  | cons input inputs ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo]
      rw [ih]
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo_child
          A strategy hwin shared input

/-- A false process-one receive bit remains false through every blind
prefix. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne_lastRecv_of_false
    (shared : LinkedOne A strategy hwin) (hfalse : shared.2.1 = false)
    (inputs : List In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne
      A strategy hwin shared inputs).2.1 = false := by
  induction inputs generalizing shared with
  | nil => exact hfalse
  | cons input inputs ih =>
      apply ih
      rfl

/-- Process-two false-bit preservation. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo_lastRecv_of_false
    (shared : LinkedTwo A strategy hwin) (hfalse : shared.2.1 = false)
    (inputs : List In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo
      A strategy hwin shared inputs).2.1 = false := by
  induction inputs generalizing shared with
  | nil => exact hfalse
  | cons input inputs ih =>
      apply ih
      rfl

/-- Every blind prefix from the canonical process-one tag root has local
receive bit `false`. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne_initial_lastRecv
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (inputs : List In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag).1 inputs).2.1 = false := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne_lastRecv_of_false
      A strategy hwin _ rfl inputs

/-- Process-two initial blind-prefix flag. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo_initial_lastRecv
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (inputs : List In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag).2 inputs).2.1 = false := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo_lastRecv_of_false
      A strategy hwin _ rfl inputs

/-- Side `1 → 2`: after any process-one blind prefix, resolving the outer
pending control at process two selects exactly the bank state carried by the
delivered tag.  This is the front-to-tail handoff equation; neither endpoint
is given the direction as runtime data. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightFirstReceive_selectedParent
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (inputs : List In₁) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let delivered :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne
        A strategy hwin
          (.inl
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
              A strategy hwin initialTag) : DeferredOne A strategy hwin)
          inputs
    let ownInitial : DeferredTwo A strategy hwin :=
      .inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
          A strategy hwin initialTag)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 delivered)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 ownInitial) =
      initialTag.1 := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne_pending]
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child]
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag).1 inputs).child A strategy hwin =
      initialTag.1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunOne_child]
  rfl

/-- Side `2 → 1` mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftFirstReceive_selectedParent
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (inputs : List In₂) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
        A strategy hwin initialTag
    let delivered :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo
        A strategy hwin
          (.inl
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
              A strategy hwin initialTag) : DeferredTwo A strategy hwin)
          inputs
    let ownInitial : DeferredOne A strategy hwin :=
      .inl
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
          A strategy hwin initialTag)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 ownInitial)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 delivered) =
      initialTag.1 := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo_pending]
  simp [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInstall,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child]
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag).2 inputs).child A strategy hwin =
      initialTag.1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSharedNoRecvRunTwo_child]
  rfl

/-! ## Complete arbitrary-prefix live steps -/

/-- A live right lookup, run through an arbitrary finite complete prefix,
produces one complete deferred receive specification.  The locally remembered
bit chooses only between the two acknowledged rows; it is not a direction or
leader bit. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightLiveStepSpec_of_move
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove)
    (rightAnchor leftAnchor continued : Bool)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin root past
    let fallback :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne
          A strategy hwin state relay continued,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo
          A strategy hwin state relay continued)
    let one : DeferredOne A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne
        A strategy hwin state relay continued
    let two : DeferredTwo A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo
        A strategy hwin state relay continued
    let fresh :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
        A strategy hwin fallback two input.2 one input.1
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two)
    Nonempty
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightLiveStepSpec
        A strategy hwin state parent fresh input
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow
            continued)) := by
  dsimp only
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRunOfState_right_payload_exists
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        past input
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow
          continued)
  refine ⟨{
    semanticPast := semanticPast
    semanticInput := semanticInput
    selectedParent_eq := ?_
    openChild_eq := ?_
    openChild_reachable := ?_
    closedChild_eq := ?_
    closedChild_reachable := ?_
    selectedOpen_child_eq := ?_
    selectedClosed_child_eq := ?_ }⟩
  · cases continued <;> rfl
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_open_child]
    cases continued <;>
      simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child]
        using hpayload
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_open_child]
    have hopen := hpayload
    cases continued <;>
      simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child]
        at hopen ⊢ <;>
      rw [hopen] <;>
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
          strategy hwin state hreachable _
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_closed_child]
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_closed_child]
    cases continued <;>
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
          strategy hwin state hreachable (.simultaneous input)
  · rfl
  · rfl

/-- Left-oriented mirror of the complete arbitrary-prefix live step. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftLiveStepSpec_of_move
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove)
    (rightAnchor leftAnchor continued : Bool)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin root past
    let fallback :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne
          A strategy hwin state relay continued,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo
          A strategy hwin state relay continued)
    let one : DeferredOne A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne
        A strategy hwin state relay continued
    let two : DeferredTwo A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo
        A strategy hwin state relay continued
    let fresh :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
        A strategy hwin fallback one input.1 two input.2
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two)
    Nonempty
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftLiveStepSpec
        A strategy hwin state parent fresh input
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow
            continued)) := by
  dsimp only
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRunOfState_left_payload_exists
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        past input
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow
          continued)
  refine ⟨{
    semanticPast := semanticPast
    semanticInput := semanticInput
    selectedParent_eq := ?_
    openChild_eq := ?_
    openChild_reachable := ?_
    closedChild_eq := ?_
    closedChild_reachable := ?_
    selectedOpen_child_eq := ?_
    selectedClosed_child_eq := ?_ }⟩
  · cases continued <;> rfl
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_open_child]
    cases continued <;>
      simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child]
        using hpayload
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_open_child]
    have hopen := hpayload
    cases continued <;>
      simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne,
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child]
        at hopen ⊢ <;>
      rw [hopen] <;>
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
          strategy hwin state hreachable _
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_closed_child]
  · rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne_closed_child]
    cases continued <;>
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
          strategy hwin state hreachable (.simultaneous input)
  · rfl
  · rfl

/-- On a reachable live right lane the literal-move premise of
`RightLiveStepSpec_of_move` is automatic. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightLiveStepSpec_of_liveLane
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (slot : ProfiledRawRightSlot A)
    (hlive : code.family.right () = some slot)
    (rightAnchor leftAnchor continued : Bool)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin root past
    let fallback :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne
          A strategy hwin state relay continued,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo
          A strategy hwin state relay continued)
    let one : DeferredOne A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne
        A strategy hwin state relay continued
    let two : DeferredTwo A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo
        A strategy hwin state relay continued
    let fresh :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
        A strategy hwin fallback two input.2 one input.1
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two)
    Nonempty
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightLiveStepSpec
        A strategy hwin state parent fresh input
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow
            continued)) := by
  obtain ⟨oldMove, hmove, _hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightLiveStepSpec_of_move
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        continued past input

/-- Reachable live left-lane mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftLiveStepSpec_of_liveLane
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (slot : ProfiledRawLeftSlot A)
    (hlive : code.family.left () = some slot)
    (rightAnchor leftAnchor continued : Bool)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin root past
    let fallback :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveOne
          A strategy hwin state relay continued,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveTwo
          A strategy hwin state relay continued)
    let one : DeferredOne A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingOne
        A strategy hwin state relay continued
    let two : DeferredTwo A strategy hwin :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLivePendingTwo
        A strategy hwin state relay continued
    let fresh :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
        A strategy hwin fallback one input.1 two input.2
    let parent :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two)
    Nonempty
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftLiveStepSpec
        A strategy hwin state parent fresh input
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLiveRow
            continued)) := by
  obtain ⟨oldMove, hmove, _hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftLiveStepSpec_of_move
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        continued past input

/-! ## Selected-relay adapters for the canonical trace -/

/-- If the relay selected by process two's acknowledged receive is a right
pair at some bank parent, the received child is exactly a strict child of
that parent.  This isolates the only trace bookkeeping needed downstream:
showing that the selected relay has the pair-at-prefix invariant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo_child_eq_of_rightPairAtPrefix
    (state : BankControl A strategy hwin)
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : DeferredOne A strategy hwin) (two : DeferredTwo A strategy hwin)
    (own : In₂) (delivered : In₁) :
    let selectedOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one
    let selectedTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two
    let base := if selectedTwo.2.1 then selectedTwo.2.2.1 else selectedOne.2.2.1
    let row : PairedEntryRow := if selectedTwo.2.1 then .both else .first
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin state base.1.1 base.1.2 →
      ∃ semanticPast semanticInput,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo
          A strategy hwin fallback two own one delivered).child A strategy
            hwin =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin state
              (.strict
                (profiledRawJointUnitRightActualDirection
                  (In₁ := In₁) (In₂ := In₂) row semanticPast
                    semanticInput)) := by
  dsimp only
  intro hpair
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hpair.payload_exists A strategy hwin (own, delivered)
      (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 two).2.1
      then .both else .first)
  refine ⟨semanticPast, semanticInput, ?_⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo]
    using hpayload

/-- Process-one/left selected-relay mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne_child_eq_of_leftPairAtPrefix
    (state : BankControl A strategy hwin)
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : DeferredOne A strategy hwin) (two : DeferredTwo A strategy hwin)
    (own : In₁) (delivered : In₂) :
    let selectedOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 one
    let selectedTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 two
    let base := if selectedOne.2.1 then selectedOne.2.2.1 else selectedTwo.2.2.1
    let row : PairedEntryRow := if selectedOne.2.1 then .both else .first
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin state base.2.1 base.2.2 →
      ∃ semanticPast semanticInput,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne
          A strategy hwin fallback one own two delivered).child A strategy
            hwin =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin state
              (.strict
                (profiledRawJointUnitLeftActualDirection
                  (In₁ := In₁) (In₂ := In₂) row semanticPast
                    semanticInput)) := by
  dsimp only
  intro hpair
  obtain ⟨semanticPast, semanticInput, hpayload⟩ :=
    hpair.payload_exists A strategy hwin (own, delivered)
      (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 one).2.1
      then .both else .first)
  refine ⟨semanticPast, semanticInput, ?_⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne]
    using hpayload

/-- Diagnostic strict-right trace adapter under the extra assumption that the
selected relay is rooted at the current provisional parent.  That assumption
is not preserved by consecutive strict rounds; use the epoch-base interface
below for trace induction. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictRightChildAt_eq_children_of_parentRootedPairAtPrefix
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (_hgraph : (env n).graph = .right) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
        A strategy hwin initialTag
    let pair :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
        A strategy hwin initialTag env n
    let selectedOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1
    let selectedTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2
    let base := if selectedTwo.2.1 then selectedTwo.2.2.1 else selectedOne.2.2.1
    let row : PairedEntryRow := if selectedTwo.2.1 then .both else .first
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwoAt
            A strategy hwin initialTag env n)
          base.1.1 base.1.2 →
      ∃ semanticPast semanticInput,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictRightChildAt
            A strategy hwin initialTag env n =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
                A strategy hwin initialTag env n)
              (.strict
                (profiledRawJointUnitRightActualDirection
                  (In₁ := In₁) (In₂ := In₂) row semanticPast
                    semanticInput)) := by
  dsimp only
  intro hpair
  obtain ⟨semanticPast, semanticInput, hexact⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo_child_eq_of_rightPairAtPrefix
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwoAt
          A strategy hwin initialTag env n)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
          A strategy hwin initialTag)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n).2
        (env n).inputTwo (env n).inputOne hpair
  refine ⟨semanticPast, semanticInput, ?_⟩
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictRightChildAt,
    hexact,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAt_eq]

/-- Non-inductive parent-rooted strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictLeftChildAt_eq_children_of_parentRootedPairAtPrefix
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (_hgraph : (env n).graph = .left) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
        A strategy hwin initialTag
    let pair :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
        A strategy hwin initialTag env n
    let selectedOne :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1
    let selectedTwo :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2
    let base := if selectedOne.2.1 then selectedOne.2.2.1 else selectedTwo.2.2.1
    let row : PairedEntryRow := if selectedOne.2.1 then .both else .first
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
            A strategy hwin initialTag env n)
          base.2.1 base.2.2 →
      ∃ semanticPast semanticInput,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictLeftChildAt
            A strategy hwin initialTag env n =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
                A strategy hwin initialTag env n)
              (.strict
                (profiledRawJointUnitLeftActualDirection
                  (In₁ := In₁) (In₂ := In₂) row semanticPast
                    semanticInput)) := by
  dsimp only
  intro hpair
  obtain ⟨semanticPast, semanticInput, hexact⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne_child_eq_of_leftPairAtPrefix
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env n)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
          A strategy hwin initialTag)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n).2
        (env n).inputOne (env n).inputTwo hpair
  refine ⟨semanticPast, semanticInput, ?_⟩
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictLeftChildAt,
    hexact]

/-! ## Non-inductive parent-rooted diagnostic -/

/-- The selected right relay at a canonical trace position is rooted at the
process-two authoritative parent and still denotes one exact semantic
occurrence. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentRootedSelectedRightPairAtPrefixAt
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base := if selectedTwo.2.1 then selectedTwo.2.2.1 else selectedOne.2.2.1
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwoAt
        A strategy hwin initialTag env n)
      base.1.1 base.1.2

/-- Selected-left mirror, rooted at process one's authoritative parent. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentRootedSelectedLeftPairAtPrefixAt
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base := if selectedOne.2.1 then selectedOne.2.2.1 else selectedTwo.2.2.1
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
        A strategy hwin initialTag env n)
      base.2.1 base.2.2

/-- Diagnostic consequence of parent-rooted selected relays.  Its premise is
not inductive: after two consecutive strict rounds the relay is still rooted
at the epoch base while `ParentOneAt` is already a provisional child.  The
epoch-base theorem below is the reusable interface. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityStepExists_of_parentRootedPairs
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hright : (env n).graph = .right →
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentRootedSelectedRightPairAtPrefixAt
        A strategy hwin initialTag env n)
    (hleft : (env n).graph = .left →
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentRootedSelectedLeftPairAtPrefixAt
        A strategy hwin initialTag env n) :
    ∃ direction :
        ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂),
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
              A strategy hwin initialTag env n)
            direction := by
  cases hgraph : (env n).graph with
  | right =>
      have hpair := hright hgraph
      unfold
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentRootedSelectedRightPairAtPrefixAt
        at hpair
      obtain ⟨semanticPast, semanticInput, hchild⟩ :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictRightChildAt_eq_children_of_parentRootedPairAtPrefix
          A strategy hwin initialTag env n hgraph hpair
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n
      let selectedTwo :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 pair.2
      let row : PairedEntryRow := if selectedTwo.2.1 then .both else .first
      refine ⟨.strict
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row semanticPast semanticInput), ?_⟩
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_right
          A strategy hwin initialTag env n hgraph]
      simpa only [row, selectedTwo, pair, fallback] using hchild
  | left =>
      have hpair := hleft hgraph
      unfold
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentRootedSelectedLeftPairAtPrefixAt
        at hpair
      obtain ⟨semanticPast, semanticInput, hchild⟩ :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictLeftChildAt_eq_children_of_parentRootedPairAtPrefix
          A strategy hwin initialTag env n hgraph hpair
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n
      let selectedOne :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 pair.1
      let row : PairedEntryRow := if selectedOne.2.1 then .both else .first
      refine ⟨.strict
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row semanticPast semanticInput), ?_⟩
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_left
          A strategy hwin initialTag env n hgraph]
      simpa only [row, selectedOne, pair, fallback] using hchild
  | both =>
      exact ⟨.simultaneous ((env n).inputOne, (env n).inputTwo),
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_both
          A strategy hwin initialTag env n hgraph⟩

/-! ## Correct epoch-base interface -/

/-- The acknowledged row used by process two's strict-right receiver. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRowAt
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : PairedEntryRow :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  if selectedTwo.2.1 then .both else .first

/-- Process-one strict-left row. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRowAt
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : PairedEntryRow :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  if selectedOne.2.1 then .both else .first

/-- The selected right relay is rooted at the explicit epoch base, not at the
provisional child carried by `ParentOneAt`. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredEpochSelectedRightPairAtPrefixAt
    (epochBase : Nat → BankControl A strategy hwin)
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base := if selectedTwo.2.1 then selectedTwo.2.2.1 else selectedOne.2.2.1
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
    A strategy hwin (epochBase n) base.1.1 base.1.2

/-- Epoch-rooted selected-left mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredEpochSelectedLeftPairAtPrefixAt
    (epochBase : Nat → BankControl A strategy hwin)
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base := if selectedOne.2.1 then selectedOne.2.2.1 else selectedTwo.2.2.1
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
    A strategy hwin (epochBase n) base.2.1 base.2.2

/-- Correct three-graph authority-step relation.  Strict rounds produce a
provisional child of the unchanged epoch base.  A BOTH round commits from the
current provisional parent; the bookkeeping layer separately sets the next
epoch base to that committed child. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityEpochStepAt
    (epochBase : Nat → BankControl A strategy hwin)
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  match (env n).graph with
  | .right =>
      ∃ semanticPast semanticInput,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
            A strategy hwin initialTag env (n + 1) =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin (epochBase n)
              (.strict
                (profiledRawJointUnitRightActualDirection
                  (In₁ := In₁) (In₂ := In₂)
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRowAt
                      A strategy hwin initialTag env n)
                    semanticPast semanticInput))
  | .left =>
      ∃ semanticPast semanticInput,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
            A strategy hwin initialTag env (n + 1) =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin (epochBase n)
              (.strict
                (profiledRawJointUnitLeftActualDirection
                  (In₁ := In₁) (In₂ := In₂)
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRowAt
                      A strategy hwin initialTag env n)
                    semanticPast semanticInput))
  | .both =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
              A strategy hwin initialTag env n)
            (.simultaneous ((env n).inputOne, (env n).inputTwo))

/-- The live selected-relay invariants discharge the corrected epoch step in
all three graph cases. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityEpochStepAt_of_selectedPairs
    (epochBase : Nat → BankControl A strategy hwin)
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hright : (env n).graph = .right →
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredEpochSelectedRightPairAtPrefixAt
        A strategy hwin epochBase initialTag env n)
    (hleft : (env n).graph = .left →
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredEpochSelectedLeftPairAtPrefixAt
        A strategy hwin epochBase initialTag env n) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityEpochStepAt
      A strategy hwin epochBase initialTag env n := by
  cases hgraph : (env n).graph with
  | right =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityEpochStepAt,
        hgraph]
      have hpair := hright hgraph
      unfold
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredEpochSelectedRightPairAtPrefixAt
        at hpair
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n
      obtain ⟨semanticPast, semanticInput, hchild⟩ :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo_child_eq_of_rightPairAtPrefix
          A strategy hwin (epochBase n) fallback pair.1 pair.2
            (env n).inputTwo (env n).inputOne hpair
      refine ⟨semanticPast, semanticInput, ?_⟩
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_right
          A strategy hwin initialTag env n hgraph,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictRightChildAt]
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedRightRowAt,
        fallback, pair] using hchild
  | left =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityEpochStepAt,
        hgraph]
      have hpair := hleft hgraph
      unfold
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredEpochSelectedLeftPairAtPrefixAt
        at hpair
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
          A strategy hwin initialTag env n
      obtain ⟨semanticPast, semanticInput, hchild⟩ :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne_child_eq_of_leftPairAtPrefix
          A strategy hwin (epochBase n) fallback pair.1 pair.2
            (env n).inputOne (env n).inputTwo hpair
      refine ⟨semanticPast, semanticInput, ?_⟩
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_left
          A strategy hwin initialTag env n hgraph,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictLeftChildAt]
      simpa only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedLeftRowAt,
        fallback, pair] using hchild
  | both =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityEpochStepAt,
        hgraph]
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_both
          A strategy hwin initialTag env n hgraph

end

end DetParityAutomaton

end DistributedSynthesis
