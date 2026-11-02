/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedPayload

/-!
# A retained carrier which does not erase the exact bank child

The older retained literal carrier keeps only the physical right/left table
controls.  That is sufficient for output readback, but it cannot implement a
resolver for the next marked-bank state: the row target has already been
erased.

This file runs the payload-linked literal-prefix tables themselves.  Its relay
contains all four finite linked controls.  On a receive the locally selected
old entry row is applied to the full receiver target and the exact
`BankControl` payload is stored in the endpoint control.  The new unresolved
open/closed member therefore changes only the *next* initialization row; it
does not choose the child again.

No transition below receives a graph, hierarchy side, leader bit,
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

private abbrev RightMove :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
    strategy hwin

private abbrev LeftMove :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
    strategy hwin

private abbrev OldRightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev OldLeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev RightSender :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev RightReceiver :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

private abbrev LeftSender :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev LeftReceiver :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

/-! ## Full finite linked relay -/

/-- Both payload-linked table pairs. -/
noncomputable abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay :=
  (RightSender A strategy hwin × RightReceiver A strategy hwin) ×
    (LeftSender A strategy hwin × LeftReceiver A strategy hwin)

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayFintype :
    Fintype (LinkedRelay A strategy hwin) := by
  infer_instance

/-- Install the two payload-linked tables before the first record. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
    (rightMove : RightMove A strategy hwin)
    (leftMove : LeftMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) : LinkedRelay A strategy hwin :=
  ((profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A rightMove,
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A
        rightMove rightAnchor),
    (profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A leftMove,
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A leftMove
        leftAnchor))

/-- Once a receive reveals the complete input pair, advance every linked
control exactly once. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
    (relay : LinkedRelay A strategy hwin) (input : In₁ × In₂) :
    LinkedRelay A strategy hwin :=
  (((profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A relay.1.1
        input.1).2,
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A relay.1.2
        input.2 input.1).2),
    ((profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A relay.2.1
        input.2).2,
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A relay.2.2
        input.1 input.2).2))

/-! ## Arbitrary-prefix relay invariant -/

/-- A current linked right sender/receiver pair belongs to one exact semantic
occurrence over `state` at some finite prefix.  The semantic data and prefix
are proof-side witnesses; the executable relay stores neither. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
    (state : BankControl A strategy hwin)
    (sender : RightSender A strategy hwin)
    (receiver : RightReceiver A strategy hwin) : Prop :=
  ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcOnePairedEntryRep strategy × A.State),
    ∃ hmember : (family.semanticChild A direction).right () =
        some semanticMember,
      ∃ (anchor : Bool) (past : List (In₂ × In₁)),
        sender =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
              A strategy hwin state family direction semanticMember hmember
                past ∧
          receiver =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
              A strategy hwin state family direction semanticMember hmember
                anchor past

/-- Left relay mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
    (state : BankControl A strategy hwin)
    (sender : LeftSender A strategy hwin)
    (receiver : LeftReceiver A strategy hwin) : Prop :=
  ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
    ∃ hmember : (family.semanticChild A direction).left () =
        some semanticMember,
      ∃ (anchor : Bool) (past : List (In₁ × In₂)),
        sender =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
              A strategy hwin state family direction semanticMember hmember
                past ∧
          receiver =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
              A strategy hwin state family direction semanticMember hmember
                anchor past

/-- Exact right roots establish the arbitrary-prefix invariant at `[]`. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix_initial
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin state
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A move)
        (profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
          anchor) := by
  dsimp only
  refine ⟨family, direction, semanticMember, hmember, anchor, [], ?_, ?_⟩
  · rfl
  · rfl

/-- Exact left roots establish the mirror invariant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix_initial
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin state
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A move)
        (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
          anchor) := by
  dsimp only
  refine ⟨family, direction, semanticMember, hmember, anchor, [], ?_, ?_⟩
  · rfl
  · rfl

/-- One complete right block extends the proof-side prefix witness. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix.step
    {state : BankControl A strategy hwin}
    {sender : RightSender A strategy hwin}
    {receiver : RightReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin state sender receiver)
    (input : In₂ × In₁) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin state
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A sender
          input.2).2
        (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A receiver
          input.1 input.2).2 := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, rfl, rfl⟩
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, anchor,
    past ++ [input], ?_, ?_⟩
  · let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    have hlocal := finiteCrossAnchorSenderNoRecv_atPrefix move.2 past input
    simpa only [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix,
      profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv] using
      congrArg
        (fun control => (⟨move, control⟩ : RightSender A strategy hwin))
        hlocal
  · let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    have hlocal :=
      finiteCrossAnchorReceiverRecv_atPrefix move.2 anchor past input
    simpa only [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix,
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv] using
      congrArg
        (fun control => (⟨move, control⟩ : RightReceiver A strategy hwin))
        hlocal

/-- One complete left block extends its prefix witness. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix.step
    {state : BankControl A strategy hwin}
    {sender : LeftSender A strategy hwin}
    {receiver : LeftReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin state sender receiver)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin state
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A sender
          input.2).2
        (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A receiver
          input.1 input.2).2 := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, rfl, rfl⟩
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, anchor,
    past ++ [input], ?_, ?_⟩
  · let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    have hlocal := finiteCrossAnchorSenderNoRecv_atPrefix move.2 past input
    simpa only [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix,
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv] using
      congrArg
        (fun control => (⟨move, control⟩ : LeftSender A strategy hwin))
        hlocal
  · let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    have hlocal :=
      finiteCrossAnchorReceiverRecv_atPrefix move.2 anchor past input
    simpa only [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix,
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv] using
      congrArg
        (fun control => (⟨move, control⟩ : LeftReceiver A strategy hwin))
        hlocal

/-- An arbitrary locally reachable right receiver output carries a genuine
strict child of its common parent state. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix.payload_exists
    {state : BankControl A strategy hwin}
    {sender : RightSender A strategy hwin}
    {receiver : RightReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin state sender receiver)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    ∃ semanticPast semanticInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
            receiver input.1 input.2).1.target row).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) row semanticPast
                  semanticInput)) := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, _hsender,
      hreceiver⟩
  rw [hreceiver]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix_payload_exists
      A strategy hwin state family direction semanticMember hmember anchor past
        input row

/-- Left arbitrary-prefix payload mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix.payload_exists
    {state : BankControl A strategy hwin}
    {sender : LeftSender A strategy hwin}
    {receiver : LeftReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin state sender receiver)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    ∃ semanticPast semanticInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
            receiver input.1 input.2).1.target row).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) row semanticPast
                  semanticInput)) := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, _hsender,
      hreceiver⟩
  rw [hreceiver]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix_payload_exists
      A strategy hwin state family direction semanticMember hmember anchor past
        input row

/-! ## Arbitrary finite relay prefixes -/

/-- Iterate the complete linked relay over a finite physical input prefix.
The graph word is irrelevant here: the authority invariant chooses which
endpoint owns the complete relay, while every complete relay advance uses the
same delivered input pair. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
    (relay : LinkedRelay A strategy hwin) :
    List (In₁ × In₂) → LinkedRelay A strategy hwin
  | [] => relay
  | input :: inputs =>
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
          A strategy hwin relay input) inputs

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun_nil
    (relay : LinkedRelay A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
      A strategy hwin relay [] = relay :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun_cons
    (relay : LinkedRelay A strategy hwin) (input : In₁ × In₂)
    (inputs : List (In₁ × In₂)) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin relay (input :: inputs) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
            A strategy hwin relay input) inputs :=
  rfl

/-- The exact semantic right-pair witness is preserved through every finite
complete-relay prefix. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix.run
    {state : BankControl A strategy hwin}
    {relay : LinkedRelay A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin state relay.1.1 relay.1.2)
    (inputs : List (In₁ × In₂)) :
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin relay inputs
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin state next.1.1 next.1.2 := by
  induction inputs generalizing relay with
  | nil => simpa using hpair
  | cons input inputs ih =>
      apply ih
      simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
        using hpair.step A strategy hwin (input.2, input.1)

/-- Left-pair mirror of arbitrary finite relay preservation. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix.run
    {state : BankControl A strategy hwin}
    {relay : LinkedRelay A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin state relay.2.1 relay.2.2)
    (inputs : List (In₁ × In₂)) :
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin relay inputs
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin state next.2.1 next.2.2 := by
  induction inputs generalizing relay with
  | nil => simpa using hpair
  | cons input inputs ih =>
      apply ih
      simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
        using hpair.step A strategy hwin input

/-! ## Endpoint controls retaining the selected exact child -/

/-- Last output, local receive bit, full linked relay, and the exact child
selected at the most recent receive. -/
noncomputable abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl :=
  Out₁ × (Bool × (LinkedRelay A strategy hwin ×
    BankControl A strategy hwin))

noncomputable abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl :=
  Out₂ × (Bool × (LinkedRelay A strategy hwin ×
    BankControl A strategy hwin))

private abbrev OneControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev TwoControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControlFintype :
    Fintype (OneControl A strategy hwin) := by
  infer_instance

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControlFintype :
    Fintype (TwoControl A strategy hwin) := by
  infer_instance

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
    (state : BankControl A strategy hwin)
    (rightMove : RightMove A strategy hwin)
    (leftMove : LeftMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
      A strategy hwin rightMove leftMove rightAnchor leftAnchor
  ((default, (false, (relay, state))),
    (default, (false, (relay, state))))

/-- Executable reinstallation from a finite bank state: both linked tables
are obtained by the proof-generated finite rebuild lookups. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
    (state : BankControl A strategy hwin) (rightAnchor leftAnchor : Bool) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial A
    strategy hwin state (state.linkedRightMove A strategy hwin)
      (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor

/-- Retained installation immediately after a simultaneous receive.  The
inner anchors select the old `both` rows, while the outer receive bits make
the very next strict round read those rows. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
    (state : BankControl A strategy hwin) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
      A strategy hwin state true true
  ((base.1.1, (true, base.1.2.2)),
    (base.2.1, (true, base.2.2.2)))

/-! ## Checker alignment at a synchronized root -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- One strict-right record from the old `both` state is exactly the fresh
child's `first` checker coordinate. -/
theorem profiledRawJointRight_bothRootStep_eq_childFirstState
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A) Allowed source)
    (input : In₂ × In₁) :
    A.step (pairedCodeStateForRow A .both source.1.1)
        (rightRoundRecord input
          (pairedRightSenderStrategy activation.lambda [] input.2)
          (pairedRightInformedForRow .both
            (profiledRawJointTargetRightReceiverStrategy A activation [] input
              ).physical)) =
      pairedCodeStateForRow A .first
        (profiledRawRightChildSlot A source activation.lambda .both [] input
          ).1.1 := by
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- One strict-left record from the old `both` state is the mirror fresh
child's `first` checker coordinate. -/
theorem profiledRawJointLeft_bothRootStep_eq_childFirstState
    {Allowed : ProfiledRawJointUnitTarget A → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A) Allowed source)
    (input : In₁ × In₂) :
    A.step (pairedCodeStateForRow A .both source.1.1)
        (leftRoundRecord input
          (pairedLeftInformedForRow .both
            (profiledRawJointTargetLeftReceiverStrategy A activation [] input
              ).physical)
          (pairedLeftSenderStrategy activation.lambda [] input.2)) =
      pairedCodeStateForRow A .first
        (profiledRawLeftChildSlot A source activation.lambda .both [] input
          ).1.1 := by
  rfl

/-! ## Live lookup roots satisfy the arbitrary-prefix invariant -/

/-- On a live one-sided right lane, the proof-generated finite lookup installs
the root of one exact semantic occurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_rightPairAtPrefix
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
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin state relay.1.1 relay.1.2 := by
  dsimp only
  have hrebuild :=
    state.linkedRightMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, familyDirection,
      semanticMember, member_eq, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial,
    hlinked] using
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix_initial
      A strategy hwin state family familyDirection semanticMember member_eq
        rightAnchor)

/-- Left live-lane lookup root. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_leftPairAtPrefix
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
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin state relay.2.1 relay.2.2 := by
  dsimp only
  have hrebuild :=
    state.linkedLeftMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, familyDirection,
      semanticMember, member_eq, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial,
    hlinked] using
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix_initial
      A strategy hwin state family familyDirection semanticMember member_eq
        leftAnchor)

/-- After any finite complete-input prefix, the operational right receiver
from a live lookup still returns an exact child of the original bank parent. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRunOfState_right_payload_exists
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove)
    (rightAnchor leftAnchor : Bool) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin root past
    ∃ semanticPast semanticInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
            relay.1.2 input.2 input.1).1.target row).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) row semanticPast
                  semanticInput)) := by
  dsimp only
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_rightPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor
        leftAnchor
  have hpair := hroot.run A strategy hwin past
  exact hpair.payload_exists A strategy hwin (input.2, input.1) row

/-- Left operational receiver mirror after an arbitrary finite prefix. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRunOfState_left_payload_exists
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove)
    (rightAnchor leftAnchor : Bool) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial
        A strategy hwin (state.linkedRightMove A strategy hwin)
          (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayRun
        A strategy hwin root past
    ∃ semanticPast semanticInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
            relay.2.2 input.1 input.2).1.target row).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) row semanticPast
                  semanticInput)) := by
  dsimp only
  have hroot :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitialOfState_leftPairAtPrefix
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor
        leftAnchor
  have hpair := hroot.run A strategy hwin past
  exact hpair.payload_exists A strategy hwin input row

/-- The exact child currently stored by process one. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child
    (state : OneControl A strategy hwin) : BankControl A strategy hwin :=
  state.2.2.2

/-- Process-two mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child
    (state : TwoControl A strategy hwin) : BankControl A strategy hwin :=
  state.2.2.2

/-! ## Child authority at a receive -/

/-- Process one's authoritative parent mirrors the relay-base choice: after
a preceding receive it trusts its own stored child, and otherwise the
delivered partner child. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentOne
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin) :
    BankControl A strategy hwin :=
  if one.2.1 then one.child A strategy hwin else two.child A strategy hwin

/-- Process-two mirror. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentTwo
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin) :
    BankControl A strategy hwin :=
  if two.2.1 then two.child A strategy hwin else one.child A strategy hwin

/-- The exact finite invariant needed for simultaneous closing.  Equal
receive flags require equal stored children; when the flags differ, both
local authority rules definitionally select the endpoint that received.
Thus neither process needs to know a graph or strict leader. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParents_eq
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin)
    (hauthority : one.2.1 = two.2.1 →
      one.child A strategy hwin = two.child A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentOne
        A strategy hwin one two =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentTwo
        A strategy hwin one two := by
  cases hone : one.2.1 <;> cases htwo : two.2.1
  · simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentTwo,
      hone, htwo] using (hauthority (hone.trans htwo.symm)).symm
  · simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentTwo,
      hone, htwo]
  · simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentTwo,
      hone, htwo]
  · simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentTwo,
      hone, htwo] using hauthority (hone.trans htwo.symm)

/-- The closed simultaneous child computed by process one from its
authoritative parent. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothChildOne
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin)
    (input : In₁ × In₂) : BankControl A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
    hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentOne
        A strategy hwin one two)
      (.simultaneous input)

/-- Process-two computation of the same closed child. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothChildTwo
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin)
    (input : In₁ × In₂) : BankControl A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
    hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParentTwo
        A strategy hwin one two)
      (.simultaneous input)

/-- Under child authority, both local simultaneous-close computations agree
on one exact bank child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothChildren_eq
    (one : OneControl A strategy hwin) (two : TwoControl A strategy hwin)
    (hauthority : one.2.1 = two.2.1 →
      one.child A strategy hwin = two.child A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothChildOne
        A strategy hwin one two input =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothChildTwo
        A strategy hwin one two input := by
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothChildOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothChildTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedSelectedParents_eq
      A strategy hwin one two hauthority]

/-! ## Local transitions -/

/-- A blind process-one step advances the linked right sender and retains the
last exact child. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne
    (state : OneControl A strategy hwin) (input : In₁) :
    OneControl A strategy hwin :=
  let next :=
    profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
      state.2.2.1.1.1 input
  (next.1,
    (false,
      (((next.2, state.2.2.1.1.2), state.2.2.1.2), state.child A strategy hwin)))

/-- Blind process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo
    (state : TwoControl A strategy hwin) (input : In₂) :
    TwoControl A strategy hwin :=
  let next :=
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
      state.2.2.1.2.1 input
  (next.1,
    (false,
      ((state.2.2.1.1, (next.2, state.2.2.1.2.2)),
        state.child A strategy hwin)))

/-- Process one imports the locally selected complete relay, emits the left
receiver coordinate, and stores the exact payload at that same selected row. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne
    (state : OneControl A strategy hwin) (own : In₁)
    (partner : TwoControl A strategy hwin) (delivered : In₂) :
    OneControl A strategy hwin :=
  let row : PairedEntryRow := if state.2.1 then .both else .first
  let base := if state.2.1 then state.2.2.1 else partner.2.2.1
  let receiver :=
    profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A base.2.2 own
      delivered
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
      A strategy hwin base (own, delivered)
  let child :=
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
      (receiver.1.target row).1
  (pairedLeftInformedForRow row receiver.1.physical,
    (true, (relay, child)))

/-- Process-two receive mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo
    (state : TwoControl A strategy hwin) (own : In₂)
    (partner : OneControl A strategy hwin) (delivered : In₁) :
    TwoControl A strategy hwin :=
  let row : PairedEntryRow := if state.2.1 then .both else .first
  let base := if state.2.1 then state.2.2.1 else partner.2.2.1
  let receiver :=
    profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A base.1.2 own
      delivered
  let relay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
      A strategy hwin base (delivered, own)
  let child :=
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
      (receiver.1.target row).1
  (pairedRightInformedForRow row receiver.1.physical,
    (true, (relay, child)))

/-! ## The selected payload is retained by blind evolution -/

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne_child
    (state : OneControl A strategy hwin) (input : In₁) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne
        A strategy hwin state input).child A strategy hwin =
      state.child A strategy hwin :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo_child
    (state : TwoControl A strategy hwin) (input : In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo
        A strategy hwin state input).child A strategy hwin =
      state.child A strategy hwin :=
  rfl

/-! ## Graph-case test steps -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
    (state : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne
      A strategy hwin state.1 input.1,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo
      A strategy hwin state.2 input.2 state.1 input.1)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
    (state : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne
      A strategy hwin state.1 input.1 state.2 input.2,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo
      A strategy hwin state.2 input.2)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothStep
    (state : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne
      A strategy hwin state.1 input.1 state.2 input.2,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo
      A strategy hwin state.2 input.2 state.1 input.1)

/-- Local indistinguishability is definitional: process one executes the same
receive transition at a strict-left and simultaneous round. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetained_strictLeft_one_eq_both_one
    (state : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin state input).1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothStep
        A strategy hwin state input).1 :=
  rfl

/-- Process-two strict-right/simultaneous mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetained_strictRight_two_eq_both_two
    (state : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin state input).2 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedBothStep
        A strategy hwin state input).2 :=
  rfl

/-! ## One executable finite controller -/

/-- The payload-linked retained carrier in the repository's local-controller
interface.  The exact child remains an internal finite control coordinate and
is read by the surrounding deferred resolver at the next acknowledgement. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedController
    (state : BankControl A strategy hwin) (rightAnchor leftAnchor : Bool) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ where
  OneControl := OneControl A strategy hwin
  TwoControl := TwoControl A strategy hwin
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
      A strategy hwin state rightAnchor leftAnchor).1
  initialTwo :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
      A strategy hwin state rightAnchor leftAnchor).2
  noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne
      A strategy hwin
  noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo
      A strategy hwin
  recvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne A
      strategy hwin
  recvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo A
      strategy hwin
  outputOne := Prod.fst
  outputTwo := Prod.fst

/-! ## The exact child survives the first and retained second record -/

/-- At a fresh right occurrence, process two stores the exact `.first` child
carried by the linked receiver target. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRight_initial_child
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (leftMove : LeftMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let rightMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    next.2.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) .first []
                (input.2, input.1))) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child]
    using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_initial_first_payload
        A strategy hwin state family direction semanticMember hmember
          rightAnchor (input.2, input.1) .first)

/-- Repeating the same right orientation uses the retained receiver control.
The selected child is still the exact pre-narrowing payload, now at the full
one-record prefix and the acknowledged `.both` row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRight_retained_child
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (leftMove : LeftMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let rightMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin afterFirst second
    afterSecond.2.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) .both
                [(first.2, first.1)] (second.2, second.1))) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl.child]
    using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_retained_second_payload
        A strategy hwin state family direction semanticMember hmember
          rightAnchor (first.2, first.1) (second.2, second.1) .both)

/-- Fresh strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeft_initial_child
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (rightMove : RightMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let leftMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    next.1.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) .first [] input)) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child]
    using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_initial_first_payload
        A strategy hwin state family direction semanticMember hmember
          leftAnchor input .first)

/-- Repeated strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeft_retained_child
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (rightMove : RightMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let leftMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin afterFirst second
    afterSecond.1.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) .both [first] second)) := by
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl.child]
    using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_retained_second_payload
        A strategy hwin state family direction semanticMember hmember
          leftAnchor first second .both)

/-! ## Physical readback: the payload enrichment is inert -/

/-- Starting the linked retained carrier directly at a marked bank root emits
the canonical exact right seed on its first strict-right round.  Both output
coordinates come from the same preselected payload-linked table. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRoot_strictRight_initial_output
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactRightUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state false false
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    (next.1.1, next.2.1) =
      (pairedRightSenderStrategy activation.lambda [] input.1,
        pairedRightInformedForRow .first
          (profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
            activation children [] (input.2, input.1)).physical) := by
  dsimp only
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove_initial_first_pair
      A strategy hwin state false (input.2, input.1)
  have hphysical := congrArg
    (fun pair ↦ (pair.2, pairedRightInformedForRow .first pair.1.physical))
    hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_linkedRightMove_eq_fallback]
    using hphysical

/-- Direct marked-root strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRoot_strictLeft_initial_output
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactLeftUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state false false
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    (next.1.1, next.2.1) =
      (pairedLeftInformedForRow .first
          (profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
            activation children [] input).physical,
        pairedLeftSenderStrategy activation.lambda [] input.2) := by
  dsimp only
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove_initial_first_pair
      A strategy hwin state false input
  have hphysical := congrArg
    (fun pair ↦ (pairedLeftInformedForRow .first pair.1.physical, pair.2))
    hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_linkedLeftMove_eq_fallback]
    using hphysical

/-- At a synchronized common root, the first strict-right round extends the
checker state stored in the old `both` row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRoot_strictRight_initial_output
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactRightUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin state
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    (next.1.1, next.2.1) =
      (pairedRightSenderStrategy activation.lambda [] input.1,
        pairedRightInformedForRow .both
          (profiledRawJointRightFinitePayloadLinkedSiblingReceiver A
            activation children [] (input.2, input.1)).physical) := by
  dsimp only
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedRightMove_initial_first_pair
      A strategy hwin state true (input.2, input.1)
  have hphysical := congrArg
    (fun pair ↦ (pair.2, pairedRightInformedForRow .both pair.1.physical))
    hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_linkedRightMove_eq_fallback]
    using hphysical

/-- Synchronized common-root strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRoot_strictLeft_initial_output
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactLeftUniformActivation A strategy hwin
        installed
    let children :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin state
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    (next.1.1, next.2.1) =
      (pairedLeftInformedForRow .both
          (profiledRawJointLeftFinitePayloadLinkedSiblingReceiver A
            activation children [] input).physical,
        pairedLeftSenderStrategy activation.lambda [] input.2) := by
  dsimp only
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFallbackLinkedLeftMove_initial_first_pair
      A strategy hwin state true input
  have hphysical := congrArg
    (fun pair ↦ (pairedLeftInformedForRow .both pair.1.physical, pair.2))
    hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_linkedLeftMove_eq_fallback]
    using hphysical

/-- The fresh right record is exactly the original semantic occurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRight_initial_output
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (leftMove : LeftMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let rightMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    (next.1.1, next.2.1) =
      (profiledRawJointRightSiblingSender A semanticMember [] input.1,
        pairedRightInformedForRow .first
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
            A strategy hwin state
              (profiledRawJointRightPhysicalSiblingActivation A hwin family
                direction semanticMember hmember rightAnchor)
              [] (input.2, input.1)).physical) := by
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_initial_first_pair
      A strategy hwin state family direction semanticMember hmember
        rightAnchor (input.2, input.1)
  have hphysical := congrArg
    (fun pair =>
      (pair.2, pairedRightInformedForRow .first pair.1.physical)) hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo]
    using hphysical

/-- After one homogeneous right record, the augmented relay emits the exact
same semantic occurrence at prefix `[first]`. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRight_retained_output
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (leftMove : LeftMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let rightMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin afterFirst second
    (afterSecond.1.1, afterSecond.2.1) =
      (profiledRawJointRightSiblingSender A semanticMember [first.1] second.1,
        pairedRightInformedForRow .both
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
            A strategy hwin state
              (profiledRawJointRightPhysicalSiblingActivation A hwin family
                direction semanticMember hmember rightAnchor)
              [(first.2, first.1)] (second.2, second.1)).physical) := by
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_retained_second_pair
      A strategy hwin state family direction semanticMember hmember rightAnchor
        (first.2, first.1) (second.2, second.1)
  have hphysical := congrArg
    (fun pair =>
      (pair.2, pairedRightInformedForRow .both pair.1.physical)) hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hphysical

/-- Fresh left physical mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeft_initial_output
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (rightMove : RightMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let leftMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    (next.1.1, next.2.1) =
      (pairedLeftInformedForRow .first
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
            A strategy hwin state
              (profiledRawJointLeftPhysicalSiblingActivation A hwin family
                direction semanticMember hmember leftAnchor) [] input).physical,
        profiledRawJointLeftSiblingSender A semanticMember [] input.2) := by
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_initial_first_pair
      A strategy hwin state family direction semanticMember hmember leftAnchor
        input
  have hphysical := congrArg
    (fun pair =>
      (pairedLeftInformedForRow .first pair.1.physical, pair.2)) hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne]
    using hphysical

/-- Retained left physical mirror at prefix `[first]`. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeft_retained_output
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (rightMove : RightMove A strategy hwin)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let leftMove :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial
        A strategy hwin state rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin afterFirst second
    (afterSecond.1.1, afterSecond.2.1) =
      (pairedLeftInformedForRow .both
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
            A strategy hwin state
              (profiledRawJointLeftPhysicalSiblingActivation A hwin family
                direction semanticMember hmember leftAnchor) [first]
                  second).physical,
        profiledRawJointLeftSiblingSender A semanticMember [first.2]
          second.2) := by
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_retained_second_pair
      A strategy hwin state family direction semanticMember hmember leftAnchor
        first second
  have hphysical := congrArg
    (fun pair =>
      (pairedLeftInformedForRow .both pair.1.physical, pair.2)) hpair
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
    using hphysical

/-! ## Lookup-installed operational specifications -/

/-- The finite rebuild lookup exposes the exact first right child on every
reachable one-sided state with a live right lane. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictRight_child
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    next.2.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) .first []
                (input.2, input.1))) := by
  have hrebuild :=
    state.linkedRightMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, familyDirection,
      semanticMember, member_eq, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    hlinked] using
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRight_initial_child
      A strategy hwin state family familyDirection semanticMember member_eq
        (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor input)

/-- The same lookup remains exact at the retained second right record. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictRight_retained_child
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin afterFirst second
    afterSecond.2.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) .both
                [(first.2, first.1)] (second.2, second.1))) := by
  have hrebuild :=
    state.linkedRightMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, familyDirection,
      semanticMember, member_eq, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    hlinked] using
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRight_retained_child
      A strategy hwin state family familyDirection semanticMember member_eq
        (state.linkedLeftMove A strategy hwin) rightAnchor leftAnchor first
          second)

/-- Lookup-installed first left child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictLeft_child
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    next.1.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) .first [] input)) := by
  have hrebuild :=
    state.linkedLeftMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, familyDirection,
      semanticMember, member_eq, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    hlinked] using
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeft_initial_child
      A strategy hwin state family familyDirection semanticMember member_eq
        (state.linkedRightMove A strategy hwin) rightAnchor leftAnchor input)

/-- Lookup-installed retained second left child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictLeft_retained_child
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin afterFirst second
    afterSecond.1.child A strategy hwin =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) .both [first] second)) := by
  have hrebuild :=
    state.linkedLeftMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, familyDirection,
      semanticMember, member_eq, _hsource, _hannotation, _haligned, _hold,
        hlinked⟩
  simpa [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState,
    hlinked] using
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeft_retained_child
      A strategy hwin state family familyDirection semanticMember member_eq
        (state.linkedRightMove A strategy hwin) rightAnchor leftAnchor first
          second)

/-! ## The lookup-installed child is iterable -/

/-- A child extracted at a fresh right receive is again a reachable bank
state.  In particular its own proof-generated linked-table lookup is valid
when a later acknowledgement activates it. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictRight_child_reachable
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (next.2.child A strategy hwin) := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictRight_child
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        input]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable
        (.strict
          (profiledRawJointUnitRightActualDirection
            (In₁ := In₁) (In₂ := In₂) .first [] (input.2, input.1)))

/-- The retained second right row also extracts a reachable child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictRight_retained_child_reachable
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldRightMove A)
    (hmove : (state.literal A strategy hwin).1 = some oldMove)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin afterFirst second
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (afterSecond.2.child A strategy hwin) := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictRight_retained_child
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        first second]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable
        (.strict
          (profiledRawJointUnitRightActualDirection
            (In₁ := In₁) (In₂ := In₂) .both
              [(first.2, first.1)] (second.2, second.1)))

/-- Fresh left extraction preserves the bank reachability invariant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictLeft_child_reachable
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove)
    (rightAnchor leftAnchor : Bool) (input : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (next.1.child A strategy hwin) := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictLeft_child
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        input]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable
        (.strict
          (profiledRawJointUnitLeftActualDirection
            (In₁ := In₁) (In₂ := In₂) .first [] input))

/-- Retained second left extraction preserves reachability. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictLeft_retained_child_reachable
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (oldMove : OldLeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some oldMove)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState
        A strategy hwin state rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial first
    let afterSecond :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin afterFirst second
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (afterSecond.1.child A strategy hwin) := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedInitialOfState_strictLeft_retained_child
      A strategy hwin hreachable code hcode oldMove hmove rightAnchor leftAnchor
        first second]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable
        (.strict
          (profiledRawJointUnitLeftActualDirection
            (In₁ := In₁) (In₂ := In₂) .both [first] second))

end

end DetParityAutomaton

end DistributedSynthesis
