/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixCurrent
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter

/-!
# A leader-free retained carrier for the current literal tables

The four finite controls of the current right/left literal tables are kept in
one relay value.  A no-receive advances the sender controlled by the local
input.  A receive imports the partner's complete pre-round relay and advances
all four controls with the now available input pair.  Consequently, after a
strict round the informed endpoint holds the complete one-letter successor;
if the hierarchy switches, the newly informed endpoint receives precisely
that successor and continues it to the literal second record.

This is the delay-one mechanism.  Neither endpoint transition receives a
graph, orientation, leader bit, strict-leader bit, semantic source, or
history.  The runtime data are only the two finite table moves, their finite
controls, and the most recent local output.  In particular no sender is
restarted at a strict switch.

Each endpoint additionally retains the one locally observable event bit
`lastRecv`.  On another receive it advances its own relay; on a receive after
a no-receive it imports the partner's relay.  Thus repeated strict rounds and
strict switches both select the fresh copy without a leader or orientation
oracle.  A simultaneous round synchronizes both copies by the same rule.
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

private abbrev RightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev RightSender :=
  ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A

private abbrev RightReceiver :=
  ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A

private abbrev LeftSender :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A

private abbrev LeftReceiver :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A

/-! ## The finite relay and its full-input transition -/

/-- The two synchronized table pairs.  This type is executable finite data;
the pairing is only a compact representation, not a proof-side semantic
annotation. -/
noncomputable abbrev ProfiledRawJointHybridLiteralPrefixRetainedRelay :=
  (RightSender A × RightReceiver A) × (LeftSender A × LeftReceiver A)

noncomputable instance
    profiledRawJointHybridLiteralPrefixRetainedRelayFintype :
    Fintype (ProfiledRawJointHybridLiteralPrefixRetainedRelay A) := by
  infer_instance

/-- Install both current tables before a future input is known. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRelayInitial
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) :
    ProfiledRawJointHybridLiteralPrefixRetainedRelay A :=
  ((profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A rightMove,
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A rightMove
        rightAnchor),
    (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A leftMove,
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A leftMove
        leftAnchor))

/-- Advance every retained control once a receive makes the complete input
pair available. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRelayAdvance
    (relay : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedRelay A :=
  (((profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A relay.1.1
        input.1).2,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A relay.1.2
        input.2 input.1).2),
    ((profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A relay.2.1
        input.2).2,
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A relay.2.2
        input.1 input.2).2))

/-! ## Genuine endpoint-local controls -/

/-- The first component is the Moore output of the most recent local event. -/
noncomputable abbrev ProfiledRawJointHybridLiteralPrefixRetainedOneControl :=
  Out₁ × (Bool × ProfiledRawJointHybridLiteralPrefixRetainedRelay A)

noncomputable abbrev ProfiledRawJointHybridLiteralPrefixRetainedTwoControl :=
  Out₂ × (Bool × ProfiledRawJointHybridLiteralPrefixRetainedRelay A)

noncomputable instance
    profiledRawJointHybridLiteralPrefixRetainedOneControlFintype :
    Fintype (ProfiledRawJointHybridLiteralPrefixRetainedOneControl A) := by
  infer_instance

noncomputable instance
    profiledRawJointHybridLiteralPrefixRetainedTwoControlFintype :
    Fintype (ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A) := by
  infer_instance

noncomputable def profiledRawJointHybridLiteralPrefixRetainedInitial
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  let relay := profiledRawJointHybridLiteralPrefixRetainedRelayInitial A
    rightMove leftMove rightAnchor leftAnchor
  ((default, (false, relay)), (default, (false, relay)))

/-- Process one's no-receive uses and retains the current right sender. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedNoRecvOne
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A)
    (input : In₁) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A :=
  let next :=
    profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A state.2.2.1.1
      input
  (next.1, (false, ((next.2, state.2.2.1.2), state.2.2.2)))

/-- Process two's no-receive is the left-sender mirror. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo
    (state : ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (input : In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  let next :=
    profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A state.2.2.2.1
      input
  (next.1, (false, (state.2.2.1, (next.2, state.2.2.2.2))))

/-- On receipt, process one imports the partner relay, advances it completely,
and emits the left receiver coordinate. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRecvOne
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A)
    (own : In₁)
    (partner : ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (delivered : In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A :=
  let row : PairedEntryRow := if state.2.1 then .both else .first
  let base := if state.2.1 then state.2.2 else partner.2.2
  let receiver :=
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A base.2.2
      own delivered
  let relay :=
    profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A base
      (own, delivered)
  (pairedLeftInformedForRow row receiver.1.physical,
    (true, relay))

/-- Process-two receive mirror, importing process one's relay and emitting the
right receiver coordinate. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRecvTwo
    (state : ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (own : In₂)
    (partner : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A)
    (delivered : In₁) :
    ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  let row : PairedEntryRow := if state.2.1 then .both else .first
  let base := if state.2.1 then state.2.2 else partner.2.2
  let receiver :=
    profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A base.1.2
      own delivered
  let relay :=
    profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A base
      (delivered, own)
  (pairedRightInformedForRow row receiver.1.physical,
    (true, relay))

/-- The minimal relay packaged in the repository's actual local-controller
interface.  Local event dispatch is supplied by the model; no hierarchy bit
is an argument of any field. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedController
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ where
  OneControl := ProfiledRawJointHybridLiteralPrefixRetainedOneControl A
  TwoControl := ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne :=
    (profiledRawJointHybridLiteralPrefixRetainedInitial A rightMove leftMove
      rightAnchor leftAnchor).1
  initialTwo :=
    (profiledRawJointHybridLiteralPrefixRetainedInitial A rightMove leftMove
      rightAnchor leftAnchor).2
  noRecvOne := profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A
  noRecvTwo := profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A
  recvOne := profiledRawJointHybridLiteralPrefixRetainedRecvOne A
  recvTwo := profiledRawJointHybridLiteralPrefixRetainedRecvTwo A
  outputOne := Prod.fst
  outputTwo := Prod.fst

/-! ## Local graph-event steps used by the freshness audit -/

noncomputable def profiledRawJointHybridLiteralPrefixRetainedStrictRightStep
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  (profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A state.1 input.1,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo A state.2 input.2
      state.1 input.1)

noncomputable def profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  (profiledRawJointHybridLiteralPrefixRetainedRecvOne A state.1 input.1
      state.2 input.2,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A state.2 input.2)

noncomputable def profiledRawJointHybridLiteralPrefixRetainedBothStep
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  (profiledRawJointHybridLiteralPrefixRetainedRecvOne A state.1 input.1
      state.2 input.2,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo A state.2 input.2
      state.1 input.1)

/-- The right-oriented physical output generated from one synchronized relay
and a complete next input. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRightOutput
    (row : PairedEntryRow)
    (relay : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  ((profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A relay.1.1
      input.1).1,
    pairedRightInformedForRow row
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A relay.1.2
        input.2 input.1).1.physical)

/-- Left mirror. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedLeftOutput
    (row : PairedEntryRow)
    (relay : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  (pairedLeftInformedForRow row
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A relay.2.2
        input.1 input.2).1.physical,
    (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A relay.2.1
      input.2).1)

/-! ## Fail-fast freshness tests

These are kernel-reduced calculations over the actual local transition
functions.  They rule out the stale-partner bug: both repeated orientations
and all four length-three strict words advance the same literal prefix.
-/

section
omit [Inhabited In₁] [Inhabited In₂]

theorem profiledRawJointHybridLiteralPrefixRetained_RR_test
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let root := profiledRawJointHybridLiteralPrefixRetainedRelayInitial A
      rightMove leftMove rightAnchor leftAnchor
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A initial first
    let afterSecond :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A afterFirst
        second
    (afterSecond.1.1, afterSecond.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedRightOutput A
        .both
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A root first)
        second := by
  rfl

theorem profiledRawJointHybridLiteralPrefixRetained_LL_test
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let root := profiledRawJointHybridLiteralPrefixRetainedRelayInitial A
      rightMove leftMove rightAnchor leftAnchor
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A initial first
    let afterSecond :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A afterFirst
        second
    (afterSecond.1.1, afterSecond.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedLeftOutput A
        .both
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A root first)
        second := by
  rfl

theorem profiledRawJointHybridLiteralPrefixRetained_RRL_test
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second third : In₁ × In₂) :
    let root := profiledRawJointHybridLiteralPrefixRetainedRelayInitial A
      rightMove leftMove rightAnchor leftAnchor
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A initial first
    let afterSecond :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A afterFirst
        second
    let afterThird :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A afterSecond
        third
    (afterThird.1.1, afterThird.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedLeftOutput A
        .first
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A
          (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A root first)
          second) third := by
  rfl

theorem profiledRawJointHybridLiteralPrefixRetained_LLR_test
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second third : In₁ × In₂) :
    let root := profiledRawJointHybridLiteralPrefixRetainedRelayInitial A
      rightMove leftMove rightAnchor leftAnchor
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A initial first
    let afterSecond :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A afterFirst
        second
    let afterThird :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A afterSecond
        third
    (afterThird.1.1, afterThird.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedRightOutput A
        .first
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A
          (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A root first)
          second) third := by
  rfl

theorem profiledRawJointHybridLiteralPrefixRetained_RLR_test
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second third : In₁ × In₂) :
    let root := profiledRawJointHybridLiteralPrefixRetainedRelayInitial A
      rightMove leftMove rightAnchor leftAnchor
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A initial first
    let afterSecond :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A afterFirst
        second
    let afterThird :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A afterSecond
        third
    (afterThird.1.1, afterThird.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedRightOutput A
        .first
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A
          (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A root first)
          second) third := by
  rfl

theorem profiledRawJointHybridLiteralPrefixRetained_LRL_test
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second third : In₁ × In₂) :
    let root := profiledRawJointHybridLiteralPrefixRetainedRelayInitial A
      rightMove leftMove rightAnchor leftAnchor
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterFirst :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A initial first
    let afterSecond :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A afterFirst
        second
    let afterThird :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A afterSecond
        third
    (afterThird.1.1, afterThird.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedLeftOutput A
        .first
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A root first)
          second) third := by
  rfl

end

/-! ## Local indistinguishability and the unbounded authority invariant -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process one performs exactly the same receive transition in a strict-left
and a simultaneous round.  The controller is therefore local: it is not told
which of those two globally different graphs occurred. -/
@[simp] theorem
    profiledRawJointHybridLiteralPrefixRetained_strictLeft_one_eq_both_one
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (input : In₁ × In₂) :
    (profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A state
      input).1 =
      (profiledRawJointHybridLiteralPrefixRetainedBothStep A state input).1 :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process two's strict-right/simultaneous local indistinguishability
mirror. -/
@[simp] theorem
    profiledRawJointHybridLiteralPrefixRetained_strictRight_two_eq_both_two
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (input : In₁ × In₂) :
    (profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A state
      input).2 =
      (profiledRawJointHybridLiteralPrefixRetainedBothStep A state input).2 :=
  rfl

/-- The executable event dispatcher.  Its graph argument belongs to the
environment/model dispatcher, never to either endpoint-local transition. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedGraphStep
    (graph : Graph)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  match graph with
  | .right =>
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A state input
  | .left =>
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A state input
  | .both =>
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input

/-- `expected` is the fully advanced literal relay.  The first two equations
say that each blind sender always has its correct component.  The last two
say that the source selected by either endpoint's local `lastRecv` bit is
exactly the full relay.  This formulation also includes the initial state,
where both bits are false but both partner copies are complete. -/
def ProfiledRawJointHybridLiteralPrefixRetainedAuthority
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A) : Prop :=
  state.1.2.2.1.1 = expected.1.1 ∧
    state.2.2.2.2.1 = expected.2.1 ∧
    (if state.1.2.1 then state.1.2.2 else state.2.2.2) = expected ∧
    (if state.2.2.1 then state.2.2.2 else state.1.2.2) = expected

omit [Inhabited In₁] [Inhabited In₂] in
theorem profiledRawJointHybridLiteralPrefixRetainedAuthority_initial
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) :
    ProfiledRawJointHybridLiteralPrefixRetainedAuthority A
      (profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove
        leftMove rightAnchor leftAnchor)
      (profiledRawJointHybridLiteralPrefixRetainedInitial A rightMove leftMove
        rightAnchor leftAnchor) := by
  simp [ProfiledRawJointHybridLiteralPrefixRetainedAuthority,
    profiledRawJointHybridLiteralPrefixRetainedInitial]

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- One arbitrary graph event preserves the authority invariant and advances
the reference relay exactly once. -/
theorem profiledRawJointHybridLiteralPrefixRetainedAuthority_step
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (graph : Graph) (input : In₁ × In₂) :
    ProfiledRawJointHybridLiteralPrefixRetainedAuthority A
      (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected input)
      (profiledRawJointHybridLiteralPrefixRetainedGraphStep A graph state
        input) := by
  rcases hauthority with ⟨hright, hleft, hone, htwo⟩
  cases graph <;>
    simp only [profiledRawJointHybridLiteralPrefixRetainedGraphStep] <;>
    simp [ProfiledRawJointHybridLiteralPrefixRetainedAuthority,
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep,
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep,
      profiledRawJointHybridLiteralPrefixRetainedBothStep,
      profiledRawJointHybridLiteralPrefixRetainedNoRecvOne,
      profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo,
      profiledRawJointHybridLiteralPrefixRetainedRecvOne,
      profiledRawJointHybridLiteralPrefixRetainedRecvTwo,
      profiledRawJointHybridLiteralPrefixRetainedRelayAdvance,
      hright, hleft, hone, htwo]

/-- The first endpoint's receive uses the fresh row exactly after a local
no-receive, and the continued row exactly after a local receive.  Under the
authority invariant its chosen relay is the common reference relay. -/
theorem profiledRawJointHybridLiteralPrefixRetainedRecvOne_authority_output
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (input : In₁ × In₂) :
    (profiledRawJointHybridLiteralPrefixRetainedRecvOne A state.1 input.1
      state.2 input.2).1 =
      pairedLeftInformedForRow
        (if state.1.2.1 then .both else .first)
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
          expected.2.2 input.1 input.2).1.physical := by
  rcases hauthority with ⟨_hright, _hleft, hone, _htwo⟩
  simp [profiledRawJointHybridLiteralPrefixRetainedRecvOne, hone]

/-- Process-two mirror. -/
theorem profiledRawJointHybridLiteralPrefixRetainedRecvTwo_authority_output
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (input : In₁ × In₂) :
    (profiledRawJointHybridLiteralPrefixRetainedRecvTwo A state.2 input.2
      state.1 input.1).1 =
      pairedRightInformedForRow
        (if state.2.2.1 then .both else .first)
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
          expected.1.2 input.2 input.1).1.physical := by
  rcases hauthority with ⟨_hright, _hleft, _hone, htwo⟩
  simp [profiledRawJointHybridLiteralPrefixRetainedRecvTwo, htwo]

/-- Exact right-round output for an arbitrary authoritative state. -/
theorem profiledRawJointHybridLiteralPrefixRetainedStrictRight_authority_output
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedStrictRightStep A state input
    (next.1.1, next.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedRightOutput A
        (if state.2.2.1 then .both else .first) expected input := by
  rcases hauthority with ⟨hright, _hleft, _hone, htwo⟩
  simp [profiledRawJointHybridLiteralPrefixRetainedStrictRightStep,
    profiledRawJointHybridLiteralPrefixRetainedRightOutput,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvOne,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo, hright, htwo]

/-- Exact left-round mirror. -/
theorem profiledRawJointHybridLiteralPrefixRetainedStrictLeft_authority_output
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep A state input
    (next.1.1, next.2.1) =
      profiledRawJointHybridLiteralPrefixRetainedLeftOutput A
        (if state.1.2.1 then .both else .first) expected input := by
  rcases hauthority with ⟨_hright, hleft, hone, _htwo⟩
  simp [profiledRawJointHybridLiteralPrefixRetainedStrictLeftStep,
    profiledRawJointHybridLiteralPrefixRetainedLeftOutput,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo,
    profiledRawJointHybridLiteralPrefixRetainedRecvOne, hleft, hone]

/-- A simultaneous round uses the same two local receive rows.  Each row is
computed solely from that endpoint's preceding local event bit. -/
theorem profiledRawJointHybridLiteralPrefixRetainedBoth_authority_output
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input
    (next.1.1, next.2.1) =
      (pairedLeftInformedForRow
          (if state.1.2.1 then .both else .first)
          (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
            expected.2.2 input.1 input.2).1.physical,
        pairedRightInformedForRow
          (if state.2.2.1 then .both else .first)
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
            expected.1.2 input.2 input.1).1.physical) := by
  rcases hauthority with ⟨_hright, _hleft, hone, htwo⟩
  simp [profiledRawJointHybridLiteralPrefixRetainedBothStep,
    profiledRawJointHybridLiteralPrefixRetainedRecvOne,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo, hone, htwo]

end

/-- Execute an arbitrary finite graph/input word. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRun
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A) :
    List (Graph × (In₁ × In₂)) →
      ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
        ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A
  | [] => state
  | event :: events =>
      profiledRawJointHybridLiteralPrefixRetainedRun
        (profiledRawJointHybridLiteralPrefixRetainedGraphStep A event.1 state
          event.2) events

/-- Reference fold of the same word, forgetting only its graphs. -/
noncomputable def profiledRawJointHybridLiteralPrefixRetainedRelayRun
    (relay : ProfiledRawJointHybridLiteralPrefixRetainedRelay A) :
    List (Graph × (In₁ × In₂)) →
      ProfiledRawJointHybridLiteralPrefixRetainedRelay A
  | [] => relay
  | event :: events =>
      profiledRawJointHybridLiteralPrefixRetainedRelayRun
        (profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A relay
          event.2) events

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The authority calculation is not bounded to the fail-fast test depth: it
holds for every finite prefix of every `right`/`left`/`both` graph word. -/
theorem profiledRawJointHybridLiteralPrefixRetainedAuthority_run
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (events : List (Graph × (In₁ × In₂))) :
    ProfiledRawJointHybridLiteralPrefixRetainedAuthority A
      (profiledRawJointHybridLiteralPrefixRetainedRelayRun A expected events)
      (profiledRawJointHybridLiteralPrefixRetainedRun A state events) := by
  induction events generalizing expected state with
  | nil => exact hauthority
  | cons event events ih =>
      apply ih
      exact profiledRawJointHybridLiteralPrefixRetainedAuthority_step A
        expected state hauthority event.1 event.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- In particular, after a simultaneous round both endpoint copies are the
same fully advanced relay and both local event bits are `true`. -/
theorem profiledRawJointHybridLiteralPrefixRetainedBoth_synchronizes
    (expected : ProfiledRawJointHybridLiteralPrefixRetainedRelay A)
    (state : ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A)
    (hauthority :
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A expected state)
    (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridLiteralPrefixRetainedBothStep A state input
    next.1.2.1 = true ∧ next.2.2.1 = true ∧
      next.1.2.2 =
        profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected
          input ∧
      next.2.2.2 =
        profiledRawJointHybridLiteralPrefixRetainedRelayAdvance A expected
          input := by
  rcases hauthority with ⟨_hright, _hleft, hone, htwo⟩
  simp [profiledRawJointHybridLiteralPrefixRetainedBothStep,
    profiledRawJointHybridLiteralPrefixRetainedRecvOne,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo, hone, htwo]

/-! ## The two dangerous alternating-strict calculations -/

omit [Inhabited In₁] [Inhabited In₂] in
/-- After a strict-right first round, process two carries the full one-letter
relay.  A strict-left switch therefore advances the left receiver and left
sender from the same retained one-letter controls. -/
theorem profiledRawJointHybridLiteralPrefixRetained_right_left_controls
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterRight :=
      (profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A initial.1
          first.1,
        profiledRawJointHybridLiteralPrefixRetainedRecvTwo A initial.2 first.2
          initial.1 first.1)
    let afterLeft :=
      (profiledRawJointHybridLiteralPrefixRetainedRecvOne A afterRight.1
          second.1 afterRight.2 second.2,
        profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A afterRight.2
          second.2)
    (afterLeft.1.1, afterLeft.2.1) =
      (pairedLeftInformedForRow .first
          (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
            (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
              (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
                leftMove leftAnchor) first.1 first.2).2 second.1
                second.2).1.physical,
        (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
          (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
            (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A
              leftMove) first.2).2 second.2).1) := by
  rfl

omit [Inhabited In₁] [Inhabited In₂] in
/-- Mirror calculation for a strict-left round followed by strict-right. -/
theorem profiledRawJointHybridLiteralPrefixRetained_left_right_controls
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterLeft :=
      (profiledRawJointHybridLiteralPrefixRetainedRecvOne A initial.1 first.1
          initial.2 first.2,
        profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A initial.2
          first.2)
    let afterRight :=
      (profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A afterLeft.1
          second.1,
        profiledRawJointHybridLiteralPrefixRetainedRecvTwo A afterLeft.2
          second.2 afterLeft.1 second.1)
    (afterRight.1.1, afterRight.2.1) =
      ((profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
          (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
            (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A
              rightMove) first.1).2 second.1).1,
        pairedRightInformedForRow .first
          (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
            (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
              (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
                rightMove rightAnchor) first.2 first.1).2 second.2
                second.1).1.physical) := by
  rfl

/-! ## Semantic readback of the switch records -/

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-- For a recurring left table, the physical output at a right-to-left
strict switch is exactly the physical projection of that semantic table's
second literal record. -/
theorem
    profiledRawJointHybridLiteralPrefixRetained_right_left_eq_left_second
    (rightMove : RightMove A)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let leftMove := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin
      family direction semanticMember hmember
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterRight :=
      (profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A initial.1
          first.1,
        profiledRawJointHybridLiteralPrefixRetainedRecvTwo A initial.2 first.2
          initial.1 first.1)
    let afterLeft :=
      (profiledRawJointHybridLiteralPrefixRetainedRecvOne A afterRight.1
          second.1 afterRight.2 second.2,
        profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A afterRight.2
          second.2)
    (afterLeft.1.1, afterLeft.2.1) =
      (pairedLeftInformedForRow .first
          (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
            semanticMember hmember leftAnchor [first] second).physical,
        profiledRawJointLeftSiblingSender A semanticMember [first.2]
          second.2) := by
  let leftMove := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin
    family direction semanticMember hmember
  have hcontrols :=
    profiledRawJointHybridLiteralPrefixRetained_right_left_controls A rightMove
      leftMove rightAnchor leftAnchor first second
  have hsemantic :=
    profiledRawJointLeftLiteralPrefixMoveOf_retained_second_pair A strategy hwin
      family direction semanticMember hmember leftAnchor first second
  have hphysical := congrArg
    (fun pair =>
      (pairedLeftInformedForRow .first pair.1.physical, pair.2))
    hsemantic
  exact hcontrols.trans hphysical

/-- Recurring right-table mirror. -/
theorem
    profiledRawJointHybridLiteralPrefixRetained_left_right_eq_right_second
    (leftMove : LeftMove A)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let rightMove := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin
      family direction semanticMember hmember
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterLeft :=
      (profiledRawJointHybridLiteralPrefixRetainedRecvOne A initial.1 first.1
          initial.2 first.2,
        profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A initial.2
          first.2)
    let afterRight :=
      (profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A afterLeft.1
          second.1,
        profiledRawJointHybridLiteralPrefixRetainedRecvTwo A afterLeft.2
          second.2 afterLeft.1 second.1)
    (afterRight.1.1, afterRight.2.1) =
      (profiledRawJointRightSiblingSender A semanticMember [first.1] second.1,
        pairedRightInformedForRow .first
          (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
            semanticMember hmember rightAnchor [(first.2, first.1)]
              (second.2, second.1)).physical) := by
  let rightMove := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin
    family direction semanticMember hmember
  have hcontrols :=
    profiledRawJointHybridLiteralPrefixRetained_left_right_controls A rightMove
      leftMove rightAnchor leftAnchor first second
  have hsemantic :=
    profiledRawJointRightLiteralPrefixMoveOf_retained_second_pair A strategy
      hwin family direction semanticMember hmember rightAnchor
        (first.2, first.1) (second.2, second.1)
  have hphysical := congrArg
    (fun pair =>
      (pair.2,
        pairedRightInformedForRow .first pair.1.physical))
    hsemantic
  exact hcontrols.trans hphysical

/-! ## Seed readback of the switch records -/

/-- At the initial common world, a right-to-left strict switch reads back the
second record of the left seed selected before either input was known. -/
theorem
    profiledRawJointHybridLiteralPrefixRetained_right_left_seed_eq_left_second
    (rightMove : RightMove A)
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let leftMove :=
      profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin world
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterRight :=
      (profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A initial.1
          first.1,
        profiledRawJointHybridLiteralPrefixRetainedRecvTwo A initial.2 first.2
          initial.1 first.1)
    let afterLeft :=
      (profiledRawJointHybridLiteralPrefixRetainedRecvOne A afterRight.1
          second.1 afterRight.2 second.2,
        profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A afterRight.2
          second.2)
    (afterLeft.1.1, afterLeft.2.1) =
      (pairedLeftInformedForRow .first
          ((profiledRawJointTargetLeftReceiverStrategy A
            (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
              (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
                world))) [first] second).physical,
        pairedLeftSenderStrategy
          (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world)).lambda [first.2] second.2) := by
  let leftMove :=
    profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin world
  have hcontrols :=
    profiledRawJointHybridLiteralPrefixRetained_right_left_controls A rightMove
      leftMove rightAnchor leftAnchor first second
  have hsemantic :=
    profiledRawJointHybridLeftLiteralPrefixSeed_retained_second A strategy hwin
      world leftAnchor first second
  have hphysical := congrArg
    (fun pair =>
      (pairedLeftInformedForRow .first pair.1.physical, pair.2))
    hsemantic
  exact hcontrols.trans hphysical

/-- Initial-world mirror: a left-to-right switch reads back the second right
seed record. -/
theorem
    profiledRawJointHybridLiteralPrefixRetained_left_right_seed_eq_right_second
    (leftMove : LeftMove A)
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (rightAnchor leftAnchor : Bool) (first second : In₁ × In₂) :
    let rightMove :=
      profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin world
    let initial := profiledRawJointHybridLiteralPrefixRetainedInitial A
      rightMove leftMove rightAnchor leftAnchor
    let afterLeft :=
      (profiledRawJointHybridLiteralPrefixRetainedRecvOne A initial.1 first.1
          initial.2 first.2,
        profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A initial.2
          first.2)
    let afterRight :=
      (profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A afterLeft.1
          second.1,
        profiledRawJointHybridLiteralPrefixRetainedRecvTwo A afterLeft.2
          second.2 afterLeft.1 second.1)
    (afterRight.1.1, afterRight.2.1) =
      (pairedRightSenderStrategy
          (profiledRawJointHybridExactRightUniformActivation A strategy hwin
            (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
              world)).lambda [first.1] second.1,
        pairedRightInformedForRow .first
          ((profiledRawJointTargetRightReceiverStrategy A
            (profiledRawJointHybridExactRightUniformActivation A strategy hwin
              (profiledRawJointHybridLiteralPrefixSeedInstalled A strategy
                world))) [(first.2, first.1)]
                  (second.2, second.1)).physical) := by
  let rightMove :=
    profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin world
  have hcontrols :=
    profiledRawJointHybridLiteralPrefixRetained_left_right_controls A rightMove
      leftMove rightAnchor leftAnchor first second
  have hsemantic :=
    profiledRawJointHybridRightLiteralPrefixSeed_retained_second A strategy hwin
      world rightAnchor (first.2, first.1) (second.2, second.1)
  have hphysical := congrArg
    (fun pair =>
      (pair.2,
        pairedRightInformedForRow .first pair.1.physical))
    hsemantic
  exact hcontrols.trans hphysical

end

end DetParityAutomaton

end DistributedSynthesis
