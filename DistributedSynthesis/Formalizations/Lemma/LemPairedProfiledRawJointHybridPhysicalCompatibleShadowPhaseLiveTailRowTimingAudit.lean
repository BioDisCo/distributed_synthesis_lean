/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSwitchOutputCouplingPreservationAudit

/-!
# Row timing at phase-live tail successors

The outer pending member is delayed state.  It is not an observation of the
current graph.  This file exposes the exact row facts needed by a repaired
switch-output contract:

* an open (`false`) freshly installed receiver always has row `.first`;
* a closed (`true`) freshly installed receiver has row `.both` whenever the
  receiver is live (as it is on the tracked semantic run);
* receiver steps retain the row of the previously selected receiver.

In particular, a strict successor has one fresh `.first` side and one
continued side.  It is therefore unsound to hard-code `.both` on both sides of
the old phase-switch contract.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

private abbrev RightOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy hwin tag

private abbrev LeftOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy hwin tag

private abbrev RightReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin tag

private abbrev LeftReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag

/-! ## Generic fresh-receiver rows -/

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver_row_false_ofOutput
    (tag : Tag A strategy hwin)
    (output : RightOutput A strategy hwin tag) (entryRow : PairedEntryRow) :
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
          hwin tag
          (profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput
            A strategy hwin tag output entryRow) false) = .first := by
  cases hmove :
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (output.target entryRow).1).1.2.2 <;>
    simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow,
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver,
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver,
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver_row_false_ofOutput
    (tag : Tag A strategy hwin)
    (output : LeftOutput A strategy hwin tag) (entryRow : PairedEntryRow) :
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
          hwin tag
          (profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
            strategy hwin tag output entryRow) false) = .first := by
  cases hmove :
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (output.target entryRow).1).1.2.1 <;>
    simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow,
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver,
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver,
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]

/-- A closed fresh left receiver has row `.both` as soon as it is live.  The
separate liveness premise is necessary because the totalized absent receiver
has default row `.first`. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver_row_true_of_live
    (tag : Tag A strategy hwin)
    (output : RightOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (hlive :
      (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
        hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
          strategy hwin tag output entryRow) true).2 ≠ none) :
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
          hwin tag
          (profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput
            A strategy hwin tag output entryRow) true) = .both := by
  simp only [profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver,
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver,
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput] at hlive ⊢
  simp only [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow]
  cases hmove :
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (output.target entryRow).1).1.2.2 with
  | none =>
      simp [profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove] at hlive
  | some move =>
      simp [profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]

/-- Right mirror of the live closed-row fact. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver_row_true_of_live
    (tag : Tag A strategy hwin)
    (output : LeftOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (hlive :
      (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
        hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
          strategy hwin tag output entryRow) true).2 ≠ none) :
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
          hwin tag
          (profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
            strategy hwin tag output entryRow) true) = .both := by
  simp only [profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver,
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver,
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput] at hlive ⊢
  simp only [profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow]
  cases hmove :
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (output.target entryRow).1).1.2.1 with
  | none =>
      simp [profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove] at hlive
  | some move =>
      simp [profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]

/-! ## Continued receivers preserve their previous row -/

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep_row
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag) (input : In₂ × In₁) :
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy
          hwin tag fallback owner receiver input).2 =
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag receiver := by
  rcases owner with ⟨ownerState, ownerShared⟩
  rcases receiver with ⟨receiverState, receiverPayload⟩
  by_cases hstate : receiverState = ownerState
  · subst receiverState
    cases ownerShared with
    | inl dormant =>
        simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep,
          profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow]
    | inr installed =>
        rcases installed with ⟨ownerMove, ownerControl⟩
        cases receiverPayload with
        | none =>
            simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep,
              profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow]
        | some retained =>
            rcases retained with ⟨receiverMove, row, monitorState, staged⟩
            by_cases hmove : receiverMove = ownerMove
            · subst receiverMove
              simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep,
                profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor,
                profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow]
            · simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep,
                profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow,
                hmove]
  · simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow, hstate]

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep_row
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy
          hwin tag fallback owner receiver input).2 =
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
        tag receiver := by
  rcases owner with ⟨ownerState, ownerShared⟩
  rcases receiver with ⟨receiverState, receiverPayload⟩
  by_cases hstate : receiverState = ownerState
  · subst receiverState
    cases ownerShared with
    | inl dormant =>
        simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep,
          profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow]
    | inr installed =>
        rcases installed with ⟨ownerMove, ownerControl⟩
        cases receiverPayload with
        | none =>
            simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep,
              profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow]
        | some retained =>
            rcases retained with ⟨receiverMove, row, monitorState, staged⟩
            by_cases hmove : receiverMove = ownerMove
            · subst receiverMove
              simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep,
                profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor,
                profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow]
            · simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep,
                profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow,
                hmove]
  · simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow, hstate]

/-- A tracked right receiver is present; this is the semantic side condition
which turns a totalized closed receiver's requested row into the exact row
`.both`. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.receiver_live
    {tag : Tag A strategy hwin} {owner : RightOwner A strategy hwin tag}
    {receiver : RightReceiver A strategy hwin tag}
    (htracked :
      ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
        owner receiver) :
    receiver.2 ≠ none := by
  rcases htracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, _⟩
  rw [hreceiver]
  simp

/-- Left mirror. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.receiver_live
    {tag : Tag A strategy hwin} {owner : LeftOwner A strategy hwin tag}
    {receiver : LeftReceiver A strategy hwin tag}
    (htracked :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
        owner receiver) :
    receiver.2 ≠ none := by
  rcases htracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, _⟩
  rw [hreceiver]
  simp

/-! ## Strict and simultaneous successor selectors -/

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext_freshLeftRow
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag next.1 next.2) = .first := by
  simp [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext,
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
    profiledRawJointHybridShadowPhaseLiveTailOnePendingStep,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
    profiledRawJointHybridShadowPhaseLiveTailFreshPair]

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext_freshRightRow
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag next.2 next.1) = .first := by
  simp [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext,
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
    profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
    profiledRawJointHybridShadowPhaseLiveTailFreshPair]

/-- In a strict-right successor the right table is continued: its effective
row is exactly the row already selected before the transition. -/
@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext_continuedRightRow
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag next.2 next.1) =
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one) := by
  dsimp only
  simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext,
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
    profiledRawJointHybridShadowPhaseLiveTailFreshPair,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh] using
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep_row A strategy
        hwin tag fallbackRight one.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag two one) (input.2, input.1))

/-- Strict-left mirror. -/
@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext_continuedLeftRow
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag next.1 next.2) =
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two) := by
  dsimp only
  simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext,
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
    profiledRawJointHybridShadowPhaseLiveTailFreshPair,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh] using
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep_row A strategy
        hwin tag fallbackLeft two.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag one two) input)

/-- On the tracked semantic run, simultaneous close selects the live closed
candidate on both endpoints, hence both effective rows are `.both`.

The tracked premise is essential: malformed totalized states may contain no
receiver, whose total row accessor deliberately defaults to `.first`. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext_closedRows
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin
        tag fallbackLeft fallbackRight one two input
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag next.1 next.2) = .both ∧
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
          tag
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag next.2 next.1) = .both := by
  dsimp only
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s} A strategy hwin tag fallbackLeft
        fallbackRight one two input
  have hnext :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag fresh.1.1.closedControl fresh.1.2.closedControl := by
    exact
      profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_trackedInvariant
        A strategy hwin tag fallbackLeft fallbackRight one two input hinvariant
  have hleftTracked := hnext.left_selected A strategy hwin
  have hrightTracked := hnext.right_selected A strategy hwin
  have hleftLive := hleftTracked.receiver_live A strategy hwin
  have hrightLive := hrightTracked.receiver_live A strategy hwin
  have hleftRow :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver_row_true_of_live
      A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshRightResult A strategy
          hwin tag fallbackRight one two input).1
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy
          hwin tag
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag two one))
        (by
          simpa [fresh,
            profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
            profiledRawJointHybridShadowPhaseLiveTailFreshPair,
            FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh] using
              hleftLive)
  have hrightRow :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver_row_true_of_live
      A strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult A strategy
          hwin tag fallbackLeft one two input).1
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
          tag
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag one two))
        (by
          simpa [fresh,
            profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
            profiledRawJointHybridShadowPhaseLiveTailFreshPair,
            FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh] using
              hrightLive)
  constructor
  · simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh] using hleftRow
  · simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh] using hrightRow

end

end DetParityAutomaton

end DistributedSynthesis
