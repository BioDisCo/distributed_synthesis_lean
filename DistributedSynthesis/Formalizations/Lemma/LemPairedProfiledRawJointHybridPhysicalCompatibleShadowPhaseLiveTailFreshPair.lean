/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSingleTablePendingBoth

/-!
# Fresh phase-live controls in one delivered-tag tail fibre

This is the tag-relative state constructor paired with the single-live-table
output seam.  It advances both locally meaningful receiver candidates, stages
their exact successor keys, and builds the open/closed deferred forks for the
next round.  Its physical output pair is *not* assembled from those two
hypothetical records: it is the one-table pair selected by the old public
phase bit.

Every definition is finite and local.  No graph, orientation, leader bit,
strict-leader bit, history, or semantic view is an executable argument.
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

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

private abbrev RightOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy hwin
    tag

private abbrev LeftOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy hwin
    tag

private abbrev RightReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin tag

private abbrev LeftReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

private abbrev OneShared (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin tag

private abbrev TwoShared (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin tag

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

/-! ## Total receiver rows and steps -/

def profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow
    (tag : Tag A strategy hwin) (receiver : RightReceiver A strategy hwin tag) :
    PairedEntryRow :=
  match receiver.2 with
  | none => .first
  | some retained => retained.2.1

def profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow
    (tag : Tag A strategy hwin) (receiver : LeftReceiver A strategy hwin tag) :
    PairedEntryRow :=
  match receiver.2 with
  | none => .first
  | some retained => retained.2.1

/-- Total right receiver update.  Alignment proves that the live branch is
taken on the semantic trace. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag) (input : In₂ × In₁) :
    RightOutput A strategy hwin tag × RightReceiver A strategy hwin tag := by
  classical
  rcases owner with ⟨ownerState, ownerShared⟩
  rcases receiver with ⟨receiverState, receiverPayload⟩
  by_cases hstate : receiverState = ownerState
  · subst receiverState
    cases ownerShared with
    | inl _ => exact (fallback, ⟨ownerState, receiverPayload⟩)
    | inr installed =>
        rcases installed with ⟨ownerMove, ownerControl⟩
        cases receiverPayload with
        | none => exact (fallback, ⟨ownerState, none⟩)
        | some retained =>
            rcases retained with
              ⟨receiverMove, row, monitorState, staged⟩
            by_cases hmove : receiverMove = ownerMove
            · subst receiverMove
              exact
                profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
                  strategy hwin tag ownerState ownerMove ownerControl row
                    monitorState input
            · exact
                (fallback,
                  ⟨ownerState,
                    some ⟨receiverMove, row, monitorState, staged⟩⟩)
  · exact (fallback, ⟨receiverState, receiverPayload⟩)

/-- Left mirror. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag) (input : In₁ × In₂) :
    LeftOutput A strategy hwin tag × LeftReceiver A strategy hwin tag := by
  classical
  rcases owner with ⟨ownerState, ownerShared⟩
  rcases receiver with ⟨receiverState, receiverPayload⟩
  by_cases hstate : receiverState = ownerState
  · subst receiverState
    cases ownerShared with
    | inl _ => exact (fallback, ⟨ownerState, receiverPayload⟩)
    | inr installed =>
        rcases installed with ⟨ownerMove, ownerControl⟩
        cases receiverPayload with
        | none => exact (fallback, ⟨ownerState, none⟩)
        | some retained =>
            rcases retained with
              ⟨receiverMove, row, monitorState, staged⟩
            by_cases hmove : receiverMove = ownerMove
            · subst receiverMove
              exact
                profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
                  strategy hwin tag ownerState ownerMove ownerControl row
                    monitorState input
            · exact
                (fallback,
                  ⟨ownerState,
                    some ⟨receiverMove, row, monitorState, staged⟩⟩)
  · exact (fallback, ⟨receiverState, receiverPayload⟩)

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep_live
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State)
    (staged : Option (RightOutput A strategy hwin tag)) (input : In₂ × In₁) :
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
        tag fallback ⟨state, .inr ⟨move, ownerControl⟩⟩
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ input =
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move ownerControl row monitorState input := by
  simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep]

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep_live
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (staged : Option (LeftOutput A strategy hwin tag)) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
        tag fallback ⟨state, .inr ⟨move, ownerControl⟩⟩
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ input =
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move ownerControl row monitorState input := by
  simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep]

/-! ## Exact successor-key installations -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner
    (tag : Tag A strategy hwin) (_parent : RightOwner A strategy hwin tag)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy
        hwin tag) : RightOwner A strategy hwin tag :=
  let target :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadTarget A strategy
      hwin tag payload false
  let state :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy hwin
      target
  ⟨state,
    profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial A strategy hwin
      tag state⟩

noncomputable def profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner
    (tag : Tag A strategy hwin) (_parent : LeftOwner A strategy hwin tag)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
        hwin tag) : LeftOwner A strategy hwin tag :=
  let target :=
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadTarget A
      strategy hwin tag payload false
  let state :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy hwin
      target
  ⟨state,
    profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial A strategy hwin
      tag state⟩

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver
    (tag : Tag A strategy hwin)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy
        hwin tag) (member : Bool) : RightReceiver A strategy hwin tag :=
  let target :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadTarget A strategy
      hwin tag payload member
  ⟨profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
      hwin target,
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver A
      strategy hwin tag payload member⟩

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver
    (tag : Tag A strategy hwin)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
        hwin tag) (member : Bool) : LeftReceiver A strategy hwin tag :=
  let target :=
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadTarget A
      strategy hwin tag payload member
  ⟨profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
      hwin target,
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver A
      strategy hwin tag payload member⟩

/-! ## Phase-selected current receivers -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo
    (tag : Tag A strategy hwin) (two : TwoPending A strategy hwin tag)
    (one : OnePending A strategy hwin tag) : RightReceiver A strategy hwin tag :=
  if two.2.1.localPhase then
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy hwin
      tag one.2.1.basePayload one.1
  else
    two.2.1.receiver two.1

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : LeftReceiver A strategy hwin tag :=
  if one.2.1.localPhase then
    one.2.1.receiver one.1
  else
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy hwin
      tag two.2.1.basePayload two.1

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRecvTwoRight
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (two : TwoPending A strategy hwin tag)
    (one : OnePending A strategy hwin tag) (input : In₂ × In₁) :=
  profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin tag
    fallback one.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
        strategy hwin tag two one) input

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRecvOneLeft
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :=
  profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin tag
    fallback two.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
        strategy hwin tag one two) input

/-- The exact left result used by the paired fresh constructor. -/
noncomputable abbrev
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :=
  profiledRawJointHybridShadowPhaseLiveTailRecvOneLeft A strategy hwin tag
    fallbackLeft one two input

/-- The exact right result used by the paired fresh constructor. -/
noncomputable abbrev
    profiledRawJointHybridShadowPhaseLiveTailFreshRightResult
    (tag : Tag A strategy hwin)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :=
  profiledRawJointHybridShadowPhaseLiveTailRecvTwoRight A strategy hwin tag
    fallbackRight two one (input.2, input.1)

/-- Process one's exact next pending payload, staged by the left result. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailFreshOnePayload
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :=
  let receiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let result :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult A strategy hwin tag
      fallbackLeft one two input
  profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A strategy
    hwin tag result.1
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
        tag receiver)

/-- Process-two mirror, staged by the right result. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailFreshTwoPayload
    (tag : Tag A strategy hwin)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :=
  let receiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let result :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRightResult A strategy hwin
      tag fallbackRight one two input
  profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
    strategy hwin tag result.1
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag receiver)

/-! ## One paired fresh-state computation -/

abbrev ProfiledRawJointHybridShadowPhaseLiveTailFreshPairResult
    (tag : Tag A strategy hwin) :=
  (FiniteDelayedFork (OnePending A strategy hwin tag) ×
      FiniteDelayedFork (TwoPending A strategy hwin tag)) ×
    (Out₁ × Out₂)

/-- Advance both candidate receivers and stage both exact successor keys, but
take the current physical output pair from one phase-selected live table. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailFreshPair
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTailFreshPairResult A strategy hwin
      tag :=
  let leftReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let rightReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let leftResult :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
      tag fallbackLeft two.2.1.baseShared leftReceiver input
  let rightResult :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
      tag fallbackRight one.2.1.baseShared rightReceiver (input.2, input.1)
  let leftRow :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
      leftReceiver
  let rightRow :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
      tag rightReceiver
  let onePayload :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
      strategy hwin tag leftResult.1 leftRow
  let twoPayload :=
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
      strategy hwin tag rightResult.1 rightRow
  let rightOwner :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner A strategy hwin tag
      one.2.1.baseShared onePayload
  let leftOwner :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner A strategy hwin tag
      two.2.1.baseShared twoPayload
  let closedLeft :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy hwin
      tag twoPayload true
  let closedRight :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy hwin
      tag onePayload true
  let oneShared : OneShared A strategy hwin tag :=
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh rightOwner onePayload
      true leftResult.2 closedLeft
  let twoShared : TwoShared A strategy hwin tag :=
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh leftOwner twoPayload
      false rightResult.2 closedRight
  ((⟨( false, oneShared, PUnit.unit), (true, oneShared, PUnit.unit)⟩,
    ⟨(false, twoShared, PUnit.unit), (true, twoShared, PUnit.unit)⟩),
   (profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne A strategy
      hwin tag fallbackLeft fallbackRight one input.1 two input.2,
    profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo A strategy
      hwin tag fallbackLeft fallbackRight two input.2 one input.1))

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailFreshPair_one_phase
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    (((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.1.candidate member).2.1
        ).localPhase = true := by
  cases member <;> rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailFreshPair_two_phase
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    (((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.2.candidate member).2.1
        ).localPhase = false := by
  cases member <;> rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTailFreshPair_output
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).2 =
      (profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne A strategy
        hwin tag fallbackLeft fallbackRight one input.1 two input.2,
       profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo A strategy
        hwin tag fallbackLeft fallbackRight two input.2 one input.1) := by
  rfl

/-! ## Exact candidate states

These two equations intentionally expose the complete next pending values.
They let the trace invariant reason in the generic controller's natural
open/closed-candidate form without unfolding either acknowledgement relays or
the fresh constructor. -/

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_one_candidate
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input).1.1.candidate member =
      let leftReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two
      let rightReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one
      let leftResult :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy
          hwin tag fallbackLeft two.2.1.baseShared leftReceiver input
      let rightResult :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy
          hwin tag fallbackRight one.2.1.baseShared rightReceiver
            (input.2, input.1)
      let leftRow :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
          tag leftReceiver
      let rightRow :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy
          hwin tag rightReceiver
      let onePayload :=
        profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
          strategy hwin tag leftResult.1 leftRow
      let twoPayload :=
        profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
          strategy hwin tag rightResult.1 rightRow
      let rightOwner :=
        profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner A strategy hwin
          tag one.2.1.baseShared onePayload
      let closedLeft :=
        profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
          hwin tag twoPayload true
      (member,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh rightOwner
          onePayload true leftResult.2 closedLeft,
        PUnit.unit) := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_two_candidate
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input).1.2.candidate member =
      let leftReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two
      let rightReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one
      let leftResult :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy
          hwin tag fallbackLeft two.2.1.baseShared leftReceiver input
      let rightResult :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy
          hwin tag fallbackRight one.2.1.baseShared rightReceiver
            (input.2, input.1)
      let leftRow :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
          tag leftReceiver
      let rightRow :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy
          hwin tag rightReceiver
      let onePayload :=
        profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
          strategy hwin tag leftResult.1 leftRow
      let twoPayload :=
        profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
          strategy hwin tag rightResult.1 rightRow
      let leftOwner :=
        profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner A strategy hwin
          tag two.2.1.baseShared twoPayload
      let closedRight :=
        profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
          hwin tag onePayload true
      (member,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh leftOwner
          twoPayload false rightResult.2 closedRight,
        PUnit.unit) := by
  cases member <;> rfl

/-! ### Projection equations used by the recursive invariant -/

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_one_baseShared
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.1.candidate member).2.1.baseShared =
      profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner A strategy hwin
        tag one.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailFreshOnePayload A strategy
            hwin tag fallbackLeft one two input) := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_one_basePayload
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.1.candidate member).2.1.basePayload =
      profiledRawJointHybridShadowPhaseLiveTailFreshOnePayload A strategy hwin
        tag fallbackLeft one two input := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_two_baseShared
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.2.candidate member).2.1.baseShared =
      profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner A strategy hwin
        tag two.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailFreshTwoPayload A strategy
            hwin tag fallbackRight one two input) := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_two_basePayload
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (member : Bool) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.2.candidate member).2.1.basePayload =
      profiledRawJointHybridShadowPhaseLiveTailFreshTwoPayload A strategy hwin
        tag fallbackRight one two input := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_one_open_receiver
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.1.openControl).2.1.receiver
        false =
      (profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult A strategy hwin
        tag fallbackLeft one two input).2 := by
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_two_open_receiver
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.2.openControl).2.1.receiver
        false =
      (profiledRawJointHybridShadowPhaseLiveTailFreshRightResult A strategy hwin
        tag fallbackRight one two input).2 := by
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_one_closed_receiver
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.1.closedControl).2.1.receiver
        true =
      profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy hwin
        tag
          (profiledRawJointHybridShadowPhaseLiveTailFreshTwoPayload A strategy
            hwin tag fallbackRight one two input) true := by
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_two_closed_receiver
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
      fallbackLeft fallbackRight one two input).1.2.closedControl).2.1.receiver
        true =
      profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
        hwin tag
          (profiledRawJointHybridShadowPhaseLiveTailFreshOnePayload A strategy
            hwin tag fallbackLeft one two input) true := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
