/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedInvariant

/-!
# The exact strict-switch output seam in a tagged tail fibre

The tracked invariant proves that the owner and selected receiver of either
strict direction are one literal table prefix.  It does **not** identify the
physical receive coordinate chosen by `TailFreshPair` with that selected
receiver coordinate.  The former is a phase-selected `.both` projection; the
latter uses the selected receiver's stored entry row.

This file names precisely those two missing coordinate equations.  It then
proves that each equation is sufficient to recover the full literal strict
record.  Thus all prefix, target, and parity bookkeeping lies downstream of
one minimal output law; none of it can manufacture the law.

The locally forced repair is also explicit: process one's receive coordinate
must be the selected left-table coordinate and process two's receive
coordinate must be the selected right-table coordinate.  On a simultaneous
round their product is a cross-table pair.  Consequently a repaired
controller must obtain its anti-mosaic equality from a joint/root-pinned
table construction; selecting one whole table by a phase bit cannot satisfy
both strict indistinguishability classes in general.

No definition below receives a graph, hierarchy side, leader bit,
strict-leader bit, history, or semantic view as executable input.
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

/-! ## The two locally forced receive coordinates -/

/-- Process two's receive output in the strict-right indistinguishability
class.  The stored row belongs to process two's selected right receiver and
is therefore local data. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailStrictRightReceiveOutput
    (tag : Tag A strategy hwin) (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Out₂ :=
  let receiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let result :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRightResult A strategy hwin
      tag fallbackRight one two input
  pairedRightInformedForRow
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
      tag receiver)
    result.1.physical

/-- Process one's mirror receive output in the strict-left
indistinguishability class. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailStrictLeftReceiveOutput
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Out₁ :=
  let receiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let result :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult A strategy hwin tag
      fallbackLeft one two input
  pairedLeftInformedForRow
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
      tag receiver)
    result.1.physical

/-- The output pair forced by the two local receive indistinguishability
classes.  On a simultaneous round process one still has its strict-left
receive view and process two still has its strict-right receive view. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLocallyForcedReceivePair
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Out₁ × Out₂ :=
  (profiledRawJointHybridShadowPhaseLiveTailStrictLeftReceiveOutput A strategy
      hwin tag fallbackLeft one two input,
    profiledRawJointHybridShadowPhaseLiveTailStrictRightReceiveOutput A strategy
      hwin tag fallbackRight one two input)

/-! ## The exact residual laws of the current controller -/

/-- The current controller's physical output pair, with an explicit result
type.  The annotation is useful because the tail controls contain proof
indices at universe levels that are otherwise invisible after projecting the
second component of `TailFreshPair`. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailCurrentReceivePair
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Out₁ × Out₂ :=
  (profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne A strategy
      hwin tag fallbackLeft fallbackRight one input.1 two input.2,
    profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo A strategy
      hwin tag fallbackLeft fallbackRight two input.2 one input.1)

/-- The current phase-selected pair supplies the strict-right receive
coordinate exactly when this equation holds. -/
def ProfiledRawJointHybridShadowPhaseLiveTailStrictRightOutputLawAt
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  (profiledRawJointHybridShadowPhaseLiveTailCurrentReceivePair A strategy hwin
      tag fallbackLeft fallbackRight one two input).2 =
    profiledRawJointHybridShadowPhaseLiveTailStrictRightReceiveOutput A strategy
      hwin tag fallbackRight one two input

/-- Strict-left mirror. -/
def ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftOutputLawAt
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  (profiledRawJointHybridShadowPhaseLiveTailCurrentReceivePair A strategy hwin
      tag fallbackLeft fallbackRight one two input).1 =
    profiledRawJointHybridShadowPhaseLiveTailStrictLeftReceiveOutput A strategy
      hwin tag fallbackLeft one two input

/-- Both strict indistinguishability classes are respected at one pending
state.  This is deliberately just two physical-coordinate equations. -/
def ProfiledRawJointHybridShadowPhaseLiveTailStrictOutputLawAt
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftOutputLawAt A strategy hwin
      tag fallbackLeft fallbackRight one two input ∧
    ProfiledRawJointHybridShadowPhaseLiveTailStrictRightOutputLawAt A strategy
      hwin tag fallbackLeft fallbackRight one two input

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailStrictOutputLawAt.output_eq_locallyForced
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag} {input : In₁ × In₂}
    (hlaw : ProfiledRawJointHybridShadowPhaseLiveTailStrictOutputLawAt A
      strategy hwin tag fallbackLeft fallbackRight one two input) :
    profiledRawJointHybridShadowPhaseLiveTailCurrentReceivePair A strategy hwin
        tag fallbackLeft fallbackRight one two input =
      profiledRawJointHybridShadowPhaseLiveTailLocallyForcedReceivePair A
        strategy hwin tag fallbackLeft fallbackRight one two input := by
  exact Prod.ext hlaw.1 hlaw.2

/-! ## The tracked prefix closes everything except the named coordinate -/

/-- Once the strict-right receive coordinate is the locally selected one, a
tracked table emits the complete literal right record. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.strictRecord_eq_literal_of_outputLaw
    {tag : Tag A strategy hwin}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy
      hwin tag one.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one))
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (input : In₁ × In₂)
    (hlaw : ProfiledRawJointHybridShadowPhaseLiveTailStrictRightOutputLawAt A
      strategy hwin tag fallbackLeft fallbackRight one two input) :
    ∃ (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
          tag)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
          strategy hwin (tag := tag) move false).State)
      (staged : Option (RightOutput A strategy hwin tag))
      (past : List (In₂ × In₁)),
      one.2.1.baseShared = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag two one =
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        rightRoundRecord (input.2, input.1)
            (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy
              hwin tag one.1 one.2.1 input.1).2
            (profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin
              tag fallbackLeft fallbackRight one two input).2.2 =
          pairedRightRecordForRow row
            (profiledRawJointTargetRightPhysicalLetter A
              (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
                strategy hwin tag state move false
                  (omegaOfList (past ++ [(input.2, input.1)])) past.length)) := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, _hmove, _hreachable, _hone, _hlive, hlocal⟩
  refine ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
    hreceiver, ?_⟩
  rw [profiledRawJointHybridShadowPhaseLiveTailFreshPair_output]
  change rightRoundRecord (input.2, input.1)
      (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
        tag one.1 one.2.1 input.1).2
      (profiledRawJointHybridShadowPhaseLiveTailCurrentReceivePair A strategy
        hwin tag fallbackLeft fallbackRight one two input).2 = _
  rw [hlaw]
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailStrictRightReceiveOutput,
      profiledRawJointHybridShadowPhaseLiveTailFreshRightResult,
      profiledRawJointHybridShadowPhaseLiveTailRecvTwoRight]
  rw [howner]
  rw [show
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
        hwin tag two one =
      ⟨state, some ⟨move, row, monitorState, staged⟩⟩ from hreceiver]
  have houtput := hlocal.output_eq_play A strategy hwin false row
    (input.2, input.1)
  have hpast :
      omegaPrefix (omegaOfList (past ++ [(input.2, input.1)])) past.length =
        past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [(input.2, input.1)]).length := by
        simp
        omega
      change omegaOfList (past ++ [(input.2, input.1)]) n = past[n]
      rw [omegaOfList_eq_getElem _ n hnPrefix]
      simp [hnRight]
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep_live]
  rw [houtput]
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep]
  rw [howner]
  rw [hlocal.1]
  simp only [profiledRawJointHybridShadowPhaseLiveTailRightSharedStep]
  rw [(profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).output_eq
    one.1 false
      ((move.memberController A false).controlAt (senderWord past)) input.1]
  cases row <;> simp
    [profiledRawJointHybridShadowPhaseLiveTailRightSharedStep,
      pairedRightRecordForRow, rightRoundRecord,
      profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter,
      profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay,
      profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController_sender,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection,
      pairedRightInformedForRow,
      profiledRawJointRightPhysicalSiblingDeferredStep, narrowedInducedTree,
      branchNode_eq_omegaPrefix, hpast,
      treePlay, blockLabelApply] <;> rfl

/-- Left strict-record mirror. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.strictRecord_eq_literal_of_outputLaw
    {tag : Tag A strategy hwin}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy
      hwin tag two.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two))
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (input : In₁ × In₂)
    (hlaw : ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftOutputLawAt A
      strategy hwin tag fallbackLeft fallbackRight one two input) :
    ∃ (state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin
          tag)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A
          strategy hwin (tag := tag) move false).State)
      (staged : Option (LeftOutput A strategy hwin tag))
      (past : List (In₁ × In₂)),
      two.2.1.baseShared = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag one two =
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        leftRoundRecord input
            (profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin
              tag fallbackLeft fallbackRight one two input).2.1
            (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy
              hwin tag two.1 two.2.1 input.2).2 =
          pairedLeftRecordForRow row
            (profiledRawJointTargetLeftPhysicalLetter A
              (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
                strategy hwin tag state move false
                  (omegaOfList (past ++ [input])) past.length)) := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, _hmove, _hreachable, _hone, _hlive, hlocal⟩
  refine ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
    hreceiver, ?_⟩
  rw [profiledRawJointHybridShadowPhaseLiveTailFreshPair_output]
  change leftRoundRecord input
      (profiledRawJointHybridShadowPhaseLiveTailCurrentReceivePair A strategy
        hwin tag fallbackLeft fallbackRight one two input).1
      (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
        tag two.1 two.2.1 input.2).2 = _
  rw [hlaw]
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailStrictLeftReceiveOutput,
      profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult,
      profiledRawJointHybridShadowPhaseLiveTailRecvOneLeft]
  rw [howner]
  rw [show
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
        hwin tag one two =
      ⟨state, some ⟨move, row, monitorState, staged⟩⟩ from hreceiver]
  have houtput := hlocal.output_eq_play A strategy hwin false row input
  have hpast : omegaPrefix (omegaOfList (past ++ [input])) past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by
        simp
        omega
      change omegaOfList (past ++ [input]) n = past[n]
      rw [omegaOfList_eq_getElem _ n hnPrefix]
      simp [hnRight]
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep_live]
  rw [houtput]
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep]
  rw [howner]
  rw [hlocal.1]
  simp only [profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep]
  rw [(profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).output_eq
    two.1 false
      ((move.memberController A false).controlAt (senderWord past)) input.2]
  cases row <;> simp
    [profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep,
      pairedLeftRecordForRow, leftRoundRecord,
      profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter,
      profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay,
      profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController_sender,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection,
      pairedLeftInformedForRow,
      profiledRawJointLeftPhysicalSiblingDeferredStep, narrowedInducedTree,
      branchNode_eq_omegaPrefix, hpast,
      treePlay, blockLabelApply] <;> rfl

/-! ## Generic no-selector algebra -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] [Fintype Out₂] in
/-- The simultaneous pair forced by the two receive views agrees with the
whole right pair exactly when process one's left-forced coordinate agrees
with the right table. -/
theorem locallyForcedPair_eq_right_iff
    {left right : Out₁ × Out₂} :
    (left.1, right.2) = right ↔ left.1 = right.1 := by
  rcases left with ⟨leftOne, leftTwo⟩
  rcases right with ⟨rightOne, rightTwo⟩
  simp only [Prod.fst, Prod.snd, Prod.mk.injEq, and_true]

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] [Fintype Out₂] in
/-- Mirror: agreement with the whole left pair is exactly the other
cross-coordinate equation. -/
theorem locallyForcedPair_eq_left_iff
    {left right : Out₁ × Out₂} :
    (left.1, right.2) = left ↔ right.2 = left.2 := by
  rcases left with ⟨leftOne, leftTwo⟩
  rcases right with ⟨rightOne, rightTwo⟩
  simp only [Prod.fst, Prod.snd, Prod.mk.injEq, true_and]

end

end DetParityAutomaton

end DistributedSynthesis
