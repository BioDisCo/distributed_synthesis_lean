/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailResolvedCutPacketBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailBootstrapSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailStrictSwitchOutputLaw

/-!
# Tracked tagged-tail traces at automatic physical cuts

This file is the operational adapter between the actual tracked finite
tail-controller trace and the already proved resolved-cut packet bridge.  Its
proof-side witnesses retain literal table prefixes between automatic cuts;
the executable endpoint maps remain unchanged and receive no graph direction,
hierarchy side, leader bit, strict-leader bit, history, or semantic view.
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

/-! ## One physical record from a tracked selected table -/

/-- On a strict-right round, a tracked selected right table emits exactly its
literal right-table record.  The statement is deliberately independent of a
cut schedule; it is the one-round fact iterated by the cut-prefix invariant. -/
theorem profiledRawJointHybridShadowPhaseLiveTailReference_rightRecord
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag)
    (hcanonical :
      ((.inl one, .inl two) :
          (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy
                hwin tag) PUnit PUnit.{1}) ×
            (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy
                hwin tag) PUnit PUnit.{1})) =
        profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy hwin
          tag initialOne initialTwo fallbackLeft fallbackRight env n)
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
        one.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag two one))
    (hlaw :
      ProfiledRawJointHybridShadowPhaseLiveTailStrictRightOutputLawAt A strategy
        hwin tag fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo))
    (hgraph : (env n).graph = .right) :
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
      one.2.1.baseShared =
          ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag two one =
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        let input : In₂ × In₁ := ((env n).inputTwo, (env n).inputOne)
        let localEnv : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
        let word :=
          (profiledRawJointHybridShadowPhaseLiveTailTraceInvariant A strategy
            hwin tag initialOne initialTwo fallbackLeft fallbackRight hinitial
              env).referenceWord
            (profiledRawJointHybridShadowPhaseLiveTailPhysicalController A
              strategy hwin tag initialOne initialTwo fallbackLeft
                fallbackRight)
        word n = pairedRightRecordForRow row
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move false localEnv past.length)) := by
  obtain
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, hrecord⟩ :=
    ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.strictRecord_eq_literal_of_outputLaw.{u,
      v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s, max u v x y s, max u v x y s,
      max u v x y s}
      (A := A) (strategy := strategy) (hwin := hwin) tracked fallbackLeft
        fallbackRight ((env n).inputOne, (env n).inputTwo) hlaw
  refine ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
    hreceiver, ?_⟩
  dsimp only
  have hpair :
      ((profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n),
        profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n) =
        ((profiledRawJointHybridShadowPhaseLiveTailNoRecvOne A strategy hwin tag
            (.inl one) (env n).inputOne).2,
          (profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy hwin
            tag initialTwo fallbackLeft fallbackRight (.inl two)
              (env n).inputTwo (.inl one) (env n).inputOne).2) := by
    have hcanonical' :
        ((.inl one, .inl two) :
            (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
                (ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy
                  hwin tag) PUnit PUnit.{1}) ×
              (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
                (ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy
                  hwin tag) PUnit PUnit.{1})) =
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
            (.inl initialOne) (.inl initialTwo)
            (profiledRawJointHybridShadowPhaseLiveTailNoRecvOne A strategy hwin
              tag)
            (profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo A strategy hwin
              tag)
            (profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy
              hwin tag initialOne fallbackLeft fallbackRight)
            (profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy
              hwin tag initialTwo fallbackLeft fallbackRight)
            (profiledRawJointHybridShadowPhaseLiveTailClose A strategy hwin tag
              initialOne initialTwo fallbackLeft fallbackRight) env n := by
      simpa only
        [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace]
        using hcanonical
    simp only
      [profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo,
        hgraph]
    rw [← hcanonical']
  rw [← hrecord]
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · apply EnvironmentRound.eq_of_components
    · rfl
    · rfl
    · exact hgraph
  · change
      (profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n,
       profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n) = _
    exact hpair

/-- Strict-left mirror of
`profiledRawJointHybridShadowPhaseLiveTailReference_rightRecord`.  A tracked
selected left table emits literally the corresponding left-table record of
its decorated physical play. -/
theorem profiledRawJointHybridShadowPhaseLiveTailReference_leftRecord
    (tag : Tag A strategy hwin) (initialOne : OnePending A strategy hwin tag)
    (initialTwo : TwoPending A strategy hwin tag)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hinitial :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag)
    (hcanonical :
      ((.inl one, .inl two) :
          (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy
                hwin tag) PUnit PUnit.{1}) ×
            (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy
                hwin tag) PUnit PUnit.{1})) =
        profiledRawJointHybridShadowPhaseLiveTailSemanticTrace A strategy hwin
          tag initialOne initialTwo fallbackLeft fallbackRight env n)
    (tracked :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
        two.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag one two))
    (hlaw :
      ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftOutputLawAt A strategy
        hwin tag fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo))
    (hgraph : (env n).graph = .left) :
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
      two.2.1.baseShared =
          ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag one two =
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        let input : In₁ × In₂ := ((env n).inputOne, (env n).inputTwo)
        let localEnv : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
        let word :=
          (profiledRawJointHybridShadowPhaseLiveTailTraceInvariant A strategy
            hwin tag initialOne initialTwo fallbackLeft fallbackRight hinitial
              env).referenceWord
            (profiledRawJointHybridShadowPhaseLiveTailPhysicalController A
              strategy hwin tag initialOne initialTwo fallbackLeft
                fallbackRight)
        word n = pairedLeftRecordForRow row
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move false localEnv past.length)) := by
  obtain
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, hrecord⟩ :=
    ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.strictRecord_eq_literal_of_outputLaw.{u,
      v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s, max u v x y s, max u v x y s,
      max u v x y s}
      (A := A) (strategy := strategy) (hwin := hwin) tracked fallbackLeft
        fallbackRight ((env n).inputOne, (env n).inputTwo) hlaw
  refine ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
    hreceiver, ?_⟩
  dsimp only
  have hpair :
      ((profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n),
        profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n) =
        ((profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy hwin
            tag initialOne fallbackLeft fallbackRight (.inl one)
              (env n).inputOne (.inl two) (env n).inputTwo).2,
          (profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo A strategy hwin
            tag (.inl two) (env n).inputTwo).2) := by
    have hcanonical' :
        ((.inl one, .inl two) :
            (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
                (ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy
                  hwin tag) PUnit PUnit.{1}) ×
              (FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
                (ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy
                  hwin tag) PUnit PUnit.{1})) =
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
            (.inl initialOne) (.inl initialTwo)
            (profiledRawJointHybridShadowPhaseLiveTailNoRecvOne A strategy hwin
              tag)
            (profiledRawJointHybridShadowPhaseLiveTailNoRecvTwo A strategy hwin
              tag)
            (profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy
              hwin tag initialOne fallbackLeft fallbackRight)
            (profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy
              hwin tag initialTwo fallbackLeft fallbackRight)
            (profiledRawJointHybridShadowPhaseLiveTailClose A strategy hwin tag
              initialOne initialTwo fallbackLeft fallbackRight) env n := by
      simpa only
        [profiledRawJointHybridShadowPhaseLiveTailSemanticTrace]
        using hcanonical
    simp only
      [profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputOne,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticOutputTwo,
        hgraph]
    rw [← hcanonical']
  rw [← hrecord]
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · apply EnvironmentRound.eq_of_components
    · rfl
    · rfl
    · exact hgraph
  · change
      (profiledRawJointHybridShadowPhaseLiveTailSemanticOutputOne A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n,
       profiledRawJointHybridShadowPhaseLiveTailSemanticOutputTwo A strategy
          hwin tag initialOne initialTwo fallbackLeft fallbackRight env n) = _
    exact hpair

end

end DetParityAutomaton

end DistributedSynthesis
