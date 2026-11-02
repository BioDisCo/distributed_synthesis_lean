/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveTableReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousTailAcceptance

/-!
# Exact physical-input segments of phase-live seam tables

Root reachability alone forgets where the currently active table epoch began.
This file retains, proof-side only, the exact start time and the consecutive
physical input segment which led from the table root to the current local
states.  No clock, prefix, graph, orientation, or leader flag is added to an
executable endpoint.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev RightReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev RightSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
    hwin package

private abbrev OneShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package) Unit

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package) Unit

/-! ## Selected physical projection of a heterogeneous table play -/

/-- Project the internally selected coordinate of a right-seam product
record to the common physical left-block alphabet. -/
noncomputable def literalRightSeamSelectedProductPhysicalLetter
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool)
    (record : RealizedBlockRound In₁ In₂
      (ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy
        hwin installed) Out₂) :
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  if anchor then
    profiledRawJointGuardedFirstLeftPhysicalLetter A
      (record.1, record.2.1.2, record.2.2)
  else
    profiledRawJointTargetLeftPhysicalLetter A
      (record.1, record.2.1.1, record.2.2)

/-- Selected physical right-seam play without introducing an independent
policy controller. -/
noncomputable def literalRightSeamSelectedTablePhysicalPlay
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₁ × In₂) : Nat →
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed
  let controller := table.memberController anchor
  fun n ↦ literalRightSeamSelectedProductPhysicalLetter A strategy hwin
    installed anchor
      (treePlay (narrowedInducedTree _ controller.labeledTree) env n)

/-- Mirror product projection. -/
noncomputable def literalLeftSeamSelectedProductPhysicalLetter
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool)
    (record : RealizedBlockRound In₂ In₁
      (ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy
        hwin installed) Out₁) :
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  if anchor then
    profiledRawJointGuardedFirstRightPhysicalLetter A
      (record.1, record.2.1.2, record.2.2)
  else
    profiledRawJointTargetRightPhysicalLetter A
      (record.1, record.2.1.1, record.2.2)

noncomputable def literalLeftSeamSelectedTablePhysicalPlay
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₂ × In₁) : Nat →
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed
  let controller := table.memberController anchor
  fun n ↦ literalLeftSeamSelectedProductPhysicalLetter A strategy hwin
    installed anchor
      (treePlay (narrowedInducedTree _ controller.labeledTree) env n)

/-- The semantic reference word named by the phase-live output trace. -/
noncomputable def literalCombinedFreshPhaseLiveRootSemanticWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne :=
        package.literalCombinedFreshPhaseLiveRootSemanticOutputOne A strategy
          hwin env n
      outputTwo :=
        package.literalCombinedFreshPhaseLiveRootSemanticOutputTwo A strategy
          hwin env n }

/-- This explicit word is exactly the reference word of the proved physical
controller trace invariant. -/
theorem literalCombinedFreshPhaseLiveRootSemanticWord_eq_referenceWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env =
      (package.literalCombinedFreshPhaseLiveRootTraceInvariant A strategy hwin
        env).referenceWord
        (package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
          hwin) := by
  rfl

/-- On a strict-left round the semantic reference word exposes exactly the
pending retained receive and blind-sender outputs. -/
theorem literalCombinedFreshPhaseLiveRootSemanticWord_strictLeft_pending
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin package),
          (.inl two : TwoControl A strategy hwin package)) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .left) :
    package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env
        n =
      leftRoundRecord ((env n).inputOne, (env n).inputTwo)
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).2
        (package.literalCombinedFreshTwoPendingStep A strategy hwin two.1
          two.2.1 (env n).inputTwo).2 := by
  have hcanonicalSelected :
      package.LiteralCombinedFreshPhaseLiveCanonicalSelected A strategy hwin
        env (.inl one) (.inl two) n :=
    ⟨one, two, rfl, rfl, hstructural, hpair⟩
  have houtputs :=
    (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A strategy
      hwin env).strictLeft n (.inl one) (.inl two) trivial hcanonicalSelected
        hgraph |>.2
  unfold literalCombinedFreshPhaseLiveRootSemanticWord
  rw [← houtputs.1, ← houtputs.2]
  simp [hgraph, leftRoundRecord,
    literalCombinedFreshPhaseLiveOpenRecvOne,
    literalCombinedFreshPhaseLiveNoRecvTwo,
    FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]

/-- Strict-right mirror of the pending semantic record equation. -/
theorem literalCombinedFreshPhaseLiveRootSemanticWord_strictRight_pending
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin package),
          (.inl two : TwoControl A strategy hwin package)) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .right) :
    package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env
        n =
      rightRoundRecord ((env n).inputTwo, (env n).inputOne)
        (package.literalCombinedFreshOnePendingStep A strategy hwin one.1
          one.2.1 (env n).inputOne).2
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).2 := by
  have hcanonicalSelected :
      package.LiteralCombinedFreshPhaseLiveCanonicalSelected A strategy hwin
        env (.inl one) (.inl two) n :=
    ⟨one, two, rfl, rfl, hstructural, hpair⟩
  have houtputs :=
    (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A strategy
      hwin env).strictRight n (.inl one) (.inl two) trivial hcanonicalSelected
        hgraph |>.2
  unfold literalCombinedFreshPhaseLiveRootSemanticWord
  rw [← houtputs.1, ← houtputs.2]
  simp [hgraph, rightRoundRecord,
    literalCombinedFreshPhaseLiveNoRecvOne,
    literalCombinedFreshPhaseLiveOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]

/-- The executable strict-left outputs are the `.both` physical projection
of the internally selected coordinate of the same heterogeneous table
record. -/
theorem literalCombinedFreshPhaseLive_strictLeft_pendingRecord_eq_selected
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (input : In₁ × In₂) :
    let receiver :=
      package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy hwin
        one two
    let receiverStep :=
      package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
        receiver input.1 input.2
    let senderStep :=
      package.literalRightSeamStagedSenderNoRecv A strategy hwin two.2.1.2.1
        input.2
    leftRoundRecord input
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).2
        (package.literalCombinedFreshTwoPendingStep A strategy hwin two.1
          two.2.1 input.2).2 =
      pairedLeftRecordForRow .both
        (literalRightSeamSelectedProductPhysicalLetter A strategy hwin
          (package.literalRightSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          (input, receiverStep.1.2, senderStep.1)) := by
  dsimp only
  let receiver :=
    package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy hwin
      one two
  cases hanchor : receiver.2.2.1.1 <;>
    simp [literalRightSeamSelectedProductPhysicalLetter,
      pairedLeftRecordForRow, profiledRawJointTargetLeftPhysicalLetter,
      profiledRawJointGuardedFirstLeftPhysicalLetter,
      indexedTargetPhysicalLetter,
      profiledRawJointTargetLeftReceiverBothPhysicalOutput,
      literalCombinedFreshPhaseLiveRecvOne,
      literalCombinedFreshTwoPendingStep,
      literalRightSeamInternalPhysicalOutput, hanchor, receiver,
      pairedLeftReceiverBothPhysicalOutput, pairedLeftInformedForRow]

/-- Mirror selected-product physical projection. -/
theorem literalCombinedFreshPhaseLive_strictRight_pendingRecord_eq_selected
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (input : In₁ × In₂) :
    let receiver :=
      package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy hwin
        two one
    let receiverStep :=
      package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin receiver
        input.2 input.1
    let senderStep :=
      package.literalLeftSeamStagedSenderNoRecv A strategy hwin one.2.1.2.1
        input.1
    rightRoundRecord (input.2, input.1)
        (package.literalCombinedFreshOnePendingStep A strategy hwin one.1
          one.2.1 input.1).2
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).2 =
      pairedRightRecordForRow .both
        (literalLeftSeamSelectedProductPhysicalLetter A strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          ((input.2, input.1), receiverStep.1.2, senderStep.1)) := by
  dsimp only
  let receiver :=
    package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy hwin
      two one
  cases hanchor : receiver.2.2.1.1 <;>
    simp [literalLeftSeamSelectedProductPhysicalLetter,
      pairedRightRecordForRow, profiledRawJointTargetRightPhysicalLetter,
      profiledRawJointGuardedFirstRightPhysicalLetter,
      indexedTargetPhysicalLetter,
      profiledRawJointTargetRightReceiverBothPhysicalOutput,
      literalCombinedFreshPhaseLiveRecvTwo,
      literalCombinedFreshOnePendingStep,
      literalLeftSeamInternalPhysicalOutput, hanchor, receiver,
      pairedRightReceiverBothPhysicalOutput, pairedRightInformedForRow]

/-- The exact consecutive strict-left input segment represented by a
right-seam table state at global time `n`. -/
def LiteralRightSeamTableRootSegmentAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package) : Prop :=
  ∃ start : Nat, ∃ past : List (In₁ × In₂),
    start + past.length = n ∧
      (∀ (j : Nat) (hj : j < past.length),
        past[j] = ((env (start + j)).inputOne,
          (env (start + j)).inputTwo)) ∧
      sender =
        ⟨receiver.1,
          finiteCrossAnchorSenderAtPrefix
            (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A
              strategy hwin
              (package.literalRightSeamInstalled A strategy hwin receiver.1))
            past⟩ ∧
      receiver.2.2.1 =
        finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A
            strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1))
          receiver.2.2.1.1 past

/-- The mirror exact consecutive strict-right input segment. -/
def LiteralLeftSeamTableRootSegmentAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package) : Prop :=
  ∃ start : Nat, ∃ past : List (In₂ × In₁),
    start + past.length = n ∧
      (∀ (j : Nat) (hj : j < past.length),
        past[j] = ((env (start + j)).inputTwo,
          (env (start + j)).inputOne)) ∧
      sender =
        ⟨receiver.1,
          finiteCrossAnchorSenderAtPrefix
            (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A
              strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin receiver.1))
            past⟩ ∧
      receiver.2.2.1 =
        finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A
            strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1))
          receiver.2.2.1.1 past

/-- A freshly installed right table represents the empty segment beginning
at its installation time. -/
theorem literalRightSeamTableRootSegmentAt_initial
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralRightSeamTableRootSegmentAt A strategy hwin env n
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalRightSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨n, [], by simp, ?_, rfl, rfl⟩
  intro j hj
  simp at hj

/-- One local left round appends the actual global input at time `n` to the
same right-table epoch. -/
theorem LiteralRightSeamTableRootSegmentAt.step
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : RightReceiver A strategy hwin package}
    {sender : RightSender A strategy hwin package}
    (hsegment : package.LiteralRightSeamTableRootSegmentAt A strategy hwin env
      n receiver sender) :
    package.LiteralRightSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
        receiver (env n).inputOne (env n).inputTwo).2
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin sender
        (env n).inputTwo).2 := by
  rcases hsegment with
    ⟨start, past, hend, hinputs, hsender, hreceiver⟩
  rcases receiver with ⟨key, row, tableReceiver, stage⟩
  dsimp only at hsender hreceiver ⊢
  subst sender
  rw [hreceiver]
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin (package.literalRightSeamInstalled A strategy hwin key)
  refine ⟨start, past ++ [((env n).inputOne, (env n).inputTwo)], ?_, ?_,
    ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro j hj
    by_cases hjOld : j < past.length
    · simpa [List.getElem_append, hjOld] using hinputs j hjOld
    · have hjEq : j = past.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      simp [hend]
  · apply Sigma.ext
    · rfl
    · simpa [literalRightSeamStagedSenderNoRecv,
        literalRightSeamFrontSenderNoRecv,
        profiledRawJointLiteralRightBothExactSenderNoRecv,
        literalRightSeamBranchStagedReceiverRecv, table] using
          (finiteCrossAnchorSenderNoRecv_atPrefix table past
            ((env n).inputOne, (env n).inputTwo))
  · simp only [literalRightSeamBranchStagedReceiverRecv]
    exact finiteCrossAnchorReceiverRecv_atPrefix table _ past
      ((env n).inputOne, (env n).inputTwo)

/-- Fresh mirror installation represents the empty segment. -/
theorem literalLeftSeamTableRootSegmentAt_initial
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env n
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨n, [], by simp, ?_, rfl, rfl⟩
  intro j hj
  simp at hj

/-- One local right round appends the actual swapped global input. -/
theorem LiteralLeftSeamTableRootSegmentAt.step
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : LeftReceiver A strategy hwin package}
    {sender : LeftSender A strategy hwin package}
    (hsegment : package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env n
      receiver sender) :
    package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
        receiver (env n).inputTwo (env n).inputOne).2
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin sender
        (env n).inputOne).2 := by
  rcases hsegment with
    ⟨start, past, hend, hinputs, hsender, hreceiver⟩
  rcases receiver with ⟨key, row, tableReceiver, stage⟩
  dsimp only at hsender hreceiver ⊢
  subst sender
  rw [hreceiver]
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin (package.literalLeftSeamInstalled A strategy hwin key)
  refine ⟨start, past ++ [((env n).inputTwo, (env n).inputOne)], ?_, ?_,
    ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro j hj
    by_cases hjOld : j < past.length
    · simpa [List.getElem_append, hjOld] using hinputs j hjOld
    · have hjEq : j = past.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      simp [hend]
  · apply Sigma.ext
    · rfl
    · simpa [literalLeftSeamStagedSenderNoRecv,
        literalLeftSeamFrontSenderNoRecv,
        profiledRawJointLiteralLeftBothExactSenderNoRecv,
        literalLeftSeamBranchStagedReceiverRecv, table] using
          (finiteCrossAnchorSenderNoRecv_atPrefix table past
            ((env n).inputTwo, (env n).inputOne))
  · simp only [literalLeftSeamBranchStagedReceiverRecv]
    exact finiteCrossAnchorReceiverRecv_atPrefix table _ past
      ((env n).inputTwo, (env n).inputOne)

/-! ## Segment transport through phase-live receives -/

/-- Repeated strict-left reception extends the retained right-table segment. -/
theorem literalCombinedFreshPhaseLiveRecvOne_same_segment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = true)
    (hsegment : package.LiteralRightSeamTableRootSegmentAt A strategy hwin env
      n (package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1) two.2.1.2.1) :
    package.LiteralRightSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 (env n).inputTwo).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A strategy
    hwin one two hphase]
  exact LiteralRightSeamTableRootSegmentAt.step A strategy hwin package env n
    hsegment

/-- A right-to-left switch starts the new right-table epoch at the current
round and immediately appends that round's input. -/
theorem literalCombinedFreshPhaseLiveRecvOne_switch_segment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = false)
    (hroot : two.2.1.2.1 =
      package.literalRightSeamStagedSenderInitial A strategy hwin
        two.2.1.2.1.1) :
    package.LiteralRightSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 (env n).inputTwo).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A
    strategy hwin one two hphase]
  rw [hroot]
  exact LiteralRightSeamTableRootSegmentAt.step A strategy hwin package env n
    (package.literalRightSeamTableRootSegmentAt_initial A strategy hwin env n
      two.2.1.2.1.1 (literalCombinedFreshRowOfMember two.1) two.1)

/-- Repeated strict-right reception extends the mirror table segment. -/
theorem literalCombinedFreshPhaseLiveRecvTwo_same_segment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = false)
    (hsegment : package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env
      n (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
        two.2.1) one.2.1.2.1) :
    package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 (env n).inputOne).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_same A strategy
    hwin two one hphase]
  exact LiteralLeftSeamTableRootSegmentAt.step A strategy hwin package env n
    hsegment

/-- A left-to-right switch starts and immediately extends the mirror epoch. -/
theorem literalCombinedFreshPhaseLiveRecvTwo_switch_segment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = true)
    (hroot : one.2.1.2.1 =
      package.literalLeftSeamStagedSenderInitial A strategy hwin
        one.2.1.2.1.1) :
    package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 (env n).inputOne).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_switch A
    strategy hwin two one hphase]
  rw [hroot]
  exact LiteralLeftSeamTableRootSegmentAt.step A strategy hwin package env n
    (package.literalLeftSeamTableRootSegmentAt_initial A strategy hwin env n
      one.2.1.2.1.1 (literalCombinedFreshRowOfMember one.1) one.1)

/-- A simultaneous close installs a fresh empty right-table epoch after the
current round. -/
theorem literalCombinedFreshPhaseLiveBoth_closed_right_segment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralRightSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalCombinedFreshOneReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1.closedControl.2.1)
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        (env n).inputTwo one
        (env n).inputOne).1.closedControl.2.1.2.1 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_closed_receiver A strategy
    hwin]
  change package.LiteralRightSeamTableRootSegmentAt A strategy hwin env
    (n + 1) _
    (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
      (env n).inputTwo one.2.1 (env n).inputOne).2.1
  rw [← package.literalCombinedFreshPendingBoundaryTwoShared_eq_receive_of_aligned
    A strategy hwin one.2.1 two.2.1
      ((env n).inputOne, (env n).inputTwo) hfresh]
  rw [package.literalCombinedFreshPendingBoundaryTwoShared_sender A strategy
    hwin]
  have hkey :
      package.literalCombinedFreshOneReceiveKey A strategy hwin one.2.1
          (env n).inputOne two.2.1 (env n).inputTwo =
        package.literalCombinedFreshPendingBoundaryKey A strategy hwin
          one.2.1 two.2.1 ((env n).inputOne, (env n).inputTwo) := rfl
  rw [hkey]
  exact package.literalRightSeamTableRootSegmentAt_initial A strategy hwin env
    (n + 1)
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 ((env n).inputOne, (env n).inputTwo)) .both true

/-- Simultaneous close installs the fresh empty mirror epoch too. -/
theorem literalCombinedFreshPhaseLiveBoth_closed_left_segment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env (n + 1)
      (package.literalCombinedFreshTwoReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).1.closedControl.2.1)
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        (env n).inputOne two
        (env n).inputTwo).1.closedControl.2.1.2.1 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_closed_receiver A strategy
    hwin]
  rw [← package.literalCombinedFreshPendingBoundaryTwoShared_eq_receive_of_aligned
    A strategy hwin one.2.1 two.2.1
      ((env n).inputOne, (env n).inputTwo) hfresh]
  change package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env
    (n + 1) _
    (package.literalLeftSeamStagedSenderInitial A strategy hwin
      (package.literalCombinedFreshOneReceiveKey A strategy hwin one.2.1
        (env n).inputOne two.2.1 (env n).inputTwo))
  have hkey :
      package.literalCombinedFreshOneReceiveKey A strategy hwin one.2.1
          (env n).inputOne two.2.1 (env n).inputTwo =
        package.literalCombinedFreshPendingBoundaryKey A strategy hwin
          one.2.1 two.2.1 ((env n).inputOne, (env n).inputTwo) := rfl
  rw [hkey]
  exact package.literalLeftSeamTableRootSegmentAt_initial A strategy hwin env
    (n + 1)
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 ((env n).inputOne, (env n).inputTwo)) .both true

/-! ## Phase-dependent exact segment -/

/-- The table(s) active in the current local phase carry their exact global
epoch start and consecutive physical input segment. -/
def LiteralCombinedFreshPhaseLiveTableRootSegmentAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  match one.2.1.1.2, two.2.1.1.2 with
  | false, false =>
      package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env n
        (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
          two.2.1) one.2.1.2.1
  | true, true =>
      package.LiteralRightSeamTableRootSegmentAt A strategy hwin env n
        (package.literalCombinedFreshOneReceiver A strategy hwin one.1
          one.2.1) two.2.1.2.1
  | true, false =>
      package.LiteralRightSeamTableRootSegmentAt A strategy hwin env n
          (package.literalCombinedFreshOneReceiver A strategy hwin one.1
            one.2.1) two.2.1.2.1 ∧
        package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env n
          (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
            two.2.1) one.2.1.2.1
  | false, true => False

theorem literalCombinedFreshPhaseLiveTableRootSegmentAt_initial
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A strategy hwin env
      0 (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) := by
  change
    package.LiteralRightSeamTableRootSegmentAt A strategy hwin env 0
        (package.literalRightSeamStagedReceiverInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          .first false)
        (package.literalRightSeamStagedSenderInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)) ∧
      package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env 0
        (package.literalLeftSeamStagedReceiverInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          .first false)
        (package.literalLeftSeamStagedSenderInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin))
  exact ⟨
    package.literalRightSeamTableRootSegmentAt_initial A strategy hwin env 0
      _ .first false,
    package.literalLeftSeamTableRootSegmentAt_initial A strategy hwin env 0
      _ .first false⟩

/-- A simultaneous round resets both exact segments after that round. -/
theorem literalCombinedFreshPhaseLiveTableRootSegmentAt_both
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        (env n).inputOne two (env n).inputTwo).1.closedControl
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        (env n).inputTwo one (env n).inputOne).1.closedControl
    package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A strategy hwin env
      (n + 1) oneNext twoNext := by
  dsimp only
  change
    package.LiteralRightSeamTableRootSegmentAt A strategy hwin env (n + 1)
        (package.literalCombinedFreshOneReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
            (env n).inputOne two (env n).inputTwo).1.closedControl.2.1)
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one
          (env n).inputOne).1.closedControl.2.1.2.1 ∧
      package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env (n + 1)
        (package.literalCombinedFreshTwoReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            (env n).inputTwo one (env n).inputOne).1.closedControl.2.1)
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two
          (env n).inputTwo).1.closedControl.2.1.2.1
  exact ⟨
    package.literalCombinedFreshPhaseLiveBoth_closed_right_segment A strategy
      hwin env n one two hstructural.1,
    package.literalCombinedFreshPhaseLiveBoth_closed_left_segment A strategy
      hwin env n one two hstructural.1⟩

/-- A strict-right round either extends the retained left segment or starts
it at this switch round. -/
theorem literalCombinedFreshPhaseLiveTableRootSegmentAt_strictRight
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hsegment : package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A
      strategy hwin env n one two) :
    let oneNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one
        (env n).inputOne
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        (env n).inputTwo one (env n).inputOne).1.openControl
    package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A strategy hwin env
      (n + 1) oneNext.1 twoNext := by
  dsimp only
  change package.LiteralLeftSeamTableRootSegmentAt A strategy hwin env (n + 1)
    (package.literalCombinedFreshTwoReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        (env n).inputTwo one (env n).inputOne).1.openControl.2.1)
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one
        (env n).inputOne).1.2.1.2.1
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvTwo_same_segment A strategy
      hwin env n two one htwo hsegment
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvTwo_same_segment A strategy
      hwin env n two one htwo hsegment.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
    have hroot := hstructural.2.2
    simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo]
      at hroot
    exact package.literalCombinedFreshPhaseLiveRecvTwo_switch_segment A
      strategy hwin env n two one htwo hroot.2

/-- Strict-left mirror: retain or start the right-table segment. -/
theorem literalCombinedFreshPhaseLiveTableRootSegmentAt_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hsegment : package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A
      strategy hwin env n one two) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        (env n).inputOne two (env n).inputTwo).1.openControl
    let twoNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
        (env n).inputTwo
    package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A strategy hwin env
      (n + 1) oneNext twoNext.1 := by
  dsimp only
  change package.LiteralRightSeamTableRootSegmentAt A strategy hwin env
    (n + 1)
    (package.literalCombinedFreshOneReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        (env n).inputOne two (env n).inputTwo).1.openControl.2.1)
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
        (env n).inputTwo).1.2.1.2.1
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
    have hroot := hstructural.2.2
    simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo]
      at hroot
    exact package.literalCombinedFreshPhaseLiveRecvOne_switch_segment A
      strategy hwin env n one two hone hroot.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvOne_same_segment A strategy
      hwin env n one two hone hsegment.1
  · simp only [LiteralCombinedFreshPhaseLiveTableRootSegmentAt, hone, htwo]
      at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvOne_same_segment A strategy
      hwin env n one two hone hsegment

/-! ## Exact segment carried by the canonical semantic trace -/

def LiteralCombinedFreshPhaseLiveRootSegmentSelected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin one
      two ∧
    package.LiteralCombinedFreshPhaseLiveTableRootSegmentAt A strategy hwin env
      n one two

def LiteralCombinedFreshPhaseLiveCanonicalRootSegmentSelected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (one : OneControl A strategy hwin package)
    (two : TwoControl A strategy hwin package) (n : Nat) : Prop :=
  ∃ onePending : OnePending A strategy hwin package,
    ∃ twoPending : TwoPending A strategy hwin package,
      one = .inl onePending ∧ two = .inl twoPending ∧
        package.LiteralCombinedFreshPhaseLiveRootSegmentSelected A strategy
          hwin env n onePending twoPending ∧
        (one, two) =
          package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
            hwin env n

/-- At every global time, the actual canonical pending controls carry an
honest table epoch `[start,n)`, with `start + past.length = n` and `past`
equal pointwise to the corresponding consecutive physical inputs. -/
theorem literalCombinedFreshPhaseLiveRootSemanticTrace_tableSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralCombinedFreshPhaseLiveCanonicalRootSegmentSelected A
      strategy hwin env
      (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n).1
      (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n).2 n := by
  intro n
  induction n with
  | zero =>
      exact ⟨
        package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin,
        package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin,
        rfl, rfl,
        ⟨package.literalCombinedFreshPhaseLiveStructuralSelected_initial A
            strategy hwin,
          package.literalCombinedFreshPhaseLiveTableRootSegmentAt_initial A
            strategy hwin env⟩,
        rfl⟩
  | succ n ih =>
      rcases ih with
        ⟨onePending, twoPending, hone, htwo, hselected, _hcanonical⟩
      have hpair :
          ((.inl onePending : OneControl A strategy hwin package),
            (.inl twoPending : TwoControl A strategy hwin package)) =
            package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
              hwin env n := by
        apply Prod.ext
        · exact hone.symm
        · exact htwo.symm
      have hcanonicalSelected :
          package.LiteralCombinedFreshPhaseLiveCanonicalSelected A strategy
            hwin env (.inl onePending) (.inl twoPending) n :=
        ⟨onePending, twoPending, rfl, rfl, hselected.1, hpair⟩
      cases hgraph : (env n).graph with
      | right =>
          let oneNext : OnePending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshOnePendingStep A strategy hwin)
              onePending (env n).inputOne).1
          let twoNext : TwoPending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin
              twoPending (env n).inputTwo onePending (env n).inputOne
              ).1.openControl
          have hnext :
              package.LiteralCombinedFreshPhaseLiveRootSegmentSelected A
                strategy hwin env (n + 1) oneNext twoNext := ⟨
            package.literalCombinedFreshPhaseLiveStructuralSelected_strictRight
              A strategy hwin onePending twoPending hselected.1
                ((env n).inputOne, (env n).inputTwo),
            package.literalCombinedFreshPhaseLiveTableRootSegmentAt_strictRight
              A strategy hwin env n onePending twoPending hselected.1
                hselected.2⟩
          have hpairNext :
              ((.inl oneNext : OneControl A strategy hwin package),
                (.inl twoNext : TwoControl A strategy hwin package)) =
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                  strategy hwin env (n + 1) := by
            have hnextCanonical :=
              (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
                strategy hwin env).strictRight n (.inl onePending)
                  (.inl twoPending) trivial hcanonicalSelected hgraph |>.1
            rcases hnextCanonical with ⟨_, _, _, _, _, htraceNext⟩
            exact htraceNext
          exact ⟨oneNext, twoNext,
            (congrArg Prod.fst hpairNext).symm,
            (congrArg Prod.snd hpairNext).symm, hnext, rfl⟩
      | left =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
              onePending (env n).inputOne twoPending (env n).inputTwo
              ).1.openControl
          let twoNext : TwoPending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshTwoPendingStep A strategy hwin)
              twoPending (env n).inputTwo).1
          have hnext :
              package.LiteralCombinedFreshPhaseLiveRootSegmentSelected A
                strategy hwin env (n + 1) oneNext twoNext := ⟨
            package.literalCombinedFreshPhaseLiveStructuralSelected_strictLeft
              A strategy hwin onePending twoPending hselected.1
                ((env n).inputOne, (env n).inputTwo),
            package.literalCombinedFreshPhaseLiveTableRootSegmentAt_strictLeft
              A strategy hwin env n onePending twoPending hselected.1
                hselected.2⟩
          have hpairNext :
              ((.inl oneNext : OneControl A strategy hwin package),
                (.inl twoNext : TwoControl A strategy hwin package)) =
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                  strategy hwin env (n + 1) := by
            have hnextCanonical :=
              (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
                strategy hwin env).strictLeft n (.inl onePending)
                  (.inl twoPending) trivial hcanonicalSelected hgraph |>.1
            rcases hnextCanonical with ⟨_, _, _, _, _, htraceNext⟩
            exact htraceNext
          exact ⟨oneNext, twoNext,
            (congrArg Prod.fst hpairNext).symm,
            (congrArg Prod.snd hpairNext).symm, hnext, rfl⟩
      | both =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
              onePending (env n).inputOne twoPending (env n).inputTwo
              ).1.closedControl
          let twoNext : TwoPending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin
              twoPending (env n).inputTwo onePending (env n).inputOne
              ).1.closedControl
          have hnext :
              package.LiteralCombinedFreshPhaseLiveRootSegmentSelected A
                strategy hwin env (n + 1) oneNext twoNext := ⟨
            package.literalCombinedFreshPhaseLiveStructuralSelected_both A
              strategy hwin onePending twoPending hselected.1
                ((env n).inputOne, (env n).inputTwo),
            package.literalCombinedFreshPhaseLiveTableRootSegmentAt_both A
              strategy hwin env n onePending twoPending hselected.1⟩
          have hpairNext :
              ((.inl oneNext : OneControl A strategy hwin package),
                (.inl twoNext : TwoControl A strategy hwin package)) =
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                  strategy hwin env (n + 1) := by
            have hnextCanonical :=
              (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
                strategy hwin env).both n (.inl onePending)
                  (.inl twoPending) trivial hcanonicalSelected hgraph |>.1
            rcases hnextCanonical with ⟨_, _, _, _, _, htraceNext⟩
            exact htraceNext
          exact ⟨oneNext, twoNext,
            (congrArg Prod.fst hpairNext).symm,
            (congrArg Prod.snd hpairNext).symm, hnext, rfl⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
