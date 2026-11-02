/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveTableSegment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchStagePhysicalPriority

/-!
# Physical readback of phase-live table segments

The proof-side epoch witnesses from the table-segment invariant are enriched
with the exact physical record produced at every position of the epoch.  The
row is deliberately fixed to `.both`: this is the executable projection used
by the literal seam, independently of the proof-side row stored in a table
state.
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

/-- A right-seam table state represents both its exact local input prefix and
the exact `.both`-projected physical records already emitted in that epoch. -/
def LiteralRightSeamTableRootPhysicalSegmentAt
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
          receiver.2.2.1.1 past ∧
      ∀ (j : Nat) (hj : j < past.length),
        package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin
            env (start + j) =
          pairedLeftRecordForRow .both
            (literalRightSeamSelectedTablePhysicalPlay A strategy hwin
              (package.literalRightSeamInstalled A strategy hwin receiver.1)
              receiver.2.2.1.1
              (fun k ↦ ((env (start + k)).inputOne,
                (env (start + k)).inputTwo)) j)

/-- Strict-right mirror. -/
def LiteralLeftSeamTableRootPhysicalSegmentAt
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
          receiver.2.2.1.1 past ∧
      ∀ (j : Nat) (hj : j < past.length),
        package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin
            env (start + j) =
          pairedRightRecordForRow .both
            (literalLeftSeamSelectedTablePhysicalPlay A strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin receiver.1)
              receiver.2.2.1.1
              (fun k ↦ ((env (start + k)).inputTwo,
                (env (start + k)).inputOne)) j)

theorem literalRightSeamTableRootPhysicalSegmentAt_initial
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalRightSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨n, [], by simp, ?_, rfl, rfl, ?_⟩
  · intro j hj
    simp at hj
  · intro j hj
    simp at hj

theorem literalLeftSeamTableRootPhysicalSegmentAt_initial
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨n, [], by simp, ?_, rfl, rfl, ?_⟩
  · intro j hj
    simp at hj
  · intro j hj
    simp at hj

/-- Append one strict-left round to an already read-back right-seam epoch. -/
theorem LiteralRightSeamTableRootPhysicalSegmentAt.step
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : RightReceiver A strategy hwin package}
    {sender : RightSender A strategy hwin package}
    (hsegment :
      package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender)
    (hrecord :
      package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env
          n =
        pairedLeftRecordForRow .both
          (literalRightSeamSelectedProductPhysicalLetter A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (((env n).inputOne, (env n).inputTwo),
              (package.literalRightSeamBranchStagedReceiverRecv A strategy
                hwin receiver (env n).inputOne (env n).inputTwo).1.2,
              (package.literalRightSeamStagedSenderNoRecv A strategy hwin
                sender (env n).inputTwo).1))) :
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
        receiver (env n).inputOne (env n).inputTwo).2
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin sender
        (env n).inputTwo).2 := by
  rcases hsegment with
    ⟨start, past, hend, hinputs, hsender, hreceiver, hrecords⟩
  rcases receiver with ⟨key, row, tableReceiver, stage⟩
  dsimp only at hsender hreceiver hrecord ⊢
  subst sender
  rw [hreceiver] at hrecord ⊢
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      (package.literalRightSeamInstalled A strategy hwin key)
  let localEnv : Nat → In₁ × In₂ :=
    fun k ↦ ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  have hpast : omegaPrefix localEnv past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro j hjLeft hjRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      exact (hinputs j hjRight).symm
  have hinput :
      localEnv past.length = ((env n).inputOne, (env n).inputTwo) := by
    simp only [localEnv, hend]
  have hlocal :=
    finiteCrossAnchor_localRound_atPrefix_eq_treePlay table
      tableReceiver.1 past ((env n).inputOne, (env n).inputTwo) localEnv hpast
        hinput
  refine ⟨start, past ++ [((env n).inputOne, (env n).inputTwo)], ?_, ?_,
    ?_, ?_, ?_⟩
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
  · intro j hj
    by_cases hjOld : j < past.length
    · simpa [literalRightSeamSelectedTablePhysicalPlay, localEnv] using
        hrecords j hjOld
    · have hjEq : j = past.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [hend]
      rw [hrecord]
      simp only [literalRightSeamSelectedTablePhysicalPlay,
        literalRightSeamBranchStagedReceiverRecv]
      congr 2

/-- Append one strict-right round to the mirror physical epoch. -/
theorem LiteralLeftSeamTableRootPhysicalSegmentAt.step
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : LeftReceiver A strategy hwin package}
    {sender : LeftSender A strategy hwin package}
    (hsegment :
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender)
    (hrecord :
      package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env
          n =
        pairedRightRecordForRow .both
          (literalLeftSeamSelectedProductPhysicalLetter A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (((env n).inputTwo, (env n).inputOne),
              (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
                receiver (env n).inputTwo (env n).inputOne).1.2,
              (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
                sender (env n).inputOne).1))) :
    package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
      (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
        receiver (env n).inputTwo (env n).inputOne).2
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin sender
        (env n).inputOne).2 := by
  rcases hsegment with
    ⟨start, past, hend, hinputs, hsender, hreceiver, hrecords⟩
  rcases receiver with ⟨key, row, tableReceiver, stage⟩
  dsimp only at hsender hreceiver hrecord ⊢
  subst sender
  rw [hreceiver] at hrecord ⊢
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      (package.literalLeftSeamInstalled A strategy hwin key)
  let localEnv : Nat → In₂ × In₁ :=
    fun k ↦ ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  have hpast : omegaPrefix localEnv past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro j hjLeft hjRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      exact (hinputs j hjRight).symm
  have hinput :
      localEnv past.length = ((env n).inputTwo, (env n).inputOne) := by
    simp only [localEnv, hend]
  have hlocal :=
    finiteCrossAnchor_localRound_atPrefix_eq_treePlay table
      tableReceiver.1 past ((env n).inputTwo, (env n).inputOne) localEnv hpast
        hinput
  refine ⟨start, past ++ [((env n).inputTwo, (env n).inputOne)], ?_, ?_,
    ?_, ?_, ?_⟩
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
  · intro j hj
    by_cases hjOld : j < past.length
    · simpa [literalLeftSeamSelectedTablePhysicalPlay, localEnv] using
        hrecords j hjOld
    · have hjEq : j = past.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [hend]
      rw [hrecord]
      simp only [literalLeftSeamSelectedTablePhysicalPlay,
        literalLeftSeamBranchStagedReceiverRecv]
      congr 2

/-! ## Transport through the concrete strict-round handlers -/

theorem literalCombinedFreshPhaseLiveRecvOne_same_physicalSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one, .inl two) :
          FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (OneShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
                strategy hwin package) Unit ×
            FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (TwoShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
                strategy hwin package) Unit) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .left)
    (hphase : one.2.1.1.2 = true)
    (hsegment :
      package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
        (package.literalCombinedFreshOneReceiver A strategy hwin one.1
          one.2.1) two.2.1.2.1) :
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 (env n).inputTwo).2 := by
  have hreceiverFor :=
    package.literalCombinedFreshLiveRightReceiverForRecvOne_same A strategy
      hwin one two hphase
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [hreceiverFor]
  apply LiteralRightSeamTableRootPhysicalSegmentAt.step A strategy hwin package
    env n hsegment
  have hselected :=
    package.literalCombinedFreshPhaseLive_strictLeft_pendingRecord_eq_selected
      A strategy hwin one two ((env n).inputOne, (env n).inputTwo)
  dsimp only at hselected
  rw [hreceiverFor] at hselected
  exact
    (package.literalCombinedFreshPhaseLiveRootSemanticWord_strictLeft_pending A
      strategy hwin env n one two hstructural hpair hgraph).trans hselected

theorem literalCombinedFreshPhaseLiveRecvOne_switch_physicalSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one, .inl two) :
          FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (OneShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
                strategy hwin package) Unit ×
            FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (TwoShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
                strategy hwin package) Unit) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .left)
    (hphase : one.2.1.1.2 = false)
    (hroot : two.2.1.2.1 =
      package.literalRightSeamStagedSenderInitial A strategy hwin
        two.2.1.2.1.1) :
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 (env n).inputTwo).2 := by
  have hreceiverFor :=
    package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A strategy
      hwin one two hphase
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [hreceiverFor]
  rw [hroot]
  apply LiteralRightSeamTableRootPhysicalSegmentAt.step A strategy hwin package
    env n
    (package.literalRightSeamTableRootPhysicalSegmentAt_initial A strategy hwin
      env n two.2.1.2.1.1 (literalCombinedFreshRowOfMember two.1) two.1)
  have hselected :=
    package.literalCombinedFreshPhaseLive_strictLeft_pendingRecord_eq_selected
      A strategy hwin one two ((env n).inputOne, (env n).inputTwo)
  dsimp only at hselected
  rw [hreceiverFor, hroot] at hselected
  exact
    (package.literalCombinedFreshPhaseLiveRootSemanticWord_strictLeft_pending A
      strategy hwin env n one two hstructural hpair hgraph).trans hselected

theorem literalCombinedFreshPhaseLiveRecvTwo_same_physicalSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one, .inl two) :
          FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (OneShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
                strategy hwin package) Unit ×
            FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (TwoShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
                strategy hwin package) Unit) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .right)
    (hphase : two.2.1.1.2 = false)
    (hsegment :
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
        (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
          two.2.1) one.2.1.2.1) :
    package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 (env n).inputOne).2 := by
  have hreceiverFor :=
    package.literalCombinedFreshLiveLeftReceiverForRecvTwo_same A strategy
      hwin two one hphase
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [hreceiverFor]
  apply LiteralLeftSeamTableRootPhysicalSegmentAt.step A strategy hwin package
    env n hsegment
  have hselected :=
    package.literalCombinedFreshPhaseLive_strictRight_pendingRecord_eq_selected
      A strategy hwin one two ((env n).inputOne, (env n).inputTwo)
  dsimp only at hselected
  rw [hreceiverFor] at hselected
  exact
    (package.literalCombinedFreshPhaseLiveRootSemanticWord_strictRight_pending A
      strategy hwin env n one two hstructural hpair hgraph).trans hselected

theorem literalCombinedFreshPhaseLiveRecvTwo_switch_physicalSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one, .inl two) :
          FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (OneShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
                strategy hwin package) Unit ×
            FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (TwoShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
                strategy hwin package) Unit) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .right)
    (hphase : two.2.1.1.2 = true)
    (hroot : one.2.1.2.1 =
      package.literalLeftSeamStagedSenderInitial A strategy hwin
        one.2.1.2.1.1) :
    package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one (env n).inputOne).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 (env n).inputOne).2 := by
  have hreceiverFor :=
    package.literalCombinedFreshLiveLeftReceiverForRecvTwo_switch A strategy
      hwin two one hphase
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [hreceiverFor]
  rw [hroot]
  apply LiteralLeftSeamTableRootPhysicalSegmentAt.step A strategy hwin package
    env n
    (package.literalLeftSeamTableRootPhysicalSegmentAt_initial A strategy hwin
      env n one.2.1.2.1.1 (literalCombinedFreshRowOfMember one.1) one.1)
  have hselected :=
    package.literalCombinedFreshPhaseLive_strictRight_pendingRecord_eq_selected
      A strategy hwin one two ((env n).inputOne, (env n).inputTwo)
  dsimp only at hselected
  rw [hreceiverFor, hroot] at hselected
  exact
    (package.literalCombinedFreshPhaseLiveRootSemanticWord_strictRight_pending A
      strategy hwin env n one two hstructural hpair hgraph).trans hselected

/-! ## Phase-dependent physical segment -/

theorem literalCombinedFreshPhaseLiveBoth_closed_right_physicalSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
      (package.literalCombinedFreshOneReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two (env n).inputTwo).1.closedControl.2.1)
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        (env n).inputTwo one
        (env n).inputOne).1.closedControl.2.1.2.1 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_closed_receiver A strategy
    hwin]
  change package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env
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
  exact package.literalRightSeamTableRootPhysicalSegmentAt_initial A strategy
    hwin env (n + 1)
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 ((env n).inputOne, (env n).inputTwo)) .both true

theorem literalCombinedFreshPhaseLiveBoth_closed_left_physicalSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env
      (n + 1)
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
  change package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env
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
  exact package.literalLeftSeamTableRootPhysicalSegmentAt_initial A strategy
    hwin env (n + 1)
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 ((env n).inputOne, (env n).inputTwo)) .both true

/-- The currently active seam table(s) carry the exact actual physical word
of their epoch. -/
def LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  match one.2.1.1.2, two.2.1.1.2 with
  | false, false =>
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
        (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
          two.2.1) one.2.1.2.1
  | true, true =>
      package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
        (package.literalCombinedFreshOneReceiver A strategy hwin one.1
          one.2.1) two.2.1.2.1
  | true, false =>
      package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
          (package.literalCombinedFreshOneReceiver A strategy hwin one.1
            one.2.1) two.2.1.2.1 ∧
        package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
          (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
            two.2.1) one.2.1.2.1
  | false, true => False

theorem literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_initial
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    package.LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt A strategy
      hwin env 0
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) := by
  change
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env 0
        (package.literalRightSeamStagedReceiverInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          .first false)
        (package.literalRightSeamStagedSenderInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)) ∧
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env 0
        (package.literalLeftSeamStagedReceiverInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          .first false)
        (package.literalLeftSeamStagedSenderInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin))
  exact ⟨
    package.literalRightSeamTableRootPhysicalSegmentAt_initial A strategy hwin
      env 0 _ .first false,
    package.literalLeftSeamTableRootPhysicalSegmentAt_initial A strategy hwin
      env 0 _ .first false⟩

theorem literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_both
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
    package.LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt A strategy
      hwin env (n + 1) oneNext twoNext := by
  dsimp only
  change
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env
        (n + 1)
        (package.literalCombinedFreshOneReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
            (env n).inputOne two (env n).inputTwo).1.closedControl.2.1)
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          (env n).inputTwo one
          (env n).inputOne).1.closedControl.2.1.2.1 ∧
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env
        (n + 1)
        (package.literalCombinedFreshTwoReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            (env n).inputTwo one (env n).inputOne).1.closedControl.2.1)
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          (env n).inputOne two
          (env n).inputTwo).1.closedControl.2.1.2.1
  exact ⟨
    package.literalCombinedFreshPhaseLiveBoth_closed_right_physicalSegment A
      strategy hwin env n one two hstructural.1,
    package.literalCombinedFreshPhaseLiveBoth_closed_left_physicalSegment A
      strategy hwin env n one two hstructural.1⟩

theorem literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_strictRight
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one, .inl two) :
          FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (OneShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
                strategy hwin package) Unit ×
            FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (TwoShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
                strategy hwin package) Unit) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .right)
    (hsegment :
      package.LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt A
        strategy hwin env n one two) :
    let oneNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one
        (env n).inputOne
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        (env n).inputTwo one (env n).inputOne).1.openControl
    package.LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt A strategy
      hwin env (n + 1) oneNext.1 twoNext := by
  dsimp only
  change package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env
    (n + 1)
    (package.literalCombinedFreshTwoReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        (env n).inputTwo one (env n).inputOne).1.openControl.2.1)
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one
        (env n).inputOne).1.2.1.2.1
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvTwo_same_physicalSegment A
      strategy hwin env n two one hstructural hpair hgraph htwo hsegment
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvTwo_same_physicalSegment A
      strategy hwin env n two one hstructural hpair hgraph htwo hsegment.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
    have hroot := hstructural.2.2
    simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at hroot
    exact package.literalCombinedFreshPhaseLiveRecvTwo_switch_physicalSegment A
      strategy hwin env n two one hstructural hpair hgraph htwo hroot.2

theorem literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hstructural :
      package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin
        one two)
    (hpair :
      ((.inl one, .inl two) :
          FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (OneShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A
                strategy hwin package) Unit ×
            FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
              (TwoShared A strategy hwin package)
              (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A
                strategy hwin package) Unit) =
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
          env n)
    (hgraph : (env n).graph = .left)
    (hsegment :
      package.LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt A
        strategy hwin env n one two) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        (env n).inputOne two (env n).inputTwo).1.openControl
    let twoNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
        (env n).inputTwo
    package.LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt A strategy
      hwin env (n + 1) oneNext twoNext.1 := by
  dsimp only
  change package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env
    (n + 1)
    (package.literalCombinedFreshOneReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        (env n).inputOne two (env n).inputTwo).1.openControl.2.1)
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
        (env n).inputTwo).1.2.1.2.1
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
    have hroot := hstructural.2.2
    simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at hroot
    exact package.literalCombinedFreshPhaseLiveRecvOne_switch_physicalSegment A
      strategy hwin env n one two hstructural hpair hgraph hone hroot.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvOne_same_physicalSegment A
      strategy hwin env n one two hstructural hpair hgraph hone hsegment.1
  · simp only [LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt,
      hone, htwo] at hsegment
    exact package.literalCombinedFreshPhaseLiveRecvOne_same_physicalSegment A
      strategy hwin env n one two hstructural hpair hgraph hone hsegment

/-! ## The actual semantic trace carries the physical segment -/

def LiteralCombinedFreshPhaseLiveCanonicalRootPhysicalSegmentSelected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (one : OneControl A strategy hwin package)
    (two : TwoControl A strategy hwin package) (n : Nat) : Prop :=
  ∃ onePending : OnePending A strategy hwin package,
    ∃ twoPending : TwoPending A strategy hwin package,
      one = .inl onePending ∧ two = .inl twoPending ∧
        package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy
          hwin onePending twoPending ∧
        package.LiteralCombinedFreshPhaseLiveTableRootPhysicalSegmentAt A
          strategy hwin env n onePending twoPending ∧
        (one, two) =
          package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
            hwin env n

/-- At every global time, the active seam table carries an exact witness
`[start,n)` of the actual semantic/reference word, pointwise equal to the
selected table play projected at row `.both`. -/
theorem literalCombinedFreshPhaseLiveRootSemanticTrace_physicalTableSegment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralCombinedFreshPhaseLiveCanonicalRootPhysicalSegmentSelected
      A strategy hwin env
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
        package.literalCombinedFreshPhaseLiveStructuralSelected_initial A
          strategy hwin,
        package.literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_initial
          A strategy hwin env,
        rfl⟩
  | succ n ih =>
      rcases ih with
        ⟨onePending, twoPending, hone, htwo, hstructural, hsegment,
          _hcanonical⟩
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
        ⟨onePending, twoPending, rfl, rfl, hstructural, hpair⟩
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
          have hstructuralNext :=
            package.literalCombinedFreshPhaseLiveStructuralSelected_strictRight
              A strategy hwin onePending twoPending hstructural
                ((env n).inputOne, (env n).inputTwo)
          have hsegmentNext :=
            package.literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_strictRight
              A strategy hwin env n onePending twoPending hstructural hpair
                hgraph hsegment
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
            (congrArg Prod.snd hpairNext).symm,
            hstructuralNext, hsegmentNext, rfl⟩

      | left =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
              onePending (env n).inputOne twoPending (env n).inputTwo
              ).1.openControl
          let twoNext : TwoPending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshTwoPendingStep A strategy hwin)
              twoPending (env n).inputTwo).1
          have hstructuralNext :=
            package.literalCombinedFreshPhaseLiveStructuralSelected_strictLeft
              A strategy hwin onePending twoPending hstructural
                ((env n).inputOne, (env n).inputTwo)
          have hsegmentNext :=
            package.literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_strictLeft
              A strategy hwin env n onePending twoPending hstructural hpair
                hgraph hsegment
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
            (congrArg Prod.snd hpairNext).symm,
            hstructuralNext, hsegmentNext, rfl⟩

      | both =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
              onePending (env n).inputOne twoPending (env n).inputTwo
              ).1.closedControl
          let twoNext : TwoPending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin
              twoPending (env n).inputTwo onePending (env n).inputOne
              ).1.closedControl
          have hstructuralNext :=
            package.literalCombinedFreshPhaseLiveStructuralSelected_both A
              strategy hwin onePending twoPending hstructural
                ((env n).inputOne, (env n).inputTwo)
          have hsegmentNext :=
            package.literalCombinedFreshPhaseLiveTableRootPhysicalSegmentAt_both
              A strategy hwin env n onePending twoPending hstructural
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
            (congrArg Prod.snd hpairNext).symm,
            hstructuralNext, hsegmentNext, rfl⟩

/-! ## Exact finite block and block minimum -/

/-- A finite consecutive slice of an omega word. -/
def phaseLiveOmegaSegment {Letter : Type*}
    (word : Nat → Letter) (start length : Nat) : List Letter :=
  List.ofFn (fun i : Fin length ↦ word (start + i))

theorem literalRightSeamSelectedTablePhysicalPlay_false
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) :
    literalRightSeamSelectedTablePhysicalPlay A strategy hwin installed false
        env n =
      profiledRawJointTargetLeftPhysicalLetter A
        (profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
          installed env n) := by
  rfl

theorem literalRightSeamSelectedTablePhysicalPlay_true
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) :
    literalRightSeamSelectedTablePhysicalPlay A strategy hwin installed true
        env n =
      profiledRawJointGuardedFirstLeftPhysicalLetter A
        (profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
          installed env n) := by
  rfl

theorem literalLeftSeamSelectedTablePhysicalPlay_false
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (n : Nat) :
    literalLeftSeamSelectedTablePhysicalPlay A strategy hwin installed false
        env n =
      profiledRawJointTargetRightPhysicalLetter A
        (profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
          installed env n) := by
  rfl

theorem literalLeftSeamSelectedTablePhysicalPlay_true
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (n : Nat) :
    literalLeftSeamSelectedTablePhysicalPlay A strategy hwin installed true
        env n =
      profiledRawJointGuardedFirstRightPhysicalLetter A
        (profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
          installed env n) := by
  rfl

/-- The finite actual word of a represented strict-left epoch is exactly the
`.both` projection of the selected right-seam table prefix. -/
theorem LiteralRightSeamTableRootPhysicalSegmentAt.exists_omegaSegment_eq
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : RightReceiver A strategy hwin package}
    {sender : RightSender A strategy hwin package}
    (hsegment :
      package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender) :
    ∃ start : Nat, ∃ past : List (In₁ × In₂),
      start + past.length = n ∧
        phaseLiveOmegaSegment
            (package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy
              hwin env) start past.length =
          omegaPrefix
            (fun j ↦ pairedLeftRecordForRow .both
              (literalRightSeamSelectedTablePhysicalPlay A strategy hwin
                (package.literalRightSeamInstalled A strategy hwin receiver.1)
                receiver.2.2.1.1
                (fun k ↦ ((env (start + k)).inputOne,
                  (env (start + k)).inputTwo)) j))
            past.length := by
  rcases hsegment with
    ⟨start, past, hend, _hinputs, _hsender, _hreceiver, hrecords⟩
  refine ⟨start, past, hend, ?_⟩
  apply List.ext_get
  · simp [phaseLiveOmegaSegment, omegaPrefix]
  · intro j hjLeft hjRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [phaseLiveOmegaSegment, omegaPrefix, List.getElem_ofFn]
    exact hrecords j (by simpa [phaseLiveOmegaSegment] using hjLeft)

/-- Strict-right mirror. -/
theorem LiteralLeftSeamTableRootPhysicalSegmentAt.exists_omegaSegment_eq
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : LeftReceiver A strategy hwin package}
    {sender : LeftSender A strategy hwin package}
    (hsegment :
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender) :
    ∃ start : Nat, ∃ past : List (In₂ × In₁),
      start + past.length = n ∧
        phaseLiveOmegaSegment
            (package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy
              hwin env) start past.length =
          omegaPrefix
            (fun j ↦ pairedRightRecordForRow .both
              (literalLeftSeamSelectedTablePhysicalPlay A strategy hwin
                (package.literalLeftSeamInstalled A strategy hwin receiver.1)
                receiver.2.2.1.1
                (fun k ↦ ((env (start + k)).inputTwo,
                  (env (start + k)).inputOne)) j))
            past.length := by
  rcases hsegment with
    ⟨start, past, hend, _hinputs, _hsender, _hreceiver, hrecords⟩
  refine ⟨start, past, hend, ?_⟩
  apply List.ext_get
  · simp [phaseLiveOmegaSegment, omegaPrefix]
  · intro j hjLeft hjRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [phaseLiveOmegaSegment, omegaPrefix, List.getElem_ofFn]
    exact hrecords j (by simpa [phaseLiveOmegaSegment] using hjLeft)

/-- DPA entry state used by the selected right-table member at a given row. -/
def literalRightSeamSelectedTableEntryState
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (row : PairedEntryRow) : A.State :=
  if anchor then
    pairedCodeStateForRow A row (installed.world.procTwoSlot A).1.1
  else
    pairedCodeStateForRow A row
      (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        installed).source.1.1

/-- Mirror entry state. -/
def literalLeftSeamSelectedTableEntryState
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (row : PairedEntryRow) : A.State :=
  if anchor then
    pairedCodeStateForRow A row (installed.world.procOneSlot A).1.1
  else
    pairedCodeStateForRow A row
      (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed).source.1.1

/-- Exact block-minimum readback for a represented strict-left epoch. -/
theorem LiteralRightSeamTableRootPhysicalSegmentAt.exists_actualBlockMin_eq
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : RightReceiver A strategy hwin package}
    {sender : RightSender A strategy hwin package}
    (hsegment :
      package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender) :
    ∃ start : Nat, ∃ past : List (In₁ × In₂),
      start + past.length = n ∧
        A.priority
            (blockMinState A
              (literalRightSeamSelectedTableEntryState A strategy hwin
                (package.literalRightSeamInstalled A strategy hwin receiver.1)
                receiver.2.2.1.1 .both)
              (phaseLiveOmegaSegment
                (package.literalCombinedFreshPhaseLiveRootSemanticWord A
                  strategy hwin env) start past.length)) =
          literalRightSeamSelectedTableBlockPriority A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (fun k ↦ ((env (start + k)).inputOne,
              (env (start + k)).inputTwo)) past.length .both := by
  obtain ⟨start, past, hend, hword⟩ :=
    hsegment.exists_omegaSegment_eq A strategy hwin package env n
  refine ⟨start, past, hend, ?_⟩
  rw [hword]
  cases hanchor : receiver.2.2.1.1
  · simp [literalRightSeamSelectedTableEntryState,
      literalRightSeamSelectedTableBlockPriority, hanchor,
      literalRightSeamSelectedTablePhysicalPlay_false,
      profiledRawJointTargetLeftPhysicalPrefixRecords, omegaPrefix]
    rfl
  · simp [literalRightSeamSelectedTableEntryState,
      literalRightSeamSelectedTableBlockPriority, hanchor,
      literalRightSeamSelectedTablePhysicalPlay_true,
      profiledRawJointGuardedFirstLeftPhysicalPrefixRecords, omegaPrefix]
    rfl

/-- Exact mirror block-minimum readback. -/
theorem LiteralLeftSeamTableRootPhysicalSegmentAt.exists_actualBlockMin_eq
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : LeftReceiver A strategy hwin package}
    {sender : LeftSender A strategy hwin package}
    (hsegment :
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender) :
    ∃ start : Nat, ∃ past : List (In₂ × In₁),
      start + past.length = n ∧
        A.priority
            (blockMinState A
              (literalLeftSeamSelectedTableEntryState A strategy hwin
                (package.literalLeftSeamInstalled A strategy hwin receiver.1)
                receiver.2.2.1.1 .both)
              (phaseLiveOmegaSegment
                (package.literalCombinedFreshPhaseLiveRootSemanticWord A
                  strategy hwin env) start past.length)) =
          literalLeftSeamSelectedTableBlockPriority A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (fun k ↦ ((env (start + k)).inputTwo,
              (env (start + k)).inputOne)) past.length .both := by
  obtain ⟨start, past, hend, hword⟩ :=
    hsegment.exists_omegaSegment_eq A strategy hwin package env n
  refine ⟨start, past, hend, ?_⟩
  rw [hword]
  cases hanchor : receiver.2.2.1.1
  · simp [literalLeftSeamSelectedTableEntryState,
      literalLeftSeamSelectedTableBlockPriority, hanchor,
      literalLeftSeamSelectedTablePhysicalPlay_false,
      profiledRawJointTargetRightPhysicalPrefixRecords, omegaPrefix]
    rfl
  · simp [literalLeftSeamSelectedTableEntryState,
      literalLeftSeamSelectedTableBlockPriority, hanchor,
      literalLeftSeamSelectedTablePhysicalPlay_true,
      profiledRawJointGuardedFirstRightPhysicalPrefixRecords, omegaPrefix]
    rfl

/-- The semantic word used above is literally the executable finite
controller's global trace word. -/
theorem literalCombinedFreshPhaseLiveRootSemanticWord_eq_actualTraceWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env =
      let controller :=
        package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
          hwin
      controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env := by
  dsimp only
  exact
    (package.literalCombinedFreshPhaseLiveRootSemanticWord_eq_referenceWord A
      strategy hwin env).trans
      (package.literalCombinedFreshPhaseLiveRootTraceWord_eq_referenceWord A
        strategy hwin env).symm

/-- The live `.both` target exposed by a represented right-seam table has
exactly the minimum priority of the actual executable word on `[start,n)`. -/
theorem
    LiteralRightSeamTableRootPhysicalSegmentAt.exists_targetPriority_eq_actualBlockMin
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : RightReceiver A strategy hwin package}
    {sender : RightSender A strategy hwin package}
    (hsegment :
      package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender) :
    ∃ start : Nat, ∃ past : List (In₁ × In₂),
      ∃ slot : ProfiledRawRightSlot A,
        start + past.length = n ∧
          (literalRightSeamSelectedTableTargetCode A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (fun k ↦ ((env (start + k)).inputOne,
              (env (start + k)).inputTwo)) past.length .both).family.right () =
              some slot ∧
          profiledRawJointThreadRootPriority A (.inl slot) =
            A.priority
              (blockMinState A
                (literalRightSeamSelectedTableEntryState A strategy hwin
                  (package.literalRightSeamInstalled A strategy hwin
                    receiver.1) receiver.2.2.1.1 .both)
                (phaseLiveOmegaSegment
                  (package.literalCombinedFreshPhaseLiveRootSemanticWord A
                    strategy hwin env) start past.length)) := by
  obtain ⟨start, past, hend, hminimum⟩ :=
    hsegment.exists_actualBlockMin_eq A strategy hwin package env n
  obtain ⟨slot, hlive, hpriority⟩ :=
    exists_literalRightSeamSelectedTable_bothTargetPriority_eq_blockMin A
      strategy hwin
      (package.literalRightSeamInstalled A strategy hwin receiver.1)
      receiver.2.2.1.1
      (fun k ↦ ((env (start + k)).inputOne,
        (env (start + k)).inputTwo)) past.length
  exact ⟨start, past, slot, hend, hlive, hpriority.trans hminimum.symm⟩

/-- Mirror live-target/actual-block-minimum equation. -/
theorem
    LiteralLeftSeamTableRootPhysicalSegmentAt.exists_targetPriority_eq_actualBlockMin
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    {receiver : LeftReceiver A strategy hwin package}
    {sender : LeftSender A strategy hwin package}
    (hsegment :
      package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender) :
    ∃ start : Nat, ∃ past : List (In₂ × In₁),
      ∃ slot : ProfiledRawLeftSlot A,
        start + past.length = n ∧
          (literalLeftSeamSelectedTableTargetCode A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (fun k ↦ ((env (start + k)).inputTwo,
              (env (start + k)).inputOne)) past.length .both).family.left () =
              some slot ∧
          profiledRawJointThreadRootPriority A (.inr slot) =
            A.priority
              (blockMinState A
                (literalLeftSeamSelectedTableEntryState A strategy hwin
                  (package.literalLeftSeamInstalled A strategy hwin receiver.1)
                  receiver.2.2.1.1 .both)
                (phaseLiveOmegaSegment
                  (package.literalCombinedFreshPhaseLiveRootSemanticWord A
                    strategy hwin env) start past.length)) := by
  obtain ⟨start, past, hend, hminimum⟩ :=
    hsegment.exists_actualBlockMin_eq A strategy hwin package env n
  obtain ⟨slot, hlive, hpriority⟩ :=
    exists_literalLeftSeamSelectedTable_bothTargetPriority_eq_blockMin A
      strategy hwin
      (package.literalLeftSeamInstalled A strategy hwin receiver.1)
      receiver.2.2.1.1
      (fun k ↦ ((env (start + k)).inputTwo,
        (env (start + k)).inputOne)) past.length
  exact ⟨start, past, slot, hend, hlive, hpriority.trans hminimum.symm⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
