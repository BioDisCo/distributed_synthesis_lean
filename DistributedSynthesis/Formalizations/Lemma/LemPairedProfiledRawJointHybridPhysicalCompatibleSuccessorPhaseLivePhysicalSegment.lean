/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveLiteralSegment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLiteralPrefixSchedule

/-!
# Exact physical segments carried by the compatible successor phase overlay

The literal-segment invariant identifies the exact consecutive input epoch of
each live table.  This module adds the corresponding physical-word equality.
For a selected strict table, the blind sender output and the informed receiver
output are the two coordinates of the same decorated table letter.  Hence a
live epoch is not merely an abstract fold: it is a literal prefix of the
physical trace.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

private abbrev OnePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending A strategy hwin
    policy

private abbrev TwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending A strategy hwin
    policy

private abbrev OneControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy hwin
      policy) PUnit PUnit

private abbrev TwoControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy hwin
      policy) PUnit PUnit

/-! ## Explicit semantic physical word -/

/-- The semantic word underlying the proved Moore trace invariant. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputOne A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n
      outputTwo :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticOutputTwo A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n }

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_eq_referenceWord
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env =
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveTraceInvariant A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          hinitial env).referenceWord
        (profiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalController A
          strategy hwin policy initialOne initialTwo fallbackLeft
            fallbackRight) := by
  rfl

/-! ## Pending semantic record equations -/

/-- In a strict-right round the explicit semantic word is the record formed
by the selected right owner and receiver computations. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictRight_pending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env n =
      rightRoundRecord ((env n).inputTwo, (env n).inputOne)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
          strategy hwin policy one.1 one.2.1.baseShared
            (env n).inputOne).2
        (profiledRawJointHybridPhysicalCompatibleRightInformedOutputAtRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy two one))
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A
            strategy hwin policy fallbackRight two one
              ((env n).inputTwo, (env n).inputOne)).1) := by
  have hselected :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalSelected A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env (.inl one) (.inl two) n :=
    ⟨one, two, rfl, rfl, hinvariant, hpair⟩
  have houtputs :=
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws A
      strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env).strictRight n (.inl one) (.inl two) trivial hselected
          hgraph |>.2
  unfold profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
  rw [← houtputs.1, ← houtputs.2]
  simp [hgraph, rightRoundRecord,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
    FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep]
  constructor <;> rfl

/-! ## Literal selected-table record equations -/

/-- Prefix-indexed form of the local output theorem.  Unlike the convenient
`omegaOfList` presentation, this form keeps one fixed local environment while
an epoch is extended. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt.output_eq_play_of_prefix
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State}
    {past : List (In₂ × In₁)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A
        strategy hwin policy state move owner monitorState past)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁) (n : Nat)
    (hpast : past = omegaPrefix localEnv n) :
    (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState (localEnv n)).1 =
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1 := by
  rcases hreach with ⟨howner, hmonitor⟩
  subst owner
  subst monitorState
  cases tableMember <;>
    simp [profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay,
      profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor,
      treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
      TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
      hpast] <;> rfl

/-- The concrete selected right owner/receiver computation is exactly one
row of the decorated right physical letter. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightRecord_eq_play
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State)
    (staged : Option (RightOutput A strategy hwin initial))
    (past : List (In₂ × In₁))
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A
        strategy hwin policy state move ownerControl monitorState past)
    (tableMember ownerMember : Bool) (localEnv : Nat → In₂ × In₁)
    (n : Nat) (hpast : past = omegaPrefix localEnv n) :
    rightRoundRecord (localEnv n)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
          strategy hwin policy ownerMember
            ⟨state, .inr ⟨move, ownerControl⟩⟩ (localEnv n).2).2
        (profiledRawJointHybridPhysicalCompatibleRightInformedOutputAtRow A
          strategy hwin row
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
            strategy hwin policy fallbackRight
              ⟨state, .inr ⟨move, ownerControl⟩⟩
              ⟨state, some ⟨move, row, monitorState, staged⟩⟩
              (localEnv n)).1) =
      pairedRightRecordForRow row
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
            strategy hwin policy state move tableMember localEnv n)) := by
  have houtput := hreach.output_eq_play_of_prefix A strategy hwin tableMember
    row localEnv n hpast
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep_live,
    houtput]
  simp only
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep]
  rw [hreach.1]
  simp only [profiledRawJointHybridPhysicalCompatibleRightSharedStep]
  rw [(profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).output_eq
    ownerMember tableMember
      ((move.memberController A false).controlAt (senderWord past))
      (localEnv n).2]
  cases row <;> simp
    [profiledRawJointHybridPhysicalCompatibleRightSharedStep,
      pairedRightRecordForRow, rightRoundRecord,
      profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter,
      profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay,
      profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_sender,
      profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection,
      profiledRawJointHybridPhysicalCompatibleRightInformedOutputAtRow,
      profiledRawJointRightPhysicalSiblingDeferredStep, narrowedInducedTree,
      branchNode_eq_omegaPrefix, hpast, treePlay, blockLabelApply] <;> rfl

/-- Strict-left semantic record mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictLeft_pending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env n =
      leftRoundRecord ((env n).inputOne, (env n).inputTwo)
        (profiledRawJointHybridPhysicalCompatibleLeftInformedOutputAtRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy one two))
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A
            strategy hwin policy fallbackLeft one two
              ((env n).inputOne, (env n).inputTwo)).1)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
          strategy hwin policy two.1 two.2.1.baseShared
            (env n).inputTwo).2 := by
  have hselected :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalSelected A
        strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env (.inl one) (.inl two) n :=
    ⟨one, two, rfl, rfl, hinvariant, hpair⟩
  have houtputs :=
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveSelectedTraceLaws A
      strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env).strictLeft n (.inl one) (.inl two) trivial hselected
          hgraph |>.2
  unfold profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
  rw [← houtputs.1, ← houtputs.2]
  simp [hgraph, leftRoundRecord,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
    FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
  constructor <;> rfl

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt.output_eq_play_of_prefix
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {past : List (In₁ × In₂)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
        hwin policy state move owner monitorState past)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂) (n : Nat)
    (hpast : past = omegaPrefix localEnv n) :
    (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState (localEnv n)).1 =
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1 := by
  rcases hreach with ⟨howner, hmonitor⟩
  subst owner
  subst monitorState
  cases tableMember <;>
    simp [profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay,
      profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor,
      treePlay, narrowedInducedTree, blockLabelApply,
      TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
      hpast] <;> rfl

/-- Left selected owner/receiver computation is the corresponding decorated
left physical record. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftRecord_eq_play
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (LeftOutput A strategy hwin initial))
    (past : List (In₁ × In₂))
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
        hwin policy state move ownerControl monitorState past)
    (tableMember ownerMember : Bool) (localEnv : Nat → In₁ × In₂)
    (n : Nat) (hpast : past = omegaPrefix localEnv n) :
    leftRoundRecord (localEnv n)
        (profiledRawJointHybridPhysicalCompatibleLeftInformedOutputAtRow A
          strategy hwin row
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A
            strategy hwin policy fallbackLeft
              ⟨state, .inr ⟨move, ownerControl⟩⟩
              ⟨state, some ⟨move, row, monitorState, staged⟩⟩
              (localEnv n)).1)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
          strategy hwin policy ownerMember
            ⟨state, .inr ⟨move, ownerControl⟩⟩ (localEnv n).2).2 =
      pairedLeftRecordForRow row
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n)) := by
  have houtput := hreach.output_eq_play_of_prefix A strategy hwin tableMember
    row localEnv n hpast
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep_live,
    houtput]
  simp only
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
  rw [hreach.1]
  simp only [profiledRawJointHybridPhysicalCompatibleLeftSharedStep]
  rw [(profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).output_eq
    ownerMember tableMember
      ((move.memberController A false).controlAt (senderWord past))
      (localEnv n).2]
  cases row <;> simp
    [pairedLeftRecordForRow, leftRoundRecord,
      profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter,
      profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay,
      profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_sender,
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection,
      profiledRawJointHybridPhysicalCompatibleLeftInformedOutputAtRow,
      profiledRawJointLeftPhysicalSiblingDeferredStep, narrowedInducedTree,
      branchNode_eq_omegaPrefix, hpast, treePlay, blockLabelApply] <;> rfl

/-! ## Physical literal epochs -/

/-- A right table is a literal prefix of `word`, beginning at its exact
installation time.  The local environment is definitionally the physical
input suffix from that time. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (tableMember : Bool)
    (owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A
      strategy hwin policy)
    (receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
        hwin (initial := initial)) : Prop :=
  ∃ (start : Nat)
      (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
        hwin initial)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false).State)
      (staged : Option (RightOutput A strategy hwin initial)),
    start ≤ n ∧
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
        hwin policy state move tableMember row
          (fun j ↦ ((env (start + j)).inputTwo,
            (env (start + j)).inputOne))
          ownerControl monitorState word start (n - start)

/-- Fresh right installation starts an empty physical epoch. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (tableMember : Bool)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt A
      strategy hwin policy env word n tableMember
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerInitial A
          strategy hwin policy state)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverInitial
          A strategy hwin state row) := by
  refine ⟨n, state, move,
    (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move false).initial,
    row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move false).initial,
    none, le_rfl, ?_, ?_, ?_⟩
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerInitial,
      profiledRawJointHybridPhysicalCompatibleRightSharedInitial, hmove]
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverInitial,
        profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]
  · simpa using
      (ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt.initial A
        strategy hwin policy state move tableMember row
          (fun j ↦ ((env (n + j)).inputTwo, (env (n + j)).inputOne)) word n)

/-- One strict-right semantic round appends the actual physical record to a
right epoch. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt.stepSemantic
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .right)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          n tableMember one.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy two one)) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt A
      strategy hwin policy env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        (n + 1) tableMember
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
          strategy hwin policy one.1 one.2.1.baseShared
            (env n).inputOne).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A
          strategy hwin policy fallbackRight two one
            ((env n).inputTwo, (env n).inputOne)).2 := by
  rcases segment with
    ⟨start, state, move, ownerControl, row, monitorState, staged,
      hstart, howner, hreceiver, hliteral⟩
  let localEnv : Nat → In₂ × In₁ :=
    fun j ↦ ((env (start + j)).inputTwo, (env (start + j)).inputOne)
  have hindex : start + (n - start) = n := Nat.add_sub_of_le hstart
  have hinput : localEnv (n - start) =
      ((env n).inputTwo, (env n).inputOne) := by
    simp only [localEnv, hindex]
  have hsemantic :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictRight_pending
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env n one two hinvariant hpair hgraph
  have hrow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one) = row := by
    rw [hreceiver]
    rfl
  rw [hrow] at hsemantic
  have hplay :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightRecord_eq_play A
      strategy hwin policy fallbackRight state move ownerControl row
        monitorState staged
        (omegaPrefix localEnv (n - start)) hliteral.literal_reachable
        tableMember one.1 localEnv (n - start) rfl
  rw [hinput] at hplay
  have hplay' := hplay
  rw [← howner, ← hreceiver] at hplay'
  have hrecord :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
          hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (start + (n - start)) =
        pairedRightRecordForRow row
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv
                (n - start))) := by
    rw [hindex]
    exact hsemantic.trans (by simpa using hplay')
  let result :=
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
      hwin policy state move ownerControl row monitorState
        ((env n).inputTwo, (env n).inputOne)
  have hliteralNext := hliteral.step A strategy hwin hrecord
  refine ⟨start, state, move,
    (move.memberController A false).step ownerControl (env n).inputOne,
    row, result.2.2.2.1, some result.1, Nat.le_trans hstart (by omega),
    ?_, ?_, ?_⟩
  · rw [howner]
    simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep,
      profiledRawJointHybridPhysicalCompatibleRightSharedStep]
    exact
      (profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).state_eq
        one.1 false ownerControl (env n).inputOne
  · simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight]
    rw [howner, hreceiver]
    simp [
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep,
      result]
    rfl
  · have hlength : n + 1 - start = (n - start) + 1 := by omega
    rw [hindex] at hliteralNext
    rw [hlength]
    exact hliteralNext

/-- Left physical-epoch mirror. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (tableMember : Bool)
    (owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A
      strategy hwin policy)
    (receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
        hwin (initial := initial)) : Prop :=
  ∃ (start : Nat)
      (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
        hwin initial)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
          strategy hwin (initial := initial) move false).State)
      (staged : Option (LeftOutput A strategy hwin initial)),
    start ≤ n ∧
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
        hwin policy state move tableMember row
          (fun j ↦ ((env (start + j)).inputOne,
            (env (start + j)).inputTwo))
          ownerControl monitorState word start (n - start)

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (tableMember : Bool)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
      strategy hwin policy env word n tableMember
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerInitial A
          strategy hwin policy state)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverInitial A
          strategy hwin state row) := by
  refine ⟨n, state, move,
    (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move false).initial,
    row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := initial) move false).initial,
    none, le_rfl, ?_, ?_, ?_⟩
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerInitial,
      profiledRawJointHybridPhysicalCompatibleLeftSharedInitial, hmove]
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverInitial,
        profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]
  · simpa using
      (ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt.initial A
        strategy hwin policy state move tableMember row
          (fun j ↦ ((env (n + j)).inputOne, (env (n + j)).inputTwo)) word n)

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt.stepSemantic
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .left)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
        strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          n tableMember two.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy one two)) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
      strategy hwin policy env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        (n + 1) tableMember
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
          strategy hwin policy two.1 two.2.1.baseShared
            (env n).inputTwo).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A
          strategy hwin policy fallbackLeft one two
            ((env n).inputOne, (env n).inputTwo)).2 := by
  rcases segment with
    ⟨start, state, move, ownerControl, row, monitorState, staged,
      hstart, howner, hreceiver, hliteral⟩
  let localEnv : Nat → In₁ × In₂ :=
    fun j ↦ ((env (start + j)).inputOne, (env (start + j)).inputTwo)
  have hindex : start + (n - start) = n := Nat.add_sub_of_le hstart
  have hinput : localEnv (n - start) =
      ((env n).inputOne, (env n).inputTwo) := by
    simp only [localEnv, hindex]
  have hsemantic :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictLeft_pending
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env n one two hinvariant hpair hgraph
  have hrow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two) = row := by
    rw [hreceiver]
    rfl
  rw [hrow] at hsemantic
  have hplay :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftRecord_eq_play A
      strategy hwin policy fallbackLeft state move ownerControl row monitorState
        staged (omegaPrefix localEnv (n - start))
        hliteral.literal_reachable tableMember two.1 localEnv (n - start) rfl
  rw [hinput] at hplay
  have hplay' := hplay
  rw [← howner, ← hreceiver] at hplay'
  have hrecord :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
          hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (start + (n - start)) =
        pairedLeftRecordForRow row
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv
                (n - start))) := by
    rw [hindex]
    exact hsemantic.trans (by simpa using hplay')
  let result :=
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy hwin
      policy state move ownerControl row monitorState
        ((env n).inputOne, (env n).inputTwo)
  have hliteralNext := hliteral.step A strategy hwin hrecord
  refine ⟨start, state, move,
    (move.memberController A false).step ownerControl (env n).inputTwo,
    row, result.2.2.2.1, some result.1, Nat.le_trans hstart (by omega),
    ?_, ?_, ?_⟩
  · rw [howner]
    simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep,
      profiledRawJointHybridPhysicalCompatibleLeftSharedStep]
    exact
      (profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).state_eq
        two.1 false ownerControl (env n).inputTwo
  · simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft]
    rw [howner, hreceiver]
    simp [
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep,
      result]
    rfl
  · have hlength : n + 1 - start = (n - start) + 1 := by omega
    rw [hindex] at hliteralNext
    rw [hlength]
    exact hliteralNext

/-! ## Fresh physical epochs -/

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_physicalSegment_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (parent : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A
      strategy hwin policy)
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (receiverMember : Bool)
    (root : ProfiledRawJointThreadRoot A)
    (htarget :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy state (output.target entryRow).1 .right root) :
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output entryRow
    let owner :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner A
        strategy hwin policy parent payload
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
          (receiverMember, owner, payload)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt A
      strategy hwin policy env word n receiverMember owner
        ⟨installed.1.1, installed.2⟩ := by
  dsimp only
  rcases htarget.transition with ⟨transition⟩
  obtain ⟨move, hmove⟩ := transition.right_move A strategy hwin
  cases receiverMember with
  | false =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner,
          profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt_initial
            A strategy hwin policy env word n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove false .first)
  | true =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner,
          profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt_initial
            A strategy hwin policy env word n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove true .both)

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_physicalSegment_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (parent : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A
      strategy hwin policy)
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (receiverMember : Bool)
    (root : ProfiledRawJointThreadRoot A)
    (htarget :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy state (output.target entryRow).1 .left root) :
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output entryRow
    let owner :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner A
        strategy hwin policy parent payload
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
          (receiverMember, owner, payload)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
      strategy hwin policy env word n receiverMember owner
        ⟨installed.1.1, installed.2⟩ := by
  dsimp only
  rcases htarget.transition with ⟨transition⟩
  obtain ⟨move, hmove⟩ := transition.left_move A strategy hwin
  cases receiverMember with
  | false =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner,
          profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt_initial
            A strategy hwin policy env word n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove false .first)
  | true =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner,
          profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt_initial
            A strategy hwin policy env word n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove true .both)

/-! ## Phase-selected physical epochs -/

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt A
    strategy hwin policy env word n one.1 one.2.1.baseShared
      (two.2.1.receiver two.1)

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
    strategy hwin policy env word n two.1 two.2.1.baseShared
      (one.2.1.receiver one.1)

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (one : OnePending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt A
    strategy hwin policy env word n one.1 one.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver A
        strategy hwin policy one)

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
    strategy hwin policy env word n two.1 two.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver A
        strategy hwin policy two)

def ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  match one.2.1.localPhase, two.2.1.localPhase with
  | false, false =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt
          A strategy hwin policy env word n one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchPhysicalSegmentAt
          A strategy hwin policy env word n two
  | true, true =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt
          A strategy hwin policy env word n one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchPhysicalSegmentAt
          A strategy hwin policy env word n one
  | true, false =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt
          A strategy hwin policy env word n one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt
          A strategy hwin policy env word n one two
  | false, true => False

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt.right_selected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {n : Nat} {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env word n one two) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt A
      strategy hwin policy env word n one.1 one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
          A strategy hwin policy two one) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt]
      at hsegment
    exact hsegment.1
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo] at hsegment
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt]
      at hsegment
    exact hsegment.1
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_switch
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchPhysicalSegmentAt]
      at hsegment
    exact hsegment.2

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt.left_selected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {n : Nat} {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env word n one two) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
      strategy hwin policy env word n two.1 two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
          A strategy hwin policy one two) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_switch
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchPhysicalSegmentAt]
      at hsegment
    exact hsegment.2
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo] at hsegment
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt]
      at hsegment
    exact hsegment.2
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt]
      at hsegment
    exact hsegment.1

/-! ## Fresh phase transport -/

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_open_leftSwitchPhysicalSegment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchPhysicalSegmentAt
      A strategy hwin policy env word (n + 1) fresh.1.2.openControl := by
  dsimp only
  let selected := hinvariant.right_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_targetAt A strategy hwin fallbackRight
      ((env n).inputTwo, (env n).inputOne) false
  have hfresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_physicalSegment_of_targetAt
      A strategy hwin policy env word (n + 1) one.2.1.baseShared.1
        two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A
          strategy hwin policy fallbackRight two one
            ((env n).inputTwo, (env n).inputOne)).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one))
        false (.inr slot) htarget
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchPhysicalSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoBasePending,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.basePending]
    using hfresh

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_open_rightSwitchPhysicalSegment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchPhysicalSegmentAt
      A strategy hwin policy env word (n + 1) fresh.1.1.openControl := by
  dsimp only
  let selected := hinvariant.left_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_targetAt A strategy hwin fallbackLeft
      ((env n).inputOne, (env n).inputTwo) false
  have hfresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_physicalSegment_of_targetAt
      A strategy hwin policy env word (n + 1) two.2.1.baseShared.1
        one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
          hwin policy fallbackLeft one two
            ((env n).inputOne, (env n).inputTwo)).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two))
        false (.inl slot) htarget
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchPhysicalSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveOneBasePending,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.basePending]
    using hfresh

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_closed_bothPhysicalSegments
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt
        A strategy hwin policy env word (n + 1) fresh.1.1.closedControl
          fresh.1.2.closedControl ∧
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt
        A strategy hwin policy env word (n + 1) fresh.1.1.closedControl
          fresh.1.2.closedControl := by
  dsimp only
  let rightSelected := hinvariant.right_selected A strategy hwin
  let leftSelected := hinvariant.left_selected A strategy hwin
  obtain ⟨rightSlot, rightTarget⟩ :=
    rightSelected.exists_targetAt A strategy hwin fallbackRight
      ((env n).inputTwo, (env n).inputOne) true
  obtain ⟨leftSlot, leftTarget⟩ :=
    leftSelected.exists_targetAt A strategy hwin fallbackLeft
      ((env n).inputOne, (env n).inputTwo) true
  have hright :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_physicalSegment_of_targetAt
      A strategy hwin policy env word (n + 1) two.2.1.baseShared.1
        one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
          hwin policy fallbackLeft one two
            ((env n).inputOne, (env n).inputTwo)).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two))
        true (.inl leftSlot) leftTarget
  have hleft :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_physicalSegment_of_targetAt
      A strategy hwin policy env word (n + 1) one.2.1.baseShared.1
        two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A
          strategy hwin policy fallbackRight two one
            ((env n).inputTwo, (env n).inputOne)).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one))
        true (.inr rightSlot) rightTarget
  constructor
  · simpa
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedRightReceiver,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
      using hright
  · simpa
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedLeftReceiver,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
      using hleft

/-! ## Preservation by the semantic trace -/

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt.strictRight
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          n one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .right) :
    let oneNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A
          strategy hwin policy) one (env n).inputOne).1
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    let twoNext := fresh.1.2.openControl
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
      A strategy hwin policy env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        (n + 1) oneNext twoNext := by
  dsimp only
  let selected := hsegment.right_selected A strategy hwin
  have hright := selected.stepSemantic A strategy hwin policy initialOne
    initialTwo fallbackLeft fallbackRight hinitial env n one two hinvariant hpair
      hgraph one.1
  have hleft :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_open_leftSwitchPhysicalSegment
      A strategy hwin policy fallbackLeft fallbackRight env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        n one two hinvariant
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentPhysicalSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep]
    using And.intro hright hleft

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt.strictLeft
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          n one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .left) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    let oneNext := fresh.1.1.openControl
    let twoNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A
          strategy hwin policy) two (env n).inputTwo).1
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
      A strategy hwin policy env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        (n + 1) oneNext twoNext := by
  dsimp only
  let selected := hsegment.left_selected A strategy hwin
  have hleft := selected.stepSemantic A strategy hwin policy initialOne
    initialTwo fallbackLeft fallbackRight hinitial env n one two hinvariant hpair
      hgraph two.1
  have hright :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_open_rightSwitchPhysicalSegment
      A strategy hwin policy fallbackLeft fallbackRight env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        n one two hinvariant
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentPhysicalSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
    using And.intro hleft hright

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt.both
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (_hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          n one two) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
      A strategy hwin policy env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        (n + 1) fresh.1.1.closedControl fresh.1.2.closedControl := by
  dsimp only
  have hboth :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_closed_bothPhysicalSegments
      A strategy hwin policy fallbackLeft fallbackRight env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        n one two hinvariant
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair]
    using hboth

/-! ## All-time physical-segment induction -/

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalPhysicalSegmentSelected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (one : OneControl A strategy hwin policy)
    (two : TwoControl A strategy hwin policy) (n : Nat) : Prop :=
  ∃ onePending : OnePending A strategy hwin policy,
    ∃ twoPending : TwoPending A strategy hwin policy,
      one = .inl onePending ∧ two = .inl twoPending ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
            strategy hwin policy onePending twoPending ∧
          ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
              A strategy hwin policy env
                (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env)
                n onePending twoPending ∧
            (one, two) =
              profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
                strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight env n

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace_physicalSegments
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo) : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalPhysicalSegmentSelected
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n).2 n := by
  intro n
  induction n with
  | zero =>
      exact ⟨initialOne, initialTwo, rfl, rfl, hinitial, hsegmentInitial, rfl⟩
  | succ n ih =>
      rcases ih with
        ⟨onePending, twoPending, hone, htwo, hinvariant, hsegment,
          hcanonical⟩
      have hpair :
          ((.inl onePending : OneControl A strategy hwin policy),
            (.inl twoPending : TwoControl A strategy hwin policy)) =
            profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env n := by
        apply Prod.ext
        · exact hone.symm
        · exact htwo.symm
      cases hgraph : (env n).graph with
      | right =>
          let oneNext : OnePending A strategy hwin policy :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep
                A strategy hwin policy) onePending (env n).inputOne).1
          let fresh :=
            profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v,
              x, y, s, max u v x y s, max u v x y s, max u v x y s,
              max u v x y s} A strategy hwin policy fallbackLeft fallbackRight
                onePending twoPending
                  ((env n).inputOne, (env n).inputTwo)
          let twoNext : TwoPending A strategy hwin policy :=
            fresh.1.2.openControl
          have hinvariantNext := hinvariant.strictRight A strategy hwin
            fallbackLeft fallbackRight
              ((env n).inputOne, (env n).inputTwo)
          have hsegmentNext := hsegment.strictRight A strategy hwin policy
            initialOne initialTwo fallbackLeft fallbackRight hinitial env n
              onePending twoPending hinvariant hpair hgraph
          have hnext :
              ((.inl oneNext : OneControl A strategy hwin policy),
                (.inl twoNext : TwoControl A strategy hwin policy)) =
                profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env (n + 1) := by
            simpa
              [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph, oneNext, twoNext, fresh]
              using congrArg
                (fun controls : OneControl A strategy hwin policy ×
                    TwoControl A strategy hwin policy ↦
                  ((profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne
                      A strategy hwin policy controls.1
                        (env n).inputOne).1,
                    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo
                      A strategy hwin policy initialTwo fallbackLeft
                        fallbackRight controls.2 (env n).inputTwo controls.1
                          (env n).inputOne).1))
                hpair
          refine ⟨oneNext, twoNext, congrArg Prod.fst hnext.symm,
            congrArg Prod.snd hnext.symm, hinvariantNext, hsegmentNext, ?_⟩
          exact Prod.eta _
      | left =>
          let fresh :=
            profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v,
              x, y, s, max u v x y s, max u v x y s, max u v x y s,
              max u v x y s} A strategy hwin policy fallbackLeft fallbackRight
                onePending twoPending
                  ((env n).inputOne, (env n).inputTwo)
          let oneNext : OnePending A strategy hwin policy :=
            fresh.1.1.openControl
          let twoNext : TwoPending A strategy hwin policy :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep
                A strategy hwin policy) twoPending (env n).inputTwo).1
          have hinvariantNext := hinvariant.strictLeft A strategy hwin
            fallbackLeft fallbackRight
              ((env n).inputOne, (env n).inputTwo)
          have hsegmentNext := hsegment.strictLeft A strategy hwin policy
            initialOne initialTwo fallbackLeft fallbackRight hinitial env n
              onePending twoPending hinvariant hpair hgraph
          have hnext :
              ((.inl oneNext : OneControl A strategy hwin policy),
                (.inl twoNext : TwoControl A strategy hwin policy)) =
                profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env (n + 1) := by
            simpa
              [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph, oneNext, twoNext, fresh]
              using congrArg
                (fun controls : OneControl A strategy hwin policy ×
                    TwoControl A strategy hwin policy ↦
                  ((profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne
                      A strategy hwin policy initialOne fallbackLeft
                        fallbackRight controls.1 (env n).inputOne controls.2
                          (env n).inputTwo).1,
                    (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo
                      A strategy hwin policy controls.2
                        (env n).inputTwo).1))
                hpair
          refine ⟨oneNext, twoNext, congrArg Prod.fst hnext.symm,
            congrArg Prod.snd hnext.symm, hinvariantNext, hsegmentNext, ?_⟩
          exact Prod.eta _
      | both =>
          let fresh :=
            profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v,
              x, y, s, max u v x y s, max u v x y s, max u v x y s,
              max u v x y s} A strategy hwin policy fallbackLeft fallbackRight
                onePending twoPending
                  ((env n).inputOne, (env n).inputTwo)
          let oneNext : OnePending A strategy hwin policy :=
            fresh.1.1.closedControl
          let twoNext : TwoPending A strategy hwin policy :=
            fresh.1.2.closedControl
          have hinvariantNext := hinvariant.both A strategy hwin fallbackLeft
            fallbackRight ((env n).inputOne, (env n).inputTwo)
          have hsegmentNext := hsegment.both A strategy hwin policy initialOne
            initialTwo fallbackLeft fallbackRight env n onePending twoPending
              hinvariant
          have hnext :
              ((.inl oneNext : OneControl A strategy hwin policy),
                (.inl twoNext : TwoControl A strategy hwin policy)) =
                profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env (n + 1) := by
            simpa
              [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
                FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
                hgraph, oneNext, twoNext, fresh]
              using congrArg
                (fun controls : OneControl A strategy hwin policy ×
                    TwoControl A strategy hwin policy ↦
                  profiledRawJointHybridPhysicalCompatiblePhaseLiveClose A
                    strategy hwin policy initialOne initialTwo fallbackLeft
                      fallbackRight controls.1 (env n).inputOne controls.2
                        (env n).inputTwo)
                hpair
          refine ⟨oneNext, twoNext, congrArg Prod.fst hnext.symm,
            congrArg Prod.snd hnext.symm, hinvariantNext, hsegmentNext, ?_⟩
          exact Prod.eta _

end

end DetParityAutomaton

end DistributedSynthesis
