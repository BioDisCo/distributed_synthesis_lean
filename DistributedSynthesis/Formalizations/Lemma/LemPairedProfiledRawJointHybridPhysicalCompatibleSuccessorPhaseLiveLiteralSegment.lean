/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveTraceSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLiteralPrefixReachability

/-!
# Exact literal segments carried by the compatible successor phase overlay

The relational phase-live invariant remembers that a selected owner and
receiver are folds of some common prefix.  Physical cut bookkeeping needs the
stronger statement that this prefix is exactly the consecutive input segment
since the table was installed.  This file introduces that proof-side segment
invariant and proves its two local operations: fresh installation starts an
empty epoch, and a matched receive appends the actual physical input.

No start time, prefix, graph orientation, side, or leader flag is added to an
executable controller state.
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

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev RightOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A strategy hwin
    policy

private abbrev LeftOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A strategy hwin
    policy

private abbrev RightReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
    hwin (initial := initial)

private abbrev LeftReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy hwin
    (initial := initial)

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

/-! ## Exact table epochs -/

/-- A live right table at global time `n` is the pair of literal folds of the
consecutive swapped-input segment `[start,n)`. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (owner : RightOwner A strategy hwin policy)
    (receiver : RightReceiver A strategy hwin (initial := initial)) : Prop :=
  ∃ (start : Nat) (past : List (In₂ × In₁))
      (state : CompatibleState A strategy hwin initial)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false).State)
      (staged : Option (RightOutput A strategy hwin initial)),
    start + past.length = n ∧
      (∀ (j : Nat) (hj : j < past.length),
        past[j] = ((env (start + j)).inputTwo,
          (env (start + j)).inputOne)) ∧
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A
        strategy hwin policy state move ownerControl monitorState past

/-- Left-table mirror, using the physical input order. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (owner : LeftOwner A strategy hwin policy)
    (receiver : LeftReceiver A strategy hwin (initial := initial)) : Prop :=
  ∃ (start : Nat) (past : List (In₁ × In₂))
      (state : CompatibleState A strategy hwin initial)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
          strategy hwin (initial := initial) move false).State)
      (staged : Option (LeftOutput A strategy hwin initial)),
    start + past.length = n ∧
      (∀ (j : Nat) (hj : j < past.length),
        past[j] = ((env (start + j)).inputOne,
          (env (start + j)).inputTwo)) ∧
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
        hwin policy state move ownerControl monitorState past

/-! ## Fresh installation -/

/-- A freshly installed right table represents the empty segment beginning at
the current global time. -/
theorem profiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt A
      strategy hwin policy env n
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerInitial A
          strategy hwin policy state)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverInitial
          A strategy hwin state row) := by
  refine ⟨n, [], state, move,
    (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move false).initial, row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move false).initial,
    none, by simp, ?_, ?_, ?_,
    profiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt_initial A
      strategy hwin policy state move⟩
  · intro j hj
    simp at hj
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerInitial,
      profiledRawJointHybridPhysicalCompatibleRightSharedInitial, hmove]
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverInitial,
        profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]

/-- Fresh left-table mirror. -/
theorem profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt A
      strategy hwin policy env n
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerInitial A
          strategy hwin policy state)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverInitial A
          strategy hwin state row) := by
  refine ⟨n, [], state, move,
    (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move false).initial, row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := initial) move false).initial,
    none, by simp, ?_, ?_, ?_,
    profiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt_initial A
      strategy hwin policy state move⟩
  · intro j hj
    simp at hj
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerInitial,
      profiledRawJointHybridPhysicalCompatibleLeftSharedInitial, hmove]
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverInitial,
        profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]

/-! ## One exact local extension -/

/-- A matched right receive appends the actual swapped physical input to the
same table epoch. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {owner : RightOwner A strategy hwin policy}
    {receiver : RightReceiver A strategy hwin (initial := initial)}
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt A
        strategy hwin policy env n owner receiver)
    (fallback : RightOutput A strategy hwin initial)
    (member : Bool) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt A
      strategy hwin policy env (n + 1)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
          strategy hwin policy member owner (env n).inputOne).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
          strategy hwin policy fallback owner receiver
            ((env n).inputTwo, (env n).inputOne)).2 := by
  rcases segment with
    ⟨start, past, state, move, ownerControl, row, monitorState, staged,
      hend, hinputs, howner, hreceiver, hreachable⟩
  subst owner
  subst receiver
  let input : In₂ × In₁ := ((env n).inputTwo, (env n).inputOne)
  let result :=
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
      hwin policy state move ownerControl row monitorState input
  refine ⟨start, past ++ [input], state, move,
    (move.memberController A false).step ownerControl input.2, row,
    result.2.2.2.1, some result.1, ?_, ?_, ?_, ?_,
    hreachable.step A strategy hwin row input⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro j hj
    by_cases hjOld : j < past.length
    · simpa [List.getElem_append, hjOld] using hinputs j hjOld
    · have hjEq : j = past.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      simp [hend, input]
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep,
      profiledRawJointHybridPhysicalCompatibleRightSharedStep]
    exact
      (profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).state_eq
        member false ownerControl input.2
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep,
      profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor, result,
      input]

/-- Left-table extension mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {owner : LeftOwner A strategy hwin policy}
    {receiver : LeftReceiver A strategy hwin (initial := initial)}
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt A
        strategy hwin policy env n owner receiver)
    (fallback : LeftOutput A strategy hwin initial)
    (member : Bool) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt A
      strategy hwin policy env (n + 1)
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
          strategy hwin policy member owner (env n).inputTwo).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A
          strategy hwin policy fallback owner receiver
            ((env n).inputOne, (env n).inputTwo)).2 := by
  rcases segment with
    ⟨start, past, state, move, ownerControl, row, monitorState, staged,
      hend, hinputs, howner, hreceiver, hreachable⟩
  subst owner
  subst receiver
  let input : In₁ × In₂ := ((env n).inputOne, (env n).inputTwo)
  let result :=
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy hwin
      policy state move ownerControl row monitorState input
  refine ⟨start, past ++ [input], state, move,
    (move.memberController A false).step ownerControl input.2, row,
    result.2.2.2.1, some result.1, ?_, ?_, ?_, ?_,
    hreachable.step A strategy hwin row input⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro j hj
    by_cases hjOld : j < past.length
    · simpa [List.getElem_append, hjOld] using hinputs j hjOld
    · have hjEq : j = past.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      simp [hend, input]
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep,
      profiledRawJointHybridPhysicalCompatibleLeftSharedStep]
    exact
      (profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).state_eq
        member false ownerControl input.2
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep,
      profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor, result,
      input]

/-! ## Fresh crossed successors start empty epochs -/

/-- An exact left-table target transition installs a fresh right-table epoch
for either acknowledged receiver row. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_literalSegment_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (state : CompatibleState A strategy hwin initial)
    (parent : RightOwner A strategy hwin policy)
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
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt A
      strategy hwin policy env n owner ⟨installed.1.1, installed.2⟩ := by
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
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt_initial
            A strategy hwin policy env n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove .first)
  | true =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner,
          profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt_initial
            A strategy hwin policy env n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove .both)

/-- Right-table target transition installs a fresh left-table epoch. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_literalSegment_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (state : CompatibleState A strategy hwin initial)
    (parent : LeftOwner A strategy hwin policy)
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
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner A strategy
        hwin policy parent payload
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
          (receiverMember, owner, payload)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt A
      strategy hwin policy env n owner ⟨installed.1.1, installed.2⟩ := by
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
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt_initial
            A strategy hwin policy env n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove .first)
  | true =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner,
          profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt_initial
            A strategy hwin policy env n
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove .both)

/-! ## Phase-selected exact epochs -/

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt A
    strategy hwin policy env n one.2.1.baseShared
      (two.2.1.receiver two.1)

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt A
    strategy hwin policy env n two.2.1.baseShared
      (one.2.1.receiver one.1)

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchLiteralSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt A
    strategy hwin policy env n one.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver A
        strategy hwin policy one)

def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchLiteralSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt A
    strategy hwin policy env n two.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver A
        strategy hwin policy two)

/-- Phase-indexed exact table epochs, in the same four cases as the existing
relational phase-live invariant. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  match one.2.1.localPhase, two.2.1.localPhase with
  | false, false =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt
          A strategy hwin policy env n one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchLiteralSegmentAt
          A strategy hwin policy env n two
  | true, true =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt
          A strategy hwin policy env n one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchLiteralSegmentAt
          A strategy hwin policy env n one
  | true, false =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt
          A strategy hwin policy env n one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt
          A strategy hwin policy env n one two
  | false, true => False

/-- Exact epoch selected by process two's local right receive dispatcher. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt.right_selected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
        A strategy hwin policy env n one two) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightLiteralSegmentAt A
      strategy hwin policy env n one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
          A strategy hwin policy two one) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt]
      at hsegment
    exact hsegment.1
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo] at hsegment
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt]
      at hsegment
    exact hsegment.1
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_switch
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchLiteralSegmentAt]
      at hsegment
    exact hsegment.2

/-- Left selected-epoch mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt.left_selected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
        A strategy hwin policy env n one two) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftLiteralSegmentAt A
      strategy hwin policy env n two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
          A strategy hwin policy one two) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_switch
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchLiteralSegmentAt]
      at hsegment
    exact hsegment.2
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo] at hsegment
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt]
      at hsegment
    exact hsegment.2
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
        hone, htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt]
      at hsegment
    exact hsegment.1

/-! ## Fresh epoch transport -/

/-- A strict-right receive prepares the opposite left switch table as a fresh
empty epoch at the following global time. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_open_leftSwitchLiteralSegment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchLiteralSegmentAt
      A strategy hwin policy env (n + 1) fresh.1.2.openControl := by
  dsimp only
  let selected := hinvariant.right_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_targetAt A strategy hwin fallbackRight
      ((env n).inputTwo, (env n).inputOne) false
  have hfresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_literalSegment_of_targetAt
      A strategy hwin policy env (n + 1) one.2.1.baseShared.1
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
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchLiteralSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoBasePending,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.basePending]
    using hfresh

/-- Strict-left mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_open_rightSwitchLiteralSegment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchLiteralSegmentAt
      A strategy hwin policy env (n + 1) fresh.1.1.openControl := by
  dsimp only
  let selected := hinvariant.left_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_targetAt A strategy hwin fallbackLeft
      ((env n).inputOne, (env n).inputTwo) false
  have hfresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_literalSegment_of_targetAt
      A strategy hwin policy env (n + 1) two.2.1.baseShared.1
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
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchLiteralSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveOneBasePending,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.basePending]
    using hfresh

/-- A simultaneous close initializes both current table epochs after the
round. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_closed_bothLiteralSegments
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt
        A strategy hwin policy env (n + 1) fresh.1.1.closedControl
          fresh.1.2.closedControl ∧
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt
        A strategy hwin policy env (n + 1) fresh.1.1.closedControl
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
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_literalSegment_of_targetAt
      A strategy hwin policy env (n + 1) two.2.1.baseShared.1
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
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_literalSegment_of_targetAt
      A strategy hwin policy env (n + 1) one.2.1.baseShared.1
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
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedRightReceiver,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
      using hright
  · simpa
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedLeftReceiver,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
      using hleft

/-! ## Preservation by physical graph kind -/

/-- A strict-right round extends the selected right epoch and installs a fresh
dormant left epoch. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt.strictRight
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
        A strategy hwin policy env n one two)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :
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
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
      A strategy hwin policy env (n + 1) oneNext twoNext := by
  dsimp only
  let selected := hsegment.right_selected A strategy hwin
  have hright := selected.step A strategy hwin fallbackRight one.1
  have hleft :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_open_leftSwitchLiteralSegment
      A strategy hwin policy fallbackLeft fallbackRight env n one two hinvariant
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentLiteralSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep]
    using And.intro hright hleft

/-- Strict-left mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt.strictLeft
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
        A strategy hwin policy env n one two)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :
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
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
      A strategy hwin policy env (n + 1) oneNext twoNext := by
  dsimp only
  let selected := hsegment.left_selected A strategy hwin
  have hleft := selected.step A strategy hwin fallbackLeft two.1
  have hright :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_open_rightSwitchLiteralSegment
      A strategy hwin policy fallbackLeft fallbackRight env n one two hinvariant
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentLiteralSegmentAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
    using And.intro hleft hright

/-- A simultaneous round resets both exact epochs after the closing record. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt.both
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (_hsegment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
        A strategy hwin policy env n one two)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          ((env n).inputOne, (env n).inputTwo)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
      A strategy hwin policy env (n + 1) fresh.1.1.closedControl
        fresh.1.2.closedControl := by
  dsimp only
  have hboth :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_closed_bothLiteralSegments
      A strategy hwin policy fallbackLeft fallbackRight env n one two hinvariant
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair]
    using hboth

/-! ## Canonical trace induction -/

/-- Pending semantic controls at time `n`, carrying both the established
structural invariant and the exact literal epoch invariant. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalLiteralSegmentSelected
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
          ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
              A strategy hwin policy env n onePending twoPending ∧
            (one, two) =
              profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
                strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight env n

/-- From one exact initial epoch package, every state of the canonical
phase-live semantic trace carries the exact consecutive physical input epoch.
This is the all-time induction needed before specializing to scheduled cuts. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace_literalSegments
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
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLiteralSegmentInvariantAt
        A strategy hwin policy env 0 initialOne initialTwo) : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveCanonicalLiteralSegmentSelected
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
          have hsegmentNext := hsegment.strictRight A strategy hwin hinvariant
            fallbackLeft fallbackRight
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
          have hsegmentNext := hsegment.strictLeft A strategy hwin hinvariant
            fallbackLeft fallbackRight
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
          have hsegmentNext := hsegment.both A strategy hwin hinvariant
            fallbackLeft fallbackRight
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
                  (profiledRawJointHybridPhysicalCompatiblePhaseLiveClose A
                    strategy hwin policy initialOne initialTwo fallbackLeft
                      fallbackRight controls.1 (env n).inputOne controls.2
                        (env n).inputTwo))
                hpair
          refine ⟨oneNext, twoNext, congrArg Prod.fst hnext.symm,
            congrArg Prod.snd hnext.symm, hinvariantNext, hsegmentNext, ?_⟩
          exact Prod.eta _

end

end DetParityAutomaton

end DistributedSynthesis
