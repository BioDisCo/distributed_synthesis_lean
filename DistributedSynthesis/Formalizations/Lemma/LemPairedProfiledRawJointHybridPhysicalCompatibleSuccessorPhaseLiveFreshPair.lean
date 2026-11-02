/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveRightOverlay
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveLeftOverlay

/-!
# Paired fresh controls for the compatible-successor phase-live overlay

One local computation advances both potentially live receivers.  Its open
continuations retain the advanced old receivers.  Its closed continuations
retain receivers initialized from the opposite freshly prepared pending
datum.  Thus a one-way continuation preserves the old table, while a
simultaneous close starts both new tables at the same boundary.

All data is finite.  The computation receives only the two endpoint controls
and the current input pair; it receives no graph, orientation, leader, or
strict-leader information.
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

private abbrev OneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy hwin
    policy

private abbrev TwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy hwin
    policy

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

/-! ## Total finite row projections -/

def profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (receiver : RightReceiver A strategy hwin (initial := initial)) :
    PairedEntryRow :=
  match receiver.2 with
  | none => .first
  | some state => state.2.1

def profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (receiver : LeftReceiver A strategy hwin (initial := initial)) :
    PairedEntryRow :=
  match receiver.2 with
  | none => .first
  | some state => state.2.1

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (RightOutput A strategy hwin initial)) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
        strategy hwin ⟨state, some ⟨move, row, monitorState, staged⟩⟩ = row :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (LeftOutput A strategy hwin initial)) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A strategy
        hwin ⟨state, some ⟨move, row, monitorState, staged⟩⟩ = row :=
  rfl

/-! ## Fresh dormant owners and closed receivers -/

/-- The fresh right owner named by a left-output pending payload.  The parent
shared argument is type-carrying only; installation reads the payload target. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (parent : RightOwner A strategy hwin policy)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy
        hwin (initial := initial)) :
    RightOwner A strategy hwin policy :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
      x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
        (false, parent, payload)
  ⟨installed.1.1, installed.1.2.2⟩

/-- Fresh left-owner mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (parent : LeftOwner A strategy hwin policy)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy
        hwin (initial := initial)) :
    LeftOwner A strategy hwin policy :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
      x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
        (false, parent, payload)
  ⟨installed.1.1, installed.1.2.2⟩

/-- The closed interpretation of process one's receiver is initialized from
the fresh process-two base pending datum at member `true`. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedLeftReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (owner : LeftOwner A strategy hwin policy)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy
        hwin (initial := initial)) :
    LeftReceiver A strategy hwin (initial := initial) :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
      x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
        (true, owner, payload)
  ⟨installed.1.1, installed.2⟩

/-- Process-two closed-receiver mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedRightReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (owner : RightOwner A strategy hwin policy)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy
        hwin (initial := initial)) :
    RightReceiver A strategy hwin (initial := initial) :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
      x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
        (true, owner, payload)
  ⟨installed.1.1, installed.2⟩

/-! ## Exact fresh-root alignment -/

/-- A left-table output selects one exact right-live successor.  Its fresh
right owner and either acknowledged receiver row are therefore initialized at
the same reachable compatible-policy key. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_aligned_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (hstate : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
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
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
        hwin policy owner ⟨installed.1.1, installed.2⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin
        initial policy owner.1 := by
  dsimp only
  rcases htarget.transition with ⟨transition⟩
  obtain ⟨move, hmove⟩ := transition.right_move A strategy hwin
  have hreachable := transition.reachable A strategy hwin hstate
  constructor
  · cases receiverMember with
    | false =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner,
          profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRight_initial_aligned
            A strategy hwin policy
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
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRight_initial_aligned
            A strategy hwin policy
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove .both)
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner,
        profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember,
        profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
        profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget]
      using hreachable

/-- Right-table/left-live mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_aligned_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (hstate : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
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
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner A
        strategy hwin policy parent payload
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
          (receiverMember, owner, payload)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
        hwin policy owner ⟨installed.1.1, installed.2⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin
        initial policy owner.1 := by
  dsimp only
  rcases htarget.transition with ⟨transition⟩
  obtain ⟨move, hmove⟩ := transition.left_move A strategy hwin
  have hreachable := transition.reachable A strategy hwin hstate
  constructor
  · cases receiverMember with
    | false =>
      simpa
        [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner,
          profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget,
          profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver,
          profiledRawJointHybridPhysicalCompatiblePendingRow]
        using
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeft_initial_aligned
            A strategy hwin policy
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
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeft_initial_aligned
            A strategy hwin policy
              (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin (output.target entryRow).1)
              move hmove .both)
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner,
        profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember,
        profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
        profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget]
      using hreachable

/-! ## One paired receive computation -/

/-- Both unresolved endpoint forks and their physical output pair. -/
abbrev ProfiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPairResult
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  (FiniteDelayedFork (OnePending A strategy hwin policy) ×
      FiniteDelayedFork (TwoPending A strategy hwin policy)) ×
    (Out₁ × Out₂)

/-- Compute the two table records once, prepare the next dormant owners from
those records, and cache the advanced/open and initialized/closed receivers. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPairResult A strategy
      hwin policy :=
  let leftReceiver :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne A
      strategy hwin policy one two
  let rightReceiver :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo A
      strategy hwin policy two one
  let leftResult :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A strategy
      hwin policy fallbackLeft two.2.1.baseShared leftReceiver input
  let rightResult :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
      strategy hwin policy fallbackRight one.2.1.baseShared rightReceiver
        (input.2, input.1)
  let leftRow :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A strategy
      hwin leftReceiver
  let rightRow :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
      strategy hwin rightReceiver
  let onePayload :=
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
      strategy hwin leftResult.1 leftRow
  let twoPayload :=
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
      strategy hwin rightResult.1 rightRow
  let rightOwner :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner A strategy
      hwin policy one.2.1.baseShared onePayload
  let leftOwner :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner A strategy
      hwin policy two.2.1.baseShared twoPayload
  let closedLeft :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedLeftReceiver A
      strategy hwin policy leftOwner twoPayload
  let closedRight :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedRightReceiver A
      strategy hwin policy rightOwner onePayload
  let oneShared : OneShared A strategy hwin policy :=
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh rightOwner onePayload
      true leftResult.2 closedLeft
  let twoShared : TwoShared A strategy hwin policy :=
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh leftOwner twoPayload
      false rightResult.2 closedRight
  ((⟨(false, oneShared, PUnit.unit), (true, oneShared, PUnit.unit)⟩,
    ⟨(false, twoShared, PUnit.unit), (true, twoShared, PUnit.unit)⟩),
   (profiledRawJointHybridPhysicalCompatibleLeftInformedOutputAtRow A strategy
      hwin leftRow leftResult.1,
    profiledRawJointHybridPhysicalCompatibleRightInformedOutputAtRow A strategy
      hwin rightRow rightResult.1))

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_phase
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (input : In₁ × In₂) (member : Bool) :
    (((profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair A strategy
      hwin policy fallbackLeft fallbackRight one two input).1.1.candidate
        member).2.1.localPhase) = true := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_phase
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (input : In₁ × In₂) (member : Bool) :
    (((profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair A strategy
      hwin policy fallbackLeft fallbackRight one two input).1.2.candidate
        member).2.1.localPhase) = false := by
  cases member <;> rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_open_receiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (input : In₁ × In₂) :
    ((profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair A strategy hwin
        policy fallbackLeft fallbackRight one two input).1.1.openControl.2.1
          ).receiver false =
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
        hwin policy fallbackLeft one two input).2 :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_open_receiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (input : In₁ × In₂) :
    ((profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair A strategy hwin
        policy fallbackLeft fallbackRight one two input).1.2.openControl.2.1
          ).receiver false =
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A strategy
        hwin policy fallbackRight two one (input.2, input.1)).2 :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
