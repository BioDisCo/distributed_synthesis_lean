/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveTracked
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveController

/-!
# The relational two-key invariant of the successor phase controller

The two endpoints do not know which process is the strict leader.  Accordingly
the invariant does not designate one executable leader key.  It retains two
same-policy candidates: the currently live crossed table and the dormant
table that is ready for a local phase switch.  The endpoint-local phase pair
determines only which already-carried relation is used in the proof.
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

/-! ## The four relations carried by a pending pair -/

/-- The right table used when process two repeats its receiving phase. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy hwin
    policy one.2.1.baseShared (two.2.1.receiver two.1)

/-- The left table used when process one repeats its receiving phase. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy hwin
    policy two.2.1.baseShared (one.2.1.receiver one.1)

/-- Dormant right table selected locally after process two observes a phase
switch. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy hwin
    policy one.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver A
        strategy hwin policy one)

/-- Dormant left-table mirror. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (two : TwoPending A strategy hwin policy) : Prop :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy hwin
    policy two.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver A
        strategy hwin policy two)

/-! ## Phase-indexed relational invariant -/

/-- The smallest table invariant closed by all three physical round kinds.

* `false,false`: right is live; the left switch table is ready;
* `true,true`: left is live; the right switch table is ready;
* `true,false`: both crossed tables are live after a simultaneous close;
* `false,true`: unreachable.

The phase bits are local history written by the two endpoint transitions, not
an oracle revealing the current graph or strict leader. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) : Prop :=
  match one.2.1.localPhase, two.2.1.localPhase with
  | false, false =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked A
          strategy hwin policy one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchTracked A
          strategy hwin policy two
  | true, true =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked A
          strategy hwin policy one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchTracked A
          strategy hwin policy one
  | true, false =>
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked A
          strategy hwin policy one two ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked A
          strategy hwin policy one two
  | false, true => False

/-- The phase invariant always supplies the exact right pair selected by
process two's local receive dispatcher. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.right_selected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
      hwin policy one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
          A strategy hwin policy two one) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked]
      at hinvariant
    exact hinvariant.1
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo] at hinvariant
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked]
      at hinvariant
    exact hinvariant.1
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_switch
      A strategy hwin policy two one htwo]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchTracked]
      at hinvariant
    exact hinvariant.2

/-- Left selected-pair mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.left_selected
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy hwin
      policy two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
          A strategy hwin policy one two) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_switch
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchTracked]
      at hinvariant
    exact hinvariant.2
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo] at hinvariant
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked]
      at hinvariant
    exact hinvariant.2
  · rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hone]
    simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo,
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked]
      at hinvariant
    exact hinvariant.1

/-! ## Selected local receive steps preserve the tracked relation -/

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight_same_tracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy)
    (hphase : two.2.1.localPhase = false)
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked A
        strategy hwin policy one two)
    (input : In₂ × In₁) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
        strategy hwin policy one.1 one.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A strategy
        hwin policy fallback two one input).2 := by
  unfold ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked at tracked
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one hphase]
  exact tracked.step A strategy hwin fallback one.1 input

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight_switch_tracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy)
    (hphase : two.2.1.localPhase = true)
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchTracked A
        strategy hwin policy one)
    (input : In₂ × In₁) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
        strategy hwin policy one.1 one.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A strategy
        hwin policy fallback two one input).2 := by
  unfold ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchTracked at tracked
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_switch
      A strategy hwin policy two one hphase]
  exact tracked.step A strategy hwin fallback one.1 input

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft_same_tracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hphase : one.2.1.localPhase = true)
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked A
        strategy hwin policy one two)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy hwin
      policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
        strategy hwin policy two.1 two.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
        hwin policy fallback one two input).2 := by
  unfold ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked at tracked
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hphase]
  exact tracked.step A strategy hwin fallback two.1 input

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft_switch_tracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hphase : one.2.1.localPhase = false)
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchTracked A
        strategy hwin policy two)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy hwin
      policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
        strategy hwin policy two.1 two.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
        hwin policy fallback one two input).2 := by
  unfold ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchTracked at tracked
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_switch
      A strategy hwin policy one two hphase]
  exact tracked.step A strategy hwin fallback two.1 input

/-! ## Fresh open and closed continuations -/

/-- A strict-right computation installs a fresh dormant left table in process
two's open continuation. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_open_leftSwitchTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (fallbackRight :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (input : In₁ × In₂) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchTracked A
      strategy hwin policy fresh.1.2.openControl := by
  dsimp only
  let selected := hinvariant.right_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_targetAt A strategy hwin fallbackRight (input.2, input.1)
      false
  have hfresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_tracked_of_targetAt
      A strategy hwin policy one.2.1.baseShared.1 selected.reachable
        two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A
          strategy hwin policy fallbackRight two one (input.2, input.1)).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one))
        false (.inr slot) htarget
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchTracked,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoBasePending,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.basePending]
    using hfresh

/-- Strict-left mirror: process one's open continuation carries a fresh
dormant right table. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_open_rightSwitchTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (fallbackRight :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (input : In₁ × In₂) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchTracked A
      strategy hwin policy fresh.1.1.openControl := by
  dsimp only
  let selected := hinvariant.left_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_targetAt A strategy hwin fallbackLeft input false
  have hfresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_tracked_of_targetAt
      A strategy hwin policy two.2.1.baseShared.1 selected.reachable
        one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
          hwin policy fallbackLeft one two input).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two))
        false (.inl slot) htarget
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchTracked,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveOneBasePending,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.basePending]
    using hfresh

/-! ## The three physical round cases -/

/-- A strict-right round preserves the full relational table invariant.  The
right receiver is selected only from process two's stored phase; the fresh
left table is retained for a possible later switch. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.strictRight
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (fallbackLeft :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (fallbackRight :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (input : In₁ × In₂) :
    let oneNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A
          strategy hwin policy) one input.1).1
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight one two input
    let twoNext := fresh.1.2.openControl
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A strategy
      hwin policy oneNext twoNext := by
  dsimp only
  let selected := hinvariant.right_selected A strategy hwin
  have hright :=
    selected.step A strategy hwin fallbackRight one.1 (input.2, input.1)
  have hleft :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_two_open_leftSwitchTracked
      A strategy hwin policy fallbackLeft fallbackRight one two hinvariant input
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant,
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked,
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
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.strictLeft
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (fallbackLeft :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (fallbackRight :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (input : In₁ × In₂) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight one two input
    let oneNext := fresh.1.1.openControl
    let twoNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A
          strategy hwin policy) two input.2).1
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A strategy
      hwin policy oneNext twoNext := by
  dsimp only
  let selected := hinvariant.left_selected A strategy hwin
  have hleft := selected.step A strategy hwin fallbackLeft two.1 input
  have hright :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_one_open_rightSwitchTracked
      A strategy hwin policy fallbackLeft fallbackRight one two hinvariant input
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant,
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
    using And.intro hleft hright

/-- The closed continuations of one paired receive carry both freshly selected
crossed tables. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_closed_bothTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallbackLeft :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (fallbackRight :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (input : In₁ × In₂) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked A
        strategy hwin policy fresh.1.1.closedControl fresh.1.2.closedControl ∧
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked A
        strategy hwin policy fresh.1.1.closedControl
          fresh.1.2.closedControl := by
  dsimp only
  let rightSelected := hinvariant.right_selected A strategy hwin
  let leftSelected := hinvariant.left_selected A strategy hwin
  obtain ⟨rightSlot, rightTarget⟩ :=
    rightSelected.exists_targetAt A strategy hwin fallbackRight
      (input.2, input.1) true
  obtain ⟨leftSlot, leftTarget⟩ :=
    leftSelected.exists_targetAt A strategy hwin fallbackLeft input true
  have hright :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_tracked_of_targetAt
      A strategy hwin policy two.2.1.baseShared.1 leftSelected.reachable
        one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
          hwin policy fallbackLeft one two input).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two))
        true (.inl leftSlot) leftTarget
  have hleft :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_tracked_of_targetAt
      A strategy hwin policy one.2.1.baseShared.1 rightSelected.reachable
        two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A
          strategy hwin policy fallbackRight two one (input.2, input.1)).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one))
        true (.inr rightSlot) rightTarget
  constructor
  · simpa
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedRightReceiver,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
      using hright
  · simpa
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshClosedLeftReceiver,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
      using hleft

/-- A simultaneous round closes both fresh candidates and preserves the full
relational invariant in phase `true,false`. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.both
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (fallbackLeft :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (fallbackRight :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (input : In₁ × In₂) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s, max u v x y s} A
        strategy hwin policy fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A strategy
      hwin policy fresh.1.1.closedControl fresh.1.2.closedControl := by
  dsimp only
  have hboth :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair_closed_bothTracked
      A strategy hwin policy fallbackLeft fallbackRight one two hinvariant input
  simpa
    [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair]
    using hboth

/-- Every admissible phase carries at least one live table. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.exists_current
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightCurrentTracked A
        strategy hwin policy one two ∨
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftCurrentTracked A
        strategy hwin policy one two := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo] at hinvariant
    exact Or.inl hinvariant.1
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo] at hinvariant
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo] at hinvariant
    exact Or.inl hinvariant.1
  · simp only
      [ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant, hone,
        htwo] at hinvariant
    exact Or.inr hinvariant.1

end


end DetParityAutomaton

end DistributedSynthesis
