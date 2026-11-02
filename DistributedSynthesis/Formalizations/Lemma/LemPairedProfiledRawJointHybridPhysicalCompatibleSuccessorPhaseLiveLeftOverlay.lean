/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveOverlayTypes

/-!
# The retained left-table receiver of the compatible successor overlay

Process one is the informed endpoint of a strict-left round.  On a repeated
strict-left round it pairs its retained left receiver with process two's
delivered, already advanced left owner.  On a switch it instead resolves the
delivered base pending control and starts both halves at the selected child.

The dispatch reads only process one's local phase bit.  It does not inspect a
graph, orientation, hierarchy side, leader, or strict-leader flag.
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

private abbrev LeftOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A strategy hwin
    policy

private abbrev LeftReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
    hwin (initial := initial)

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

private abbrev TwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending A strategy hwin
    policy

private abbrev OnePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending A strategy hwin
    policy

/-! ## Matched owner/receiver prefixes -/

/-- The delivered left owner and process one's retained receiver are the two
folds of one common finite prefix.  The prefix itself lives only in the final
proof field and is not finite controller data. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (owner : LeftOwner A strategy hwin policy)
    (receiver : LeftReceiver A strategy hwin (initial := initial)) : Prop :=
  ∃ (state : CompatibleState A strategy hwin initial)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
          strategy hwin (initial := initial) move false).State)
      (staged : Option (LeftOutput A strategy hwin initial)),
    owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
          hwin policy state move ownerControl monitorState ∧
        state.1.2.2 = some move

/-! ## Initial and total local left steps -/

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerInitial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    LeftOwner A strategy hwin policy :=
  ⟨state,
    profiledRawJointHybridPhysicalCompatibleLeftSharedInitial A strategy hwin
      policy state⟩

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverInitial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial) (row : PairedEntryRow) :
    LeftReceiver A strategy hwin (initial := initial) :=
  ⟨state,
    profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
      state row⟩

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeft_initial_aligned
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerInitial A
        strategy hwin policy state)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverInitial A
        strategy hwin state row) := by
  refine ⟨state, move,
    (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move false).initial,
    row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := initial) move false).initial,
    none, ?_, ?_, ?_, hmove⟩
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerInitial,
      profiledRawJointHybridPhysicalCompatibleLeftSharedInitial, hmove]
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverInitial,
        profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]
  · exact
      profiledRawJointHybridPhysicalCompatibleLeftLocallyReachable_initial A
        strategy hwin policy state move

/-- Advance a delivered left owner.  The old member is accepted as an
argument because the actual carrier supplies it; the compatible tables are
member coherent. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) (member : Bool)
    (owner : LeftOwner A strategy hwin policy) (input : In₂) :
    LeftOwner A strategy hwin policy × Out₂ :=
  let next :=
    profiledRawJointHybridPhysicalCompatibleLeftSharedStep A strategy hwin
      policy owner.1 member owner.2 input
  (⟨owner.1, next.1⟩, next.2)

/-- Totalized left receiver step.  Every mismatch branch retains the old
receiver and emits the supplied fallback.  The alignment invariant proves
that no such branch is taken on the semantic trace. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : LeftOutput A strategy hwin initial)
    (owner : LeftOwner A strategy hwin policy)
    (receiver : LeftReceiver A strategy hwin (initial := initial))
    (input : In₁ × In₂) :
    LeftOutput A strategy hwin initial ×
      LeftReceiver A strategy hwin (initial := initial) := by
  classical
  rcases owner with ⟨state, ownerShared⟩
  rcases receiver with ⟨receiverState, receiverPayload⟩
  by_cases hstate : receiverState = state
  · subst receiverState
    cases ownerShared with
    | inl _ => exact (fallback, ⟨state, receiverPayload⟩)
    | inr installed =>
        rcases installed with ⟨ownerMove, ownerControl⟩
        cases receiverPayload with
        | none => exact (fallback, ⟨state, none⟩)
        | some receiverState =>
            rcases receiverState with
              ⟨receiverMove, row, monitorState, staged⟩
            by_cases hmove : receiverMove = ownerMove
            · subst receiverMove
              let next :=
                profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A
                  strategy hwin policy state ownerMove ownerControl row
                    monitorState input
              exact (next.1, ⟨state, some next.2⟩)
            · exact
                (fallback,
                  ⟨state,
                    some ⟨receiverMove, row, monitorState, staged⟩⟩)
  · exact (fallback, ⟨receiverState, receiverPayload⟩)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : LeftOutput A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (LeftOutput A strategy hwin initial))
    (input : In₁ × In₂) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A
        strategy hwin policy fallback
          ⟨state, .inr ⟨move, ownerControl⟩⟩
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ input =
      let next :=
        profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
          hwin policy state move ownerControl row monitorState input
      (next.1, ⟨state, some next.2⟩) := by
  simp
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep]

/-! ## The dangerous repeated-round preservation law -/

/-- The compatible successor phase-live overlay passes the pair test: one
strict-left round advances the delivered owner and retained receiver through
the same input, preserving their common-prefix invariant. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeft_step_preserves
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : LeftOutput A strategy hwin initial)
    (owner : LeftOwner A strategy hwin policy)
    (receiver : LeftReceiver A strategy hwin (initial := initial))
    (haligned :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
        hwin policy owner receiver)
    (member : Bool) (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
        strategy hwin policy member owner input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A
        strategy hwin policy fallback owner receiver input).2 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl, hreach,
      hmove⟩
  refine ⟨state, move,
    (move.memberController A false).step ownerControl input.2,
    row,
    (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
      hwin policy state move ownerControl row monitorState input).2.2.2.1,
    some
      (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move ownerControl row monitorState input).1,
    ?_, ?_, ?_, hmove⟩
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep,
        profiledRawJointHybridPhysicalCompatibleLeftSharedStep]
    exact
      (profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).state_eq
        member false ownerControl input.2
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep,
        profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor]
  · exact hreach.step A strategy hwin row input

/-! ## Phase-selected repeated and switch receivers -/

/-- Resolve process two's underlying old pending datum and retain only the
newly initialized left receiver.  The delivered `baseShared` is the dormant
left owner which will actually take the simultaneous blind step. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (two : TwoPending A strategy hwin policy) :
    LeftReceiver A strategy hwin (initial := initial) :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
      x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoBasePending A
        strategy hwin two)
  ⟨installed.1.1, installed.2⟩

/-- Process one selects its retained receiver on a repeated left round
(`true`), and the freshly installed receiver after a local role switch
(`false`). -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy) :
    LeftReceiver A strategy hwin (initial := initial) :=
  if one.2.1.localPhase then
    one.2.1.receiver one.1
  else
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver A
      strategy hwin policy two

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hphase : one.2.1.localPhase = true) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne A
        strategy hwin policy one two =
      one.2.1.receiver one.1 := by
  simp
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne,
      hphase]

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_switch
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hphase : one.2.1.localPhase = false) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne A
        strategy hwin policy one two =
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver A
        strategy hwin policy two := by
  simp
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne,
      hphase]

/-- Advance process one's locally selected left receiver.  This is already
the physical local receive calculation; later fresh constructors only decide
which advanced/fresh receiver is cached in each unresolved continuation. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : LeftOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (input : In₁ × In₂) :
    LeftOutput A strategy hwin initial ×
      LeftReceiver A strategy hwin (initial := initial) :=
  profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A strategy
    hwin policy fallback two.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
        A strategy hwin policy one two)
      input

/-- A repeated strict-left round uses the retained receiver and passes the
matched-prefix pair test. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft_same_preserves
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : LeftOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hphase : one.2.1.localPhase = true)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
        hwin policy two.2.1.baseShared (one.2.1.receiver one.1))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
        strategy hwin policy two.1 two.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
        hwin policy fallback one two input).2 := by
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_same
      A strategy hwin policy one two hphase]
  exact
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeft_step_preserves A
      strategy hwin policy fallback two.2.1.baseShared
        (one.2.1.receiver one.1) haligned two.1 input

/-- At a local role switch, the receiver installed from process two's base
pending datum is advanced once with the dormant delivered owner.  The sole
premise is their root alignment, which the paired fresh constructor will
establish when it creates that dormant datum. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft_switch_preserves
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : LeftOutput A strategy hwin initial)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hphase : one.2.1.localPhase = false)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
        hwin policy two.2.1.baseShared
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver
            A strategy hwin policy two))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
        strategy hwin policy two.1 two.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
        hwin policy fallback one two input).2 := by
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne_switch
      A strategy hwin policy one two hphase]
  exact
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeft_step_preserves A
      strategy hwin policy fallback two.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftSwitchReceiver A
          strategy hwin policy two)
        haligned two.1 input

end

end DetParityAutomaton

end DistributedSynthesis
