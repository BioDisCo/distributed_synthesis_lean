/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveOverlayTypes

/-!
# The retained right-table receiver of the compatible successor overlay

Process two is the informed endpoint of a strict-right round.  On a repeated
strict-right round it pairs its retained right receiver with process one's
delivered, already advanced right owner.  On a switch it instead resolves the
delivered base pending control and starts both halves at the selected child.

The dispatch reads only process two's local phase bit.  It does not inspect a
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

private abbrev RightOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A strategy hwin
    policy

private abbrev RightReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
    hwin (initial := initial)

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
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

/-! ## Matched owner/receiver prefixes -/

/-- The delivered right owner and process two's retained receiver are the two
folds of one common finite prefix.  The prefix itself lives only in the final
proof field and is not finite controller data. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (owner : RightOwner A strategy hwin policy)
    (receiver : RightReceiver A strategy hwin (initial := initial)) : Prop :=
  ∃ (state : CompatibleState A strategy hwin initial)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false).State)
      (staged : Option (RightOutput A strategy hwin initial)),
    owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
          hwin policy state move ownerControl monitorState ∧
        state.1.2.1 = some move

/-! ## Initial and total local right steps -/

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerInitial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :
    RightOwner A strategy hwin policy :=
  ⟨state,
    profiledRawJointHybridPhysicalCompatibleRightSharedInitial A strategy hwin
      policy state⟩

noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverInitial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial) (row : PairedEntryRow) :
    RightReceiver A strategy hwin (initial := initial) :=
  ⟨state,
    profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
      state row⟩

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRight_initial_aligned
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerInitial A
        strategy hwin policy state)
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverInitial A
        strategy hwin state row) := by
  refine ⟨state, move,
    (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move false).initial,
    row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move false).initial,
    none, ?_, ?_, ?_, hmove⟩
  · simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerInitial,
      profiledRawJointHybridPhysicalCompatibleRightSharedInitial, hmove]
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverInitial,
        profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]
  · exact
      profiledRawJointHybridPhysicalCompatibleRightLocallyReachable_initial A
        strategy hwin policy state move

/-- Advance a delivered right owner.  The old member is accepted as an
argument because the actual carrier supplies it; the compatible tables are
member coherent. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) (member : Bool)
    (owner : RightOwner A strategy hwin policy) (input : In₁) :
    RightOwner A strategy hwin policy × Out₁ :=
  let next :=
    profiledRawJointHybridPhysicalCompatibleRightSharedStep A strategy hwin
      policy owner.1 member owner.2 input
  (⟨owner.1, next.1⟩, next.2)

/-- Totalized right receiver step.  Every mismatch branch retains the old
receiver and emits the supplied fallback.  The alignment invariant proves
that no such branch is taken on the semantic trace. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : RightOutput A strategy hwin initial)
    (owner : RightOwner A strategy hwin policy)
    (receiver : RightReceiver A strategy hwin (initial := initial))
    (input : In₂ × In₁) :
    RightOutput A strategy hwin initial ×
      RightReceiver A strategy hwin (initial := initial) := by
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
                profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A
                  strategy hwin policy state ownerMove ownerControl row
                    monitorState input
              exact (next.1, ⟨state, some next.2⟩)
            · exact
                (fallback,
                  ⟨state,
                    some ⟨receiverMove, row, monitorState, staged⟩⟩)
  · exact (fallback, ⟨receiverState, receiverPayload⟩)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : RightOutput A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (RightOutput A strategy hwin initial))
    (input : In₂ × In₁) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
        strategy hwin policy fallback
          ⟨state, .inr ⟨move, ownerControl⟩⟩
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ input =
      let next :=
        profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
          hwin policy state move ownerControl row monitorState input
      (next.1, ⟨state, some next.2⟩) := by
  simp
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep]

/-! ## The dangerous repeated-round preservation law -/

/-- The compatible successor phase-live overlay passes the pair test: one
strict-right round advances the delivered owner and retained receiver through
the same input, preserving their common-prefix invariant. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRight_step_preserves
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : RightOutput A strategy hwin initial)
    (owner : RightOwner A strategy hwin policy)
    (receiver : RightReceiver A strategy hwin (initial := initial))
    (haligned :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
        hwin policy owner receiver)
    (member : Bool) (input : In₂ × In₁) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
        strategy hwin policy member owner input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
        strategy hwin policy fallback owner receiver input).2 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl, hreach,
      hmove⟩
  refine ⟨state, move,
    (move.memberController A false).step ownerControl input.2,
    row,
    (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
      hwin policy state move ownerControl row monitorState input).2.2.2.1,
    some
      (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move ownerControl row monitorState input).1,
    ?_, ?_, ?_, hmove⟩
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep,
        profiledRawJointHybridPhysicalCompatibleRightSharedStep]
    exact
      (profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).state_eq
        member false ownerControl input.2
  · simp
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep,
        profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor]
  · exact hreach.step A strategy hwin row input

/-! ## Phase-selected repeated and switch receivers -/

/-- Resolve process one's underlying old pending datum and retain only the
newly initialized right receiver.  The delivered `baseShared` is the dormant
right owner which will actually take the simultaneous blind step. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (one : OnePending A strategy hwin policy) :
    RightReceiver A strategy hwin (initial := initial) :=
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
      x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveOneBasePending A
        strategy hwin one)
  ⟨installed.1.1, installed.2⟩

/-- Process two selects its retained receiver on a repeated right round
(`false`), and the freshly installed receiver after a local role switch
(`true`). -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy) :
    RightReceiver A strategy hwin (initial := initial) :=
  if two.2.1.localPhase then
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver A
      strategy hwin policy one
  else
    two.2.1.receiver two.1

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy)
    (hphase : two.2.1.localPhase = false) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo A
        strategy hwin policy two one =
      two.2.1.receiver two.1 := by
  simp
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo,
      hphase]

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_switch
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy)
    (hphase : two.2.1.localPhase = true) :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo A
        strategy hwin policy two one =
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver A
        strategy hwin policy one := by
  simp
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo,
      hphase]

/-- Advance process two's locally selected right receiver.  This is already
the physical local receive calculation; later fresh constructors only decide
which advanced/fresh receiver is cached in each unresolved continuation. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : RightOutput A strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy)
    (input : In₂ × In₁) :
    RightOutput A strategy hwin initial ×
      RightReceiver A strategy hwin (initial := initial) :=
  profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A strategy
    hwin policy fallback one.2.1.baseShared
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
        A strategy hwin policy two one)
      input

/-- A repeated strict-right round uses the retained receiver and passes the
matched-prefix pair test. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight_same_preserves
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : RightOutput A strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy)
    (hphase : two.2.1.localPhase = false)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
        hwin policy one.2.1.baseShared (two.2.1.receiver two.1))
    (input : In₂ × In₁) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
        strategy hwin policy one.1 one.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A strategy
        hwin policy fallback two one input).2 := by
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_same
      A strategy hwin policy two one hphase]
  exact
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRight_step_preserves A
      strategy hwin policy fallback one.2.1.baseShared
        (two.2.1.receiver two.1) haligned one.1 input

/-- At a local role switch, the receiver installed from process one's base
pending datum is advanced once with the dormant delivered owner.  The sole
premise is their root alignment, which the paired fresh constructor will
establish when it creates that dormant datum. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight_switch_preserves
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : RightOutput A strategy hwin initial)
    (two : TwoPending A strategy hwin policy)
    (one : OnePending A strategy hwin policy)
    (hphase : two.2.1.localPhase = true)
    (haligned :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
        hwin policy one.2.1.baseShared
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver
            A strategy hwin policy one))
    (input : In₂ × In₁) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
        strategy hwin policy one.1 one.2.1.baseShared input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A strategy
        hwin policy fallback two one input).2 := by
  rw [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight,
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo_switch
      A strategy hwin policy two one hphase]
  exact
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRight_step_preserves A
      strategy hwin policy fallback one.2.1.baseShared
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightSwitchReceiver A
          strategy hwin policy one)
        haligned one.1 input

end

end DetParityAutomaton

end DistributedSynthesis
