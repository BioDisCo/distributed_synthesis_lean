/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorMemberCutPacket

/-!
# The old table member and the new close member are independent

There are two temporally different hidden bits at a physical close.

* `tableMember` is the already selected member of the table whose finite play
  produced the current target.  It selects the target row.
* `closeMember` records whether the new physical receive was strict/open or
  simultaneous/closed.  It selects only the DPA coordinate and receiver row
  installed for the following block.

The row-generic physical cut theorem requires no equation between these bits.
This file records that fact directly, for both orientations, and gives the
minimal one-target pending payload suggested by the four-case audit.  The
payload keeps one target/key selected by the old member and two receiver
initializations selected later by the new member.

Both Booleans are proof-side occurrence data.  No executable map is passed a
graph, orientation, hierarchy side, leader bit, strict-leader bit, history,
or semantic view.
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

private abbrev SuccessorTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
    initial

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

/-! ## The four row pairs really are exhaustive -/

/-- Explicit `Bool²` audit.  In particular, neither off-diagonal case is
eliminated. -/
theorem profiledRawJointHybridPhysicalCompatible_pendingRow_pair_cases
    (tableMember closeMember : Bool) :
    (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember,
        profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) =
      match tableMember, closeMember with
      | false, false => (.first, .first)
      | false, true => (.first, .both)
      | true, false => (.both, .first)
      | true, true => (.both, .both) := by
  cases tableMember <;> cases closeMember <;> rfl

/-! ## Minimal temporally indexed payload -/

/-- A right-table close needs one old-row-selected target and two possible
initializations of the following left receiver. -/
structure ProfiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} where
  target : SuccessorTarget A strategy hwin initial
  firstReceiver :
    ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial)
  bothReceiver :
    ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial)

/-- Left-table mirror. -/
structure ProfiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} where
  target : SuccessorTarget A strategy hwin initial
  firstReceiver :
    ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial)
  bothReceiver :
    ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial)

/-- Select the current target with the old table member, then prepare both
possible rows of the next receiver at that one target key. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayloadOfOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial) (tableMember : Bool) :
    ProfiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayload A
      strategy hwin (initial := initial) :=
  let target := (output.target
    (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)).1
  { target := target
    firstReceiver :=
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .first
    bothReceiver :=
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .both }

/-- Left mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayloadOfOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial) (tableMember : Bool) :
    ProfiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayload A
      strategy hwin (initial := initial) :=
  let target := (output.target
    (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)).1
  { target := target
    firstReceiver :=
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .first
    bothReceiver :=
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .both }

def profiledRawJointHybridPhysicalCompatibleRightTemporalPendingReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayload A
        strategy hwin (initial := initial)) (closeMember : Bool) :=
  if closeMember then payload.bothReceiver else payload.firstReceiver

def profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayload A
        strategy hwin (initial := initial)) (closeMember : Bool) :=
  if closeMember then payload.bothReceiver else payload.firstReceiver

/-- The next close member changes only the receiver row; the retained target
is the old table member's target. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightTemporalPending_receiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial) (tableMember closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleRightTemporalPendingReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayloadOfOutput
          A strategy hwin output tableMember) closeMember =
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin
          (profiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayloadOfOutput
            A strategy hwin output tableMember).target)
        (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  cases closeMember <;> rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftTemporalPending_receiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial) (tableMember closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayloadOfOutput
          A strategy hwin output tableMember) closeMember =
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin
          (profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayloadOfOutput
            A strategy hwin output tableMember).target)
        (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  cases closeMember <;> rfl

/-- Both new-member candidates have literally the same compatible key. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightTemporalPending_same_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayload A
        strategy hwin (initial := initial)) :
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
        payload.target =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
        payload.target :=
  rfl

theorem
    profiledRawJointHybridPhysicalCompatibleLeftTemporalPending_same_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayload A
        strategy hwin (initial := initial)) :
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
        payload.target =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
        payload.target :=
  rfl

/-! ## Regression bridge to the operational payload

The operational carrier now uses exactly the temporal indexing audited above.
These lemmas deliberately mention both Boolean parameters: future changes
which accidentally query the target at `closeMember` instead of
`tableMember` will break this bridge, including in either off-diagonal case.
-/

/-- The corrected right operational payload retains the target chosen by the
old table member. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightOperational_target_eq_temporal
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial)
    (tableMember closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A strategy
        hwin
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
          strategy hwin output
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember))
        closeMember =
      (profiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayloadOfOutput
        A strategy hwin output tableMember).target := by
  rfl

/-- Its independently selected next receiver is literally the temporal
payload's receiver. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightOperational_receiver_eq_temporal
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial)
    (tableMember closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
          strategy hwin output
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember))
        closeMember =
      profiledRawJointHybridPhysicalCompatibleRightTemporalPendingReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRightTemporalPendingPayloadOfOutput
          A strategy hwin output tableMember) closeMember := by
  cases closeMember <;> rfl

/-- Left operational target regression. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftOperational_target_eq_temporal
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial)
    (tableMember closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A strategy
        hwin
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
          strategy hwin output
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember))
        closeMember =
      (profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayloadOfOutput
        A strategy hwin output tableMember).target := by
  rfl

/-- Left receiver regression, again with independent old and new bits. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftOperational_receiver_eq_temporal
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial)
    (tableMember closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
          strategy hwin output
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember))
        closeMember =
      profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleLeftTemporalPendingPayloadOfOutput
          A strategy hwin output tableMember) closeMember := by
  cases closeMember <;> rfl

/-! ## Row-generic two-bit physical packet -/

/-- Right-table packet with the two bits independent.  The target and its
priority use `tableMember`; only the following DPA coordinate uses
`closeMember`. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRight_memberPairCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember closeMember : Bool)
    (env : Nat → In₂ × In₁) (n : Nat) (slot : ProfiledRawLeftSlot A)
    (htarget :
      profiledRawJointHybridPhysicalCompatibleSuccessorRightTargetProjection A
          strategy hwin
          ((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A
            strategy hwin policy state move tableMember env n).2.1.target
              (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
            ).1 =
        .inr (.inr slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetRightClosingRecordForMember closeMember
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember env n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inr slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember)
          slot.1.1 := by
  let play :=
    profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy hwin
      policy state move tableMember env
  have hwins :=
    profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay_wins A strategy
      hwin policy state move tableMember env
  have htarget' :
      profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)) =
        .inr (.inr slot) := by
    simpa [play,
      profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay,
      profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection,
      profiledRawJointHybridPhysicalCompatibleSuccessorRightTargetProjection]
      using htarget
  simpa only
    [profiledRawJointHybridPhysicalCompatiblePendingRow_eq_closeRowOfMember]
    using
      (profiledRawJointTargetRight_memberCutPacket_of_wins A
        (profiledRawJointUnitRightTargetProjection A)
        (profiledRawJointRightPhysicalSiblingAllowed A move.1)
        move.1.source play hwins n
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember) slot
        htarget' closeMember physicalState word cuts k hcut hstate hlength
          hslice hclosing)

/-- Left-table mirror of the independent two-bit packet. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeft_memberPairCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember closeMember : Bool)
    (env : Nat → In₁ × In₂) (n : Nat) (slot : ProfiledRawRightSlot A)
    (htarget :
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftTargetProjection A
          strategy hwin
          ((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A
            strategy hwin policy state move tableMember env n).2.1.target
              (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
            ).1 =
        .inr (.inl slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetLeftClosingRecordForMember closeMember
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember env n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inl slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember)
          slot.1.1 := by
  let play :=
    profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy hwin
      policy state move tableMember env
  have hwins :=
    profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay_wins A strategy
      hwin policy state move tableMember env
  have htarget' :
      profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)) =
        .inr (.inl slot) := by
    simpa [play,
      profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay,
      profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection,
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftTargetProjection]
      using htarget
  simpa only
    [profiledRawJointHybridPhysicalCompatiblePendingRow_eq_closeRowOfMember]
    using
      (profiledRawJointTargetLeft_memberCutPacket_of_wins A
        (profiledRawJointUnitLeftTargetProjection A)
        (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
        move.1.source play hwins n
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember) slot
        htarget' closeMember physicalState word cuts k hcut hstate hlength
          hslice hclosing)

end

end DetParityAutomaton

end DistributedSynthesis
