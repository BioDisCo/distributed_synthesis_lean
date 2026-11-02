/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableOwnerFibreSafetyAutomaton
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreSafetyAtKey

/-!
# Fixed-key extensionality of the raw finite-table owner kernel

An uncertified table family is consulted only at the root key stored in its
bank state.  Therefore two raw families which agree at that key produce the
same resolved packets, informed forks, decoded receives, complete rounds, and
guarded safety steps from every state in that fibre.  This is the raw half of
the transfer from the per-key enriched checker to one assembled certified
policy.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

private abbrev OneControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
    (Memory := Memory) A strategy

private abbrev TwoControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
    (Memory := Memory) A strategy

private abbrev TableSelection :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) A strategy

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable (tables other : TableSelection (Memory := Memory) A strategy)

/-- Agreement of two raw table families at one root key. -/
def AgreeAt (key : RootKey A strategy) : Prop :=
  tables key = other key

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem successor_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.AtKey A strategy key)
    (childCode : LinkedCode A)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.successor A strategy state childCode =
      other.successor A strategy state childCode := by
  change state.1 = key at hkey
  subst key
  unfold AgreeAt at hagrees
  unfold successor
  rw [hagrees]

section
omit [Fintype Memory]

theorem childRealizes_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.AtKey A strategy key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ChildRealizes A strategy hwin state target childCode ↔
      other.ChildRealizes A strategy hwin state target childCode := by
  change state.1 = key at hkey
  subst key
  unfold AgreeAt at hagrees
  unfold ChildRealizes successor
  rw [hagrees]

theorem resolveTarget_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.AtKey A strategy key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.resolveTarget A strategy hwin state target =
      other.resolveTarget A strategy hwin state target := by
  change state.1 = key at hkey
  subst key
  unfold AgreeAt at hagrees
  unfold resolveTarget ChildRealizes successor
  rw [hagrees]

theorem resolvePacket_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.AtKey A strategy key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.resolvePacket A strategy hwin state target =
      other.resolvePacket A strategy hwin state target := by
  dsimp only [resolvePacket]
  rw [tables.resolveTarget_congr_at A strategy hwin other key state hkey
    target hagrees]
  rw [tables.successor_congr_at A strategy other key state hkey
    (other.resolveTarget A strategy hwin state target) hagrees]

theorem rightBoundaryOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := Memory) A strategy)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : data.1.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.rightBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input =
      other.rightBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input := by
  unfold rightBoundaryOwnerFibreReceive
  rw [tables.resolvePacket_congr_at A strategy hwin other key data.1 hkey
    (data.target (Memory := Memory) A strategy input) hagrees]

theorem leftBoundaryOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := Memory) A strategy)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : data.1.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.leftBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input =
      other.leftBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input := by
  unfold leftBoundaryOwnerFibreReceive
  rw [tables.resolvePacket_congr_at A strategy hwin other key data.1 hkey
    (data.target (Memory := Memory) A strategy input) hagrees]

theorem rightReceiveFor_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (hkey : state.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.rightReceiveFor A strategy hwin state receiver owner input =
      other.rightReceiveFor A strategy hwin state receiver owner input := by
  unfold rightReceiveFor
  generalize
    stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1 owner
      receiver.2.1 receiver.2.2.1 input = next
  cases htarget : next.2.2.2.2 with
  | none => simp [htarget]
  | some target =>
      simp only [htarget]
      rw [tables.resolvePacket_congr_at A strategy hwin other key state hkey
        target hagrees]

theorem leftReceiveFor_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : state.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.leftReceiveFor A strategy hwin state receiver owner input =
      other.leftReceiveFor A strategy hwin state receiver owner input := by
  unfold leftReceiveFor
  generalize
    stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1 owner
      receiver.2.1 receiver.2.2.1 input = next
  cases htarget : next.2.2.2.2 with
  | none => simp [htarget]
  | some target =>
      simp only [htarget]
      rw [tables.resolvePacket_congr_at A strategy hwin other key state hkey
        target hagrees]

theorem rightToLeftBridgeForkTwo_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (hkey : state.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.rightToLeftBridgeForkTwo A strategy hwin state receiver owner input =
      other.rightToLeftBridgeForkTwo A strategy hwin state receiver owner
        input := by
  unfold rightToLeftBridgeForkTwo
  rw [tables.rightReceiveFor_congr_at A strategy hwin other key state receiver
    owner input hkey hagrees]
  dsimp only
  rw [tables.resolvePacket_congr_at A strategy hwin other key state hkey _
    hagrees]

theorem leftToRightBridgeForkOne_congr_at
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : state.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.leftToRightBridgeForkOne A strategy hwin state receiver owner input =
      other.leftToRightBridgeForkOne A strategy hwin state receiver owner
        input := by
  unfold leftToRightBridgeForkOne
  rw [tables.leftReceiveFor_congr_at A strategy hwin other key state receiver
    owner input hkey hagrees]
  dsimp only
  rw [tables.resolvePacket_congr_at A strategy hwin other key state hkey _
    hagrees]

theorem rightPhaseOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (hkey : data.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.rightPhaseOwnerFibreReceive A strategy hwin data input =
      other.rightPhaseOwnerFibreReceive A strategy hwin data input := by
  unfold rightPhaseOwnerFibreReceive
  dsimp only
  rw [tables.rightBoundaryOwnerFibreReceive_congr_at A strategy hwin other
    key data.1 data.2.1 data.2.2 input hkey.1 hagrees]
  rw [tables.rightToLeftBridgeForkTwo_congr_at A strategy hwin other key
    data.1.1 (data.1.receiver (Memory := Memory) A strategy)
      (data.1.owner (Memory := Memory) A strategy) (input.2, input.1)
      hkey.1 hagrees]
  rw [tables.resolvePacket_congr_at A strategy hwin other key data.1.1 hkey.1
    (data.1.target (Memory := Memory) A strategy input) hagrees]

theorem leftPhaseOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (hkey : data.AtKey A strategy key)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.leftPhaseOwnerFibreReceive A strategy hwin data input =
      other.leftPhaseOwnerFibreReceive A strategy hwin data input := by
  unfold leftPhaseOwnerFibreReceive
  dsimp only
  rw [tables.leftBoundaryOwnerFibreReceive_congr_at A strategy hwin other key
    data.1 data.2.1 data.2.2 input hkey.1 hagrees]
  rw [tables.leftToRightBridgeForkOne_congr_at A strategy hwin other key
    data.1.1 (data.1.receiver (Memory := Memory) A strategy)
      (data.1.owner (Memory := Memory) A strategy) input hkey.1 hagrees]
  rw [tables.resolvePacket_congr_at A strategy hwin other key data.1.1 hkey.1
    (data.1.target (Memory := Memory) A strategy input) hagrees]

theorem ownerFibreBoundaryReceive?_congr_at
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy)
    (two : TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreBoundaryReceive? A strategy hwin one two input =
      other.ownerFibreBoundaryReceive? A strategy hwin one two input := by
  cases hright :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy one two with
  | some data =>
      have hdata :=
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.rightBoundaryData?_atKey
          (Memory := Memory) A strategy key one two data hone htwo hright
      simp only [ownerFibreBoundaryReceive?, hright]
      rw [tables.rightPhaseOwnerFibreReceive_congr_at A strategy hwin other
        key data input hdata hagrees]
  | none =>
      cases hleft :
          profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
            (Memory := Memory) A strategy one two with
      | some data =>
          have hdata :=
            ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.leftBoundaryData?_atKey
              (Memory := Memory) A strategy key one two data hone htwo hleft
          simp only [ownerFibreBoundaryReceive?, hright, hleft]
          rw [tables.leftPhaseOwnerFibreReceive_congr_at A strategy hwin other
            key data input hdata hagrees]
      | none => simp [ownerFibreBoundaryReceive?, hright, hleft]

theorem ownerFibreBoundaryOpenRecvOne_congr_at
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo =
      other.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo := by
  unfold ownerFibreBoundaryOpenRecvOne
  rw [tables.ownerFibreBoundaryReceive?_congr_at A strategy hwin other key one
    two (inputOne, inputTwo) hone htwo hagrees]

theorem ownerFibreBoundaryOpenRecvTwo_congr_at
    (key : RootKey A strategy)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne =
      other.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne := by
  unfold ownerFibreBoundaryOpenRecvTwo
  rw [tables.ownerFibreBoundaryReceive?_congr_at A strategy hwin other key one
    two (inputOne, inputTwo) hone htwo hagrees]

theorem ownerFibreBoundaryCloseRound_congr_at
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
        inputTwo =
      other.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
        inputTwo := by
  unfold ownerFibreBoundaryCloseRound
  rw [tables.ownerFibreBoundaryReceive?_congr_at A strategy hwin other key one
    two (inputOne, inputTwo) hone htwo hagrees]

theorem ownerFibreRound_congr_at
    (key : RootKey A strategy)
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key controls.1)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key controls.2)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreRound A strategy hwin controls input graph =
      other.ownerFibreRound A strategy hwin controls input graph := by
  cases graph with
  | right =>
      unfold ownerFibreRound
      rw [tables.ownerFibreBoundaryOpenRecvTwo_congr_at A strategy hwin other
        key controls.2 input.2 controls.1 input.1 htwo hone hagrees]
  | left =>
      unfold ownerFibreRound
      rw [tables.ownerFibreBoundaryOpenRecvOne_congr_at A strategy hwin other
        key controls.1 input.1 controls.2 input.2 hone htwo hagrees]
  | both =>
      exact tables.ownerFibreBoundaryCloseRound_congr_at A strategy hwin other
        key controls.1 input.1 controls.2 input.2 hone htwo hagrees

theorem ownerFibreRoundRecord_congr_at
    (key : RootKey A strategy)
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key controls.1)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key controls.2)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreRoundRecord A strategy hwin controls input graph =
      other.ownerFibreRoundRecord A strategy hwin controls input graph := by
  unfold ownerFibreRoundRecord
  rw [tables.ownerFibreRound_congr_at A strategy hwin other key controls input
    graph hone htwo hagrees]

theorem ownerFibreSafetyLiveStep_congr_at
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := Memory) A strategy)
    (direction :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂))
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
        (Memory := Memory) A strategy key state)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreSafetyLiveStep A strategy hwin state direction =
      other.ownerFibreSafetyLiveStep A strategy hwin state direction := by
  unfold ownerFibreSafetyLiveStep
  rw [tables.ownerFibreRound_congr_at A strategy hwin other key state.1
    direction.1 direction.2 hkey.1 hkey.2 hagrees]
  rw [tables.ownerFibreRoundRecord_congr_at A strategy hwin other key state.1
    direction.1 direction.2 hkey.1 hkey.2 hagrees]

theorem ownerFibreSafetyStep_congr_at
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
        (Memory := Memory) A strategy)
    (direction :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂))
    (hkey :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.SafetyStateAtKey
        (Memory := Memory) A strategy key state)
    (hagrees : tables.AgreeAt A strategy other key) :
    tables.ownerFibreSafetyStep A strategy hwin state direction =
      other.ownerFibreSafetyStep A strategy hwin state direction := by
  cases state with
  | none => rfl
  | some live =>
      by_cases hdecodes :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := Memory) A strategy live.1.1 live.1.2
      · simp only [ownerFibreSafetyStep, hdecodes, if_pos, Option.some.injEq]
        exact tables.ownerFibreSafetyLiveStep_congr_at A strategy hwin other
          key live direction hkey hagrees
      · simp [ownerFibreSafetyStep, hdecodes]

end

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

end

end DetParityAutomaton

end DistributedSynthesis
