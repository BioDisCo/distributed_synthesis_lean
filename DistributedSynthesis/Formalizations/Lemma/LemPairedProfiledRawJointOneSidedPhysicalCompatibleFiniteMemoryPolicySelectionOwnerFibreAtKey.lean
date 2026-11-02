/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreHonestEntry

/-!
# Fixed-key locality of the finite-memory owner-fibre kernel

Every bank coordinate stored by a well-formed owner-fibre state retains its
root key.  Consequently, two global finite-memory policy selections which
agree at that key induce identical physical rounds from the state.  This is
the locality theorem needed for diagonal assembly of independently certified
root fibres.
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

private abbrev OneControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
    (Memory := Memory) A strategy

private abbrev TwoControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
    (Memory := Memory) A strategy

private abbrev PolicySelection
    (initialMemory : RootKey A strategy → Memory) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
    (Memory := Memory) A strategy hwin initialMemory

/-! ## Blind transitions preserve the stored root key -/

omit [Inhabited Out₁] [Fintype Memory] in
theorem ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey
        (Memory := Memory) A strategy key control)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey
      (Memory := Memory) A strategy key
      (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
        (Memory := Memory) A strategy control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      change state.AtKey A strategy key ∧ _ at hkey
      cases packet with
      | none => exact hkey
      | some packet =>
          have hsuccessor := hkey.2 packet rfl
          dsimp [profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv]
          split
          · exact hkey
          · exact hsuccessor
  | inr installed =>
      exact hkey

omit [Inhabited Out₂] [Fintype Memory] in
theorem ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey
        (Memory := Memory) A strategy key control)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey
      (Memory := Memory) A strategy key
      (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
        (Memory := Memory) A strategy control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      change state.AtKey A strategy key ∧ _ at hkey
      cases packet with
      | none => exact hkey
      | some packet =>
          have hsuccessor := hkey.2 packet rfl
          dsimp [profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv]
          split
          · exact hkey
          · exact hsuccessor
  | inr installed =>
      exact hkey

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey
        (Memory := Memory) A strategy key control)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey
      (Memory := Memory) A strategy key
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
        (Memory := Memory) A strategy control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simpa [ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hkey

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey
        (Memory := Memory) A strategy key control)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey
      (Memory := Memory) A strategy key
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
        (Memory := Memory) A strategy control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simpa [ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hkey

omit [Inhabited Out₂] [Fintype Memory] in
theorem
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey.noRecv
    (key : RootKey A strategy)
    (control : OneControl (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key control)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
      (Memory := Memory) A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := Memory) A strategy control input).1 := by
  rcases control with ⟨base, coordinates⟩
  rcases hkey with ⟨hbase, hcoordinates⟩
  cases base with
  | inl bridge =>
      exact ⟨hbase.noRecv (Memory := Memory) A strategy key bridge input,
        hcoordinates⟩
  | inr pending =>
      exact ⟨hbase.noRecv (Memory := Memory) A strategy key pending input,
        hcoordinates⟩

omit [Inhabited Out₁] [Fintype Memory] in
theorem
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey.noRecv
    (key : RootKey A strategy)
    (control : TwoControl (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key control)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
      (Memory := Memory) A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := Memory) A strategy control input).1 := by
  rcases control with ⟨base, coordinates⟩
  rcases hkey with ⟨hbase, hcoordinates⟩
  cases base with
  | inl bridge =>
      exact ⟨hbase.noRecv (Memory := Memory) A strategy key bridge input,
        hcoordinates⟩
  | inr pending =>
      exact ⟨hbase.noRecv (Memory := Memory) A strategy key pending input,
        hcoordinates⟩

/-! ## Informed forks preserve the stored root key -/

def ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData.AtKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy) : Prop :=
  data.1.1.AtKey A strategy key ∧ data.2.1.AtKey A strategy key

def ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData.AtKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy) : Prop :=
  data.1.1.AtKey A strategy key ∧ data.2.1.AtKey A strategy key

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory]

theorem
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey.receiver
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey
        (Memory := Memory) A strategy key control) :
    (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
      (Memory := Memory) A strategy control).1.AtKey A strategy key := by
  by_cases hmember : control.1
  · simpa [profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
      hmember] using hkey.2
  · simpa [profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
      hmember] using hkey.1

theorem
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey.receiver
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (hkey :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey
        (Memory := Memory) A strategy key control) :
    (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
      (Memory := Memory) A strategy control).1.AtKey A strategy key := by
  by_cases hmember : control.1
  · simpa [profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
      hmember] using hkey.2
  · simpa [profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
      hmember] using hkey.1

theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork_atKey
    (key : RootKey A strategy)
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (hold : oldState.AtKey A strategy key)
    (hpacket : packet.AtKey A strategy key) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey
        (Memory := Memory) A strategy key fork.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey
        (Memory := Memory) A strategy key fork.closedControl := by
  exact ⟨⟨hold, hpacket⟩, ⟨hold, hpacket⟩⟩

theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork_atKey
    (key : RootKey A strategy)
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (input : In₂ × In₁)
    (hold : oldState.AtKey A strategy key)
    (hpacket : packet.AtKey A strategy key) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey
        (Memory := Memory) A strategy key fork.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey
        (Memory := Memory) A strategy key fork.closedControl := by
  exact ⟨⟨hold, hpacket⟩, ⟨hold, hpacket⟩⟩

end

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection other : PolicySelection (Memory := Memory) A strategy hwin
    initialMemory)

theorem rightToLeftBridgeForkTwo_atKey
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (hstate : state.AtKey A strategy key) :
    let fork :=
      (selection.rightToLeftBridgeForkTwo A strategy hwin initialMemory state
        receiver owner input).1
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey
        (Memory := Memory) A strategy key fork.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey
        (Memory := Memory) A strategy key fork.closedControl := by
  change state.1 = key at hstate
  simp only [rightToLeftBridgeForkTwo]
  split <;>
    simp [rightReceiveFor,
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl.AtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget.AtKey,
      hstate]

theorem leftToRightBridgeForkOne_atKey
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hstate : state.AtKey A strategy key) :
    let fork :=
      (selection.leftToRightBridgeForkOne A strategy hwin initialMemory state
        receiver owner input).1
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey
        (Memory := Memory) A strategy key fork.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey
        (Memory := Memory) A strategy key fork.closedControl := by
  change state.1 = key at hstate
  simp only [leftToRightBridgeForkOne]
  split <;>
    simp [leftReceiveFor,
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl.AtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget.AtKey,
      hstate]

theorem rightBoundaryOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := Memory) A strategy)
    (oldState :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : data.1.1 = key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.rightBoundaryOwnerFibreReceive A strategy hwin initialMemory
        data oldState oldOwner input =
      other.rightBoundaryOwnerFibreReceive A strategy hwin initialMemory
        data oldState oldOwner input := by
  unfold rightBoundaryOwnerFibreReceive
  rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other key
    data.1 hkey (data.target (Memory := Memory) A strategy input) hagrees]

theorem leftBoundaryOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := Memory) A strategy)
    (oldState :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : data.1.1 = key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.leftBoundaryOwnerFibreReceive A strategy hwin initialMemory
        data oldState oldOwner input =
      other.leftBoundaryOwnerFibreReceive A strategy hwin initialMemory
        data oldState oldOwner input := by
  unfold leftBoundaryOwnerFibreReceive
  rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other key
    data.1 hkey (data.target (Memory := Memory) A strategy input) hagrees]

/-! A successful decoder can only expose bank states already stored in the
two endpoints.  Hence decoded phase data inherit the common root key. -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem rightBoundaryData?_atKey
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy)
    (two : TwoControl (Memory := Memory) A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy one two = some data) :
    data.AtKey A strategy key := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  rcases hone with ⟨honeBase, honeRight, honeLeft⟩
  rcases htwo with ⟨htwoBase, htwoRight, htwoLeft⟩
  rcases oneBase with oneBridge | onePending
  · rcases oneBridge with oneStaged | oneInstalled
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled <;>
          simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
            at hdecode
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
          at hdecode
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled
        · rcases twoStaged with ⟨stagedState, receiver, packet⟩
          change stagedState.AtKey A strategy key ∧ _ at htwoBase
          cases packet with
          | none =>
              simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | some packet =>
              have hpacket := htwoBase.2 packet rfl
              cases hmove : packet.successor.2.1.1.2.2 with
              | none =>
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                    hmove] at hdecode
              | some move =>
                  have hdecode' := hdecode
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                    hmove] at hdecode'
                  have hstates :=
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
                      (Memory := Memory) A strategy oneInstalled.1
                        oneInstalled.2.1 receiver packet.successor
                        ⟨move, (move.memberController A false).initial⟩
                        (initialProfiledRawJointLeftPhysicalSiblingReceiver A
                          move .first) data
                        hdecode'.2
                  exact ⟨by rw [hstates.1]; exact honeBase,
                    by rw [hstates.2]; exact hpacket⟩
        · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
            at hdecode
      · have hreceiver :=
          htwoBase.receiver (Memory := Memory) A strategy key twoPending
        simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
          at hdecode
        split at hdecode
        · have hstates :=
            profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
              (Memory := Memory) A strategy oneInstalled.1
                oneInstalled.2.1
                (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                  (Memory := Memory) A strategy twoPending).2
                oneCoordinates.2
                (profiledRawJointLeftOwnerFibreExceptional A
                  twoPending.2.1.1)
                (twoPending.2.1.1.finiteMemoryReceiverAt A
                  oneInstalled.2.2) data hdecode
          exact ⟨by rw [hstates.1]; exact honeBase,
            by rw [hstates.2]; exact honeLeft⟩
        · simp at hdecode
  · rcases twoBase with twoBridge | twoPending
    · rcases twoBridge with twoStaged | twoInstalled
      · rcases twoStaged with ⟨stagedState, receiver, packet⟩
        change stagedState.AtKey A strategy key ∧ _ at htwoBase
        cases packet with
        | none =>
            simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
              at hdecode
        | some packet =>
            have hpacket := htwoBase.2 packet rfl
            cases hmove : packet.successor.2.1.1.2.2 with
            | none =>
                simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                  hmove] at hdecode
            | some move =>
                have hstates :=
                  profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
                    (Memory := Memory) A strategy stagedState
                      (profiledRawJointRightOwnerFibreExceptional A
                        onePending.2.1.1)
                      (onePending.2.1.1.finiteMemoryReceiverAt A receiver)
                      packet.successor
                      ⟨move, (move.memberController A false).initial⟩
                      (initialProfiledRawJointLeftPhysicalSiblingReceiver A
                        move .first) data
                      (by simpa [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                        hmove] using hdecode)
                exact ⟨by rw [hstates.1]; exact htwoBase.1,
                  by rw [hstates.2]; exact hpacket⟩
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
          at hdecode
    · have hright :=
        htwoBase.receiver (Memory := Memory) A strategy key twoPending
      have hleft :=
        honeBase.receiver (Memory := Memory) A strategy key onePending
      simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
        at hdecode
      split at hdecode
      · have hstates :=
          profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
            (Memory := Memory) A strategy
              (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                (Memory := Memory) A strategy twoPending).1
              (profiledRawJointRightOwnerFibreExceptional A
                onePending.2.1.1)
              (onePending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                  (Memory := Memory) A strategy twoPending).2)
              (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                (Memory := Memory) A strategy onePending).1
              (profiledRawJointLeftOwnerFibreExceptional A
                twoPending.2.1.1)
              (twoPending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                  (Memory := Memory) A strategy onePending).2)
              data hdecode
        exact ⟨by rw [hstates.1]; exact hright,
          by rw [hstates.2]; exact hleft⟩
      · simp at hdecode

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem leftBoundaryData?_atKey
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy)
    (two : TwoControl (Memory := Memory) A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy one two = some data) :
    data.AtKey A strategy key := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  rcases hone with ⟨honeBase, honeRight, honeLeft⟩
  rcases htwo with ⟨htwoBase, htwoRight, htwoLeft⟩
  rcases oneBase with oneBridge | onePending
  · rcases oneBridge with oneStaged | oneInstalled
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled
        · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
            at hdecode
        · rcases oneStaged with ⟨stagedState, receiver, packet⟩
          change stagedState.AtKey A strategy key ∧ _ at honeBase
          cases packet with
          | none =>
              simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode
          | some packet =>
              have hpacket := honeBase.2 packet rfl
              cases hmove : packet.successor.2.1.1.2.1 with
              | none =>
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                    hmove] at hdecode
              | some move =>
                  have hdecode' := hdecode
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                    hmove] at hdecode'
                  have hstates :=
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
                      (Memory := Memory) A strategy twoInstalled.1
                        twoInstalled.2.1 receiver packet.successor
                        ⟨move, (move.memberController A false).initial⟩
                        (initialProfiledRawJointRightPhysicalSiblingReceiver A
                          move .first) data hdecode'.2
                  exact ⟨by rw [hstates.1]; exact htwoBase,
                    by rw [hstates.2]; exact hpacket⟩
      · rcases oneStaged with ⟨stagedState, receiver, packet⟩
        change stagedState.AtKey A strategy key ∧ _ at honeBase
        cases hmember : twoPending.1 with
        | false =>
            simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
              hmember] at hdecode
        | true =>
            cases packet with
            | none =>
                simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                  hmember] at hdecode
            | some packet =>
                have hpacket := honeBase.2 packet rfl
                cases hmove : packet.successor.2.1.1.2.1 with
                | none =>
                    simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                      hmember, hmove] at hdecode
                | some move =>
                    have hstates :=
                      profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
                        (Memory := Memory) A strategy stagedState
                          (profiledRawJointLeftOwnerFibreExceptional A
                            twoPending.2.1.1)
                          (twoPending.2.1.1.finiteMemoryReceiverAt A receiver)
                          packet.successor
                          ⟨move, (move.memberController A false).initial⟩
                          (initialProfiledRawJointRightPhysicalSiblingReceiver A
                            move .first) data
                          (by simpa [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                            hmember, hmove] using hdecode)
                    exact ⟨by rw [hstates.1]; exact honeBase.1,
                      by rw [hstates.2]; exact hpacket⟩
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled <;>
          simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
            at hdecode
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
          at hdecode
  · rcases twoBase with twoBridge | twoPending
    · rcases twoBridge with twoStaged | twoInstalled
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
          at hdecode
      · have hreceiver :=
          honeBase.receiver (Memory := Memory) A strategy key onePending
        simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
          at hdecode
        split at hdecode
        · have hstates :=
            profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
              (Memory := Memory) A strategy twoInstalled.1
                twoInstalled.2.1
                (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                  (Memory := Memory) A strategy onePending).2
                twoCoordinates.1
                (profiledRawJointRightOwnerFibreExceptional A
                  onePending.2.1.1)
                (onePending.2.1.1.finiteMemoryReceiverAt A
                  twoInstalled.2.2) data hdecode
          exact ⟨by rw [hstates.1]; exact htwoBase,
            by rw [hstates.2]; exact htwoRight⟩
        · simp at hdecode
    · have hleft :=
        honeBase.receiver (Memory := Memory) A strategy key onePending
      have hright :=
        htwoBase.receiver (Memory := Memory) A strategy key twoPending
      simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
        at hdecode
      split at hdecode
      · have hstates :=
          profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
            (Memory := Memory) A strategy
              (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                (Memory := Memory) A strategy onePending).1
              (profiledRawJointLeftOwnerFibreExceptional A
                twoPending.2.1.1)
              (twoPending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                  (Memory := Memory) A strategy onePending).2)
              (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                (Memory := Memory) A strategy twoPending).1
              (profiledRawJointRightOwnerFibreExceptional A
                onePending.2.1.1)
              (onePending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                  (Memory := Memory) A strategy twoPending).2)
              data hdecode
        exact ⟨by rw [hstates.1]; exact hleft,
          by rw [hstates.2]; exact hright⟩
      · simp at hdecode

theorem rightReceiveFor_congr_at
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (hkey : state.AtKey A strategy key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.rightReceiveFor A strategy hwin initialMemory state receiver
        owner input =
      other.rightReceiveFor A strategy hwin initialMemory state receiver owner
        input := by
  unfold rightReceiveFor
  generalize
    stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1 owner
      receiver.2.1 receiver.2.2.1 input = next
  cases htarget : next.2.2.2.2 with
  | none => simp [htarget]
  | some target =>
      simp only [htarget]
      rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other
        key state hkey target hagrees]

theorem leftReceiveFor_congr_at
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : state.AtKey A strategy key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.leftReceiveFor A strategy hwin initialMemory state receiver owner
        input =
      other.leftReceiveFor A strategy hwin initialMemory state receiver owner
        input := by
  unfold leftReceiveFor
  generalize
    stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1 owner
      receiver.2.1 receiver.2.2.1 input = next
  cases htarget : next.2.2.2.2 with
  | none => simp [htarget]
  | some target =>
      simp only [htarget]
      rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other
        key state hkey target hagrees]

theorem rightToLeftBridgeForkTwo_congr_at
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (hkey : state.AtKey A strategy key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.rightToLeftBridgeForkTwo A strategy hwin initialMemory state
        receiver owner input =
      other.rightToLeftBridgeForkTwo A strategy hwin initialMemory state
        receiver owner input := by
  unfold rightToLeftBridgeForkTwo
  rw [selection.rightReceiveFor_congr_at A strategy hwin initialMemory other
    key state receiver owner input hkey hagrees]
  dsimp only
  rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other key
    state hkey _ hagrees]

theorem leftToRightBridgeForkOne_congr_at
    (key : RootKey A strategy)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : state.AtKey A strategy key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.leftToRightBridgeForkOne A strategy hwin initialMemory state
        receiver owner input =
      other.leftToRightBridgeForkOne A strategy hwin initialMemory state
        receiver owner input := by
  unfold leftToRightBridgeForkOne
  rw [selection.leftReceiveFor_congr_at A strategy hwin initialMemory other
    key state receiver owner input hkey hagrees]
  dsimp only
  rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other key
    state hkey _ hagrees]

theorem rightPhaseOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (hkey : data.AtKey A strategy key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.rightPhaseOwnerFibreReceive A strategy hwin initialMemory data
        input =
      other.rightPhaseOwnerFibreReceive A strategy hwin initialMemory data
        input := by
  unfold rightPhaseOwnerFibreReceive
  dsimp only
  rw [selection.rightBoundaryOwnerFibreReceive_congr_at A strategy hwin
    initialMemory other key data.1 data.2.1 data.2.2 input hkey.1 hagrees]
  rw [selection.rightToLeftBridgeForkTwo_congr_at A strategy hwin
    initialMemory other key data.1.1
      (data.1.receiver (Memory := Memory) A strategy)
      (data.1.owner (Memory := Memory) A strategy) (input.2, input.1)
      hkey.1 hagrees]
  rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other key
    data.1.1 hkey.1 (data.1.target (Memory := Memory) A strategy input)
      hagrees]

theorem leftPhaseOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (hkey : data.AtKey A strategy key)
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.leftPhaseOwnerFibreReceive A strategy hwin initialMemory data
        input =
      other.leftPhaseOwnerFibreReceive A strategy hwin initialMemory data
        input := by
  unfold leftPhaseOwnerFibreReceive
  dsimp only
  rw [selection.leftBoundaryOwnerFibreReceive_congr_at A strategy hwin
    initialMemory other key data.1 data.2.1 data.2.2 input hkey.1 hagrees]
  rw [selection.leftToRightBridgeForkOne_congr_at A strategy hwin
    initialMemory other key data.1.1
      (data.1.receiver (Memory := Memory) A strategy)
      (data.1.owner (Memory := Memory) A strategy) input hkey.1 hagrees]
  rw [selection.resolvePacket_congr_at A strategy hwin initialMemory other key
    data.1.1 hkey.1 (data.1.target (Memory := Memory) A strategy input)
      hagrees]

theorem rightPhaseOwnerFibreReceive_atKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hkey : data.AtKey A strategy key)
    (input : In₁ × In₂) :
    let result :=
      selection.rightPhaseOwnerFibreReceive A strategy hwin initialMemory data
        input
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1.closedControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.2.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.2.1.closedControl := by
  rcases data with ⟨⟨state, ⟨receiver, owner⟩, oldReceiver⟩,
    oldState, oldOwner⟩
  rcases hkey with ⟨hstate, hold⟩
  let packet := selection.resolvePacket A strategy hwin initialMemory state
    (((((receiver.1.memberController A false).labelOf owner).2
      receiver.2.2.1 (input.2, input.1)).target receiver.2.1))
  have hpacket : packet.AtKey A strategy key := by
    change (selection.successor A strategy hwin initialMemory state _).1 = key
    rw [selection.successor_index A strategy hwin initialMemory]
    exact hstate
  have hphase :=
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork_atKey
      (Memory := Memory) A strategy key ⟨receiver.1, owner⟩ oldState
        oldReceiver oldOwner packet input hold hpacket
  have hbridge := selection.rightToLeftBridgeForkTwo_atKey A strategy hwin
    initialMemory key state receiver owner (input.2, input.1) hstate
  rcases hphase with ⟨hphaseOpen, hphaseClosed⟩
  rcases hbridge with ⟨hbridgeOpen, hbridgeClosed⟩
  exact ⟨⟨hphaseOpen, hstate, hold⟩,
    ⟨hphaseClosed, hstate, hpacket⟩,
    ⟨hbridgeOpen, hstate, hpacket⟩,
    ⟨hbridgeClosed, hstate, hpacket⟩⟩

theorem leftPhaseOwnerFibreReceive_atKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hkey : data.AtKey A strategy key)
    (input : In₁ × In₂) :
    let result :=
      selection.leftPhaseOwnerFibreReceive A strategy hwin initialMemory data
        input
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1.closedControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.2.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.2.1.closedControl := by
  rcases data with ⟨⟨state, ⟨receiver, owner⟩, oldReceiver⟩,
    oldState, oldOwner⟩
  rcases hkey with ⟨hstate, hold⟩
  let packet := selection.resolvePacket A strategy hwin initialMemory state
    (((((receiver.1.memberController A false).labelOf owner).2
      receiver.2.2.1 input).target receiver.2.1))
  have hpacket : packet.AtKey A strategy key := by
    change (selection.successor A strategy hwin initialMemory state _).1 = key
    rw [selection.successor_index A strategy hwin initialMemory]
    exact hstate
  have hphase :=
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork_atKey
      (Memory := Memory) A strategy key ⟨receiver.1, owner⟩ oldState
        oldReceiver oldOwner packet (input.2, input.1) hold hpacket
  have hbridge := selection.leftToRightBridgeForkOne_atKey A strategy hwin
    initialMemory key state receiver owner input hstate
  rcases hphase with ⟨hphaseOpen, hphaseClosed⟩
  rcases hbridge with ⟨hbridgeOpen, hbridgeClosed⟩
  exact ⟨⟨hbridgeOpen, hpacket, hstate⟩,
    ⟨hbridgeClosed, hpacket, hstate⟩,
    ⟨hphaseOpen, hold, hstate⟩,
    ⟨hphaseClosed, hpacket, hstate⟩⟩

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
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreBoundaryReceive? A strategy hwin initialMemory one two
        input =
      other.ownerFibreBoundaryReceive? A strategy hwin initialMemory one two
        input := by
  cases hright :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy one two with
  | some data =>
      have hdata := rightBoundaryData?_atKey (Memory := Memory) A strategy
        key one two data hone htwo hright
      simp only [ownerFibreBoundaryReceive?, hright]
      rw [selection.rightPhaseOwnerFibreReceive_congr_at A strategy hwin
        initialMemory other key data input hdata hagrees]
  | none =>
      cases hleft :
          profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
            (Memory := Memory) A strategy one two with
      | some data =>
          have hdata := leftBoundaryData?_atKey (Memory := Memory) A strategy
            key one two data hone htwo hleft
          simp only [ownerFibreBoundaryReceive?, hright, hleft]
          rw [selection.leftPhaseOwnerFibreReceive_congr_at A strategy hwin
            initialMemory other key data input hdata hagrees]
      | none => simp [ownerFibreBoundaryReceive?, hright, hleft]

theorem ownerFibreBoundaryReceive?_atKey
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy)
    (two : TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂)
    (result :
      (FiniteDelayedFork (OneControl (Memory := Memory) A strategy) × Out₁) ×
        (FiniteDelayedFork (TwoControl (Memory := Memory) A strategy) × Out₂))
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin
      initialMemory one two input = some result) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1.closedControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.2.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.2.1.closedControl := by
  cases hright :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy one two with
  | some data =>
      have hdata := rightBoundaryData?_atKey (Memory := Memory) A strategy
        key one two data hone htwo hright
      have hall := selection.rightPhaseOwnerFibreReceive_atKey A strategy hwin
        initialMemory key data hdata input
      rw [ownerFibreBoundaryReceive?, hright] at hreceive
      cases Option.some.inj hreceive
      exact hall
  | none =>
      cases hleft :
          profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
            (Memory := Memory) A strategy one two with
      | some data =>
          have hdata := leftBoundaryData?_atKey (Memory := Memory) A strategy
            key one two data hone htwo hleft
          have hall := selection.leftPhaseOwnerFibreReceive_atKey A strategy
            hwin initialMemory key data hdata input
          rw [ownerFibreBoundaryReceive?, hright, hleft] at hreceive
          cases Option.some.inj hreceive
          exact hall
      | none => simp [ownerFibreBoundaryReceive?, hright, hleft] at hreceive

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
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreBoundaryOpenRecvOne A strategy hwin initialMemory one
        inputOne two inputTwo =
      other.ownerFibreBoundaryOpenRecvOne A strategy hwin initialMemory one
        inputOne two inputTwo := by
  unfold ownerFibreBoundaryOpenRecvOne
  rw [selection.ownerFibreBoundaryReceive?_congr_at A strategy hwin
    initialMemory other key one two (inputOne, inputTwo) hone htwo hagrees]

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
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreBoundaryOpenRecvTwo A strategy hwin initialMemory two
        inputTwo one inputOne =
      other.ownerFibreBoundaryOpenRecvTwo A strategy hwin initialMemory two
        inputTwo one inputOne := by
  unfold ownerFibreBoundaryOpenRecvTwo
  rw [selection.ownerFibreBoundaryReceive?_congr_at A strategy hwin
    initialMemory other key one two (inputOne, inputTwo) hone htwo hagrees]

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
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreBoundaryCloseRound A strategy hwin initialMemory one
        inputOne two inputTwo =
      other.ownerFibreBoundaryCloseRound A strategy hwin initialMemory one
        inputOne two inputTwo := by
  unfold ownerFibreBoundaryCloseRound
  rw [selection.ownerFibreBoundaryReceive?_congr_at A strategy hwin
    initialMemory other key one two (inputOne, inputTwo) hone htwo hagrees]

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
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreRound A strategy hwin initialMemory controls input
        graph =
      other.ownerFibreRound A strategy hwin initialMemory controls input
        graph := by
  cases graph with
  | right =>
      unfold ownerFibreRound
      rw [selection.ownerFibreBoundaryOpenRecvTwo_congr_at A strategy hwin
        initialMemory other key controls.2 input.2 controls.1 input.1 htwo hone
          hagrees]
  | left =>
      unfold ownerFibreRound
      rw [selection.ownerFibreBoundaryOpenRecvOne_congr_at A strategy hwin
        initialMemory other key controls.1 input.1 controls.2 input.2 hone htwo
          hagrees]
  | both =>
      exact selection.ownerFibreBoundaryCloseRound_congr_at A strategy hwin
        initialMemory other key controls.1 input.1 controls.2 input.2 hone htwo
          hagrees

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
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.ownerFibreRoundRecord A strategy hwin initialMemory controls
        input graph =
      other.ownerFibreRoundRecord A strategy hwin initialMemory controls input
        graph := by
  unfold ownerFibreRoundRecord
  rw [selection.ownerFibreRound_congr_at A strategy hwin initialMemory other
    key controls input graph hone htwo hagrees]

theorem ownerFibreBoundaryOpenRecvOne_atKey
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
      (Memory := Memory) A strategy key
      (selection.ownerFibreBoundaryOpenRecvOne A strategy hwin initialMemory
        one inputOne two inputTwo).1 := by
  cases hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin
      initialMemory one two (inputOne, inputTwo) with
  | none =>
      simpa [ownerFibreBoundaryOpenRecvOne, hreceive] using
        hone.noRecv (Memory := Memory) A strategy key one inputOne
  | some result =>
      have hall := selection.ownerFibreBoundaryReceive?_atKey A strategy hwin
        initialMemory key one two (inputOne, inputTwo) result hone htwo hreceive
      simpa [ownerFibreBoundaryOpenRecvOne, hreceive] using hall.1

theorem ownerFibreBoundaryOpenRecvTwo_atKey
    (key : RootKey A strategy)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
      (Memory := Memory) A strategy key
      (selection.ownerFibreBoundaryOpenRecvTwo A strategy hwin initialMemory
        two inputTwo one inputOne).1 := by
  cases hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin
      initialMemory one two (inputOne, inputTwo) with
  | none =>
      simpa [ownerFibreBoundaryOpenRecvTwo, hreceive] using
        htwo.noRecv (Memory := Memory) A strategy key two inputTwo
  | some result =>
      have hall := selection.ownerFibreBoundaryReceive?_atKey A strategy hwin
        initialMemory key one two (inputOne, inputTwo) result hone htwo hreceive
      simpa [ownerFibreBoundaryOpenRecvTwo, hreceive] using hall.2.2.1

theorem ownerFibreBoundaryCloseRound_atKey
    (key : RootKey A strategy)
    (one : OneControl (Memory := Memory) A strategy) (inputOne : In₁)
    (two : TwoControl (Memory := Memory) A strategy) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key one)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key two) :
    let result := selection.ownerFibreBoundaryCloseRound A strategy hwin
      initialMemory one inputOne two inputTwo
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1 ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.1.2 := by
  cases hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin
      initialMemory one two (inputOne, inputTwo) with
  | none =>
      exact ⟨by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using
            hone.noRecv (Memory := Memory) A strategy key one inputOne,
        by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using
            htwo.noRecv (Memory := Memory) A strategy key two inputTwo⟩
  | some result =>
      have hall := selection.ownerFibreBoundaryReceive?_atKey A strategy hwin
        initialMemory key one two (inputOne, inputTwo) result hone htwo hreceive
      exact ⟨by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using hall.2.1,
        by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using hall.2.2.2⟩

/-- Every physical round remains inside the initial root-key fibre. -/
theorem ownerFibreRound_atKey
    (key : RootKey A strategy)
    (controls : OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy)
    (input : In₁ × In₂) (graph : Graph)
    (hone :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key controls.1)
    (htwo :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key controls.2) :
    let result := selection.ownerFibreRound A strategy hwin initialMemory
      controls input graph
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
        (Memory := Memory) A strategy key result.1.1 ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
        (Memory := Memory) A strategy key result.1.2 := by
  cases graph with
  | right =>
      exact ⟨by
          simpa [ownerFibreRound] using
            hone.noRecv (Memory := Memory) A strategy key controls.1 input.1,
        by
          simpa [ownerFibreRound] using
            selection.ownerFibreBoundaryOpenRecvTwo_atKey A strategy hwin
              initialMemory key controls.2 input.2 controls.1 input.1 htwo hone⟩
  | left =>
      exact ⟨by
          simpa [ownerFibreRound] using
            selection.ownerFibreBoundaryOpenRecvOne_atKey A strategy hwin
              initialMemory key controls.1 input.1 controls.2 input.2 hone htwo,
        by
          simpa [ownerFibreRound] using
            htwo.noRecv (Memory := Memory) A strategy key controls.2 input.2⟩
  | both =>
      simpa [ownerFibreRound] using
        selection.ownerFibreBoundaryCloseRound_atKey A strategy hwin
          initialMemory key controls.1 input.1 controls.2 input.2 hone htwo

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
