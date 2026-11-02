/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreParity
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly

/-!
# Fixed-bank alignment of the owner-fibre relay

The recurrent endpoint controls store bank states in more places than their
two outer bank-coordinate registers.  A staged bridge retains both its
current state and a packet successor, while a pending owner-fibre state
retains the old and fresh banked receivers of its unresolved fork.  This file
tracks all of those occurrences.  Consequently, resolving an acknowledged
relay cannot silently select a state belonging to another rational policy.
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

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

/-! ## Every bank state stored by one endpoint -/

def ProfiledRawJointOneSidedPhysicalCompatibleBankControl.AtKey
    (key : RootKey A strategy) (state : BankControl A strategy hwin) : Prop :=
  state.1 = key

def ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget.AtKey
    (key : RootKey A strategy)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) : Prop :=
  packet.successor.1 = key

def ProfiledRawJointRecurrentRightToLeftBridgeAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin) :
    Prop :=
  match control with
  | .inl staged =>
      staged.1.AtKey A strategy hwin key ∧
        ∀ packet, staged.2.2 = some packet →
          packet.AtKey A strategy hwin key
  | .inr installed => installed.1.AtKey A strategy hwin key

def ProfiledRawJointRecurrentLeftToRightBridgeAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin) :
    Prop :=
  match control with
  | .inl staged =>
      staged.1.AtKey A strategy hwin key ∧
        ∀ packet, staged.2.2 = some packet →
          packet.AtKey A strategy hwin key
  | .inr installed => installed.1.AtKey A strategy hwin key

/-- Both meanings of the unresolved dormant-left receiver fork use `key`. -/
def ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin) :
    Prop :=
  control.2.1.2.openControl.1.AtKey A strategy hwin key ∧
    control.2.1.2.closedControl.1.AtKey A strategy hwin key

/-- Both meanings of the unresolved dormant-right receiver fork use `key`. -/
def ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin) :
    Prop :=
  control.2.1.2.openControl.1.AtKey A strategy hwin key ∧
    control.2.1.2.closedControl.1.AtKey A strategy hwin key

def ProfiledRawJointRecurrentOwnerFibreBoundaryOneBaseAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneBase A strategy hwin) :
    Prop :=
  match control with
  | .inl bridge =>
      ProfiledRawJointRecurrentLeftToRightBridgeAtKey A strategy hwin key
        bridge
  | .inr pending =>
      ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey A strategy hwin key
        pending

def ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBaseAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBase A strategy hwin) :
    Prop :=
  match control with
  | .inl bridge =>
      ProfiledRawJointRecurrentRightToLeftBridgeAtKey A strategy hwin key
        bridge
  | .inr pending =>
      ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey A strategy hwin key
        pending

/-- Every bank state stored by process one, including both outer registers. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneBaseAtKey A strategy hwin key
      control.1 ∧
    control.2.1.AtKey A strategy hwin key ∧
    control.2.2.AtKey A strategy hwin key

/-- Every bank state stored by process two, including both outer registers. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBaseAtKey A strategy hwin key
      control.1 ∧
    control.2.1.AtKey A strategy hwin key ∧
    control.2.2.AtKey A strategy hwin key

/-! ## Local preservation facts -/

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_atKey
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state target).AtKey A strategy hwin state.1 :=
  rfl

theorem ProfiledRawJointRecurrentRightToLeftBridgeAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentRightToLeftBridgeAtKey A strategy hwin key
        control)
    (input : In₂) :
    ProfiledRawJointRecurrentRightToLeftBridgeAtKey A strategy hwin key
      (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin
        control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      change state.AtKey A strategy hwin key ∧ _ at hkey
      cases packet with
      | none => exact hkey
      | some packet =>
          have hsuccessor := hkey.2 packet rfl
          dsimp [profiledRawJointRecurrentRightToLeftBridgeNoRecv]
          split
          · exact hkey
          · exact hsuccessor
  | inr installed =>
      exact hkey

theorem ProfiledRawJointRecurrentLeftToRightBridgeAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentLeftToRightBridgeAtKey A strategy hwin key
        control)
    (input : In₁) :
    ProfiledRawJointRecurrentLeftToRightBridgeAtKey A strategy hwin key
      (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin
        control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      change state.AtKey A strategy hwin key ∧ _ at hkey
      cases packet with
      | none => exact hkey
      | some packet =>
          have hsuccessor := hkey.2 packet rfl
          dsimp [profiledRawJointRecurrentLeftToRightBridgeNoRecv]
          split
          · exact hkey
          · exact hsuccessor
  | inr installed =>
      exact hkey

theorem ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey A strategy hwin key
        control)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey A strategy hwin key
      (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
        control input).1 := by
  exact hkey

theorem ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey A strategy hwin key
        control)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey A strategy hwin key
      (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
        control input).1 := by
  exact hkey

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        control)
    (input : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        control input).1 := by
  rcases control with ⟨base, coordinates⟩
  rcases hkey with ⟨hbase, hcoordinates⟩
  cases base with
  | inl bridge =>
      exact ⟨hbase.noRecv A strategy hwin key bridge input, hcoordinates⟩
  | inr pending =>
      exact ⟨hbase.noRecv A strategy hwin key pending input, hcoordinates⟩

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        control)
    (input : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        control input).1 := by
  rcases control with ⟨base, coordinates⟩
  rcases hkey with ⟨hbase, hcoordinates⟩
  cases base with
  | inl bridge =>
      exact ⟨hbase.noRecv A strategy hwin key bridge input, hcoordinates⟩
  | inr pending =>
      exact ⟨hbase.noRecv A strategy hwin key pending input, hcoordinates⟩

/-! ## Fresh boundary forks stay in one bank fibre -/

theorem
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork_atKey
    (key : RootKey A strategy)
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂)
    (hold : oldState.AtKey A strategy hwin key)
    (hpacket : packet.AtKey A strategy hwin key) :
    let fork :=
      (profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey A strategy hwin key
        fork.openControl ∧
      ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey A strategy hwin key
        fork.closedControl := by
  exact ⟨⟨hold, hpacket⟩, ⟨hold, hpacket⟩⟩

theorem
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork_atKey
    (key : RootKey A strategy)
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁)
    (hold : oldState.AtKey A strategy hwin key)
    (hpacket : packet.AtKey A strategy hwin key) :
    let fork :=
      (profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey A strategy hwin key
        fork.openControl ∧
      ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey A strategy hwin key
        fork.closedControl := by
  exact ⟨⟨hold, hpacket⟩, ⟨hold, hpacket⟩⟩

theorem profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo_atKey
    (key : RootKey A strategy)
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (hstate : state.AtKey A strategy hwin key) :
    let fork :=
      (profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo A strategy hwin
        state receiver owner input).1
    ProfiledRawJointRecurrentRightToLeftBridgeAtKey A strategy hwin key
        fork.openControl ∧
      ProfiledRawJointRecurrentRightToLeftBridgeAtKey A strategy hwin key
        fork.closedControl := by
  change state.1 = key at hstate
  simp only [profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo]
  split <;>
    simp [profiledRawJointRecurrentRightReceiveFor,
      ProfiledRawJointRecurrentRightToLeftBridgeAtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl.AtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget.AtKey,
      hstate]

theorem profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne_atKey
    (key : RootKey A strategy)
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hstate : state.AtKey A strategy hwin key) :
    let fork :=
      (profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne A strategy hwin
        state receiver owner input).1
    ProfiledRawJointRecurrentLeftToRightBridgeAtKey A strategy hwin key
        fork.openControl ∧
      ProfiledRawJointRecurrentLeftToRightBridgeAtKey A strategy hwin key
        fork.closedControl := by
  change state.1 = key at hstate
  simp only [profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne]
  split <;>
    simp [profiledRawJointRecurrentLeftReceiveFor,
      ProfiledRawJointRecurrentLeftToRightBridgeAtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl.AtKey,
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget.AtKey,
      hstate]

/-! ## The bank data decoded for a boundary -/

def ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.AtKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) :
    Prop :=
  data.1.1.AtKey A strategy hwin key ∧
    data.2.1.AtKey A strategy hwin key

def ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.AtKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) :
    Prop :=
  data.1.1.AtKey A strategy hwin key ∧
    data.2.1.AtKey A strategy hwin key

theorem ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey.receiver
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreAtKey A strategy hwin key
        control) :
    (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy hwin
      control).1.AtKey A strategy hwin key := by
  by_cases hmember : control.1
  · simpa [profiledRawJointRecurrentRightToLeftOwnerFibreReceiver, hmember]
      using hkey.2
  · simpa [profiledRawJointRecurrentRightToLeftOwnerFibreReceiver, hmember]
      using hkey.1

theorem ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey.receiver
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (hkey :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreAtKey A strategy hwin key
        control) :
    (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy hwin
      control).1.AtKey A strategy hwin key := by
  by_cases hmember : control.1
  · simpa [profiledRawJointRecurrentLeftToRightOwnerFibreReceiver, hmember]
      using hkey.2
  · simpa [profiledRawJointRecurrentLeftToRightOwnerFibreReceiver, hmember]
      using hkey.1

/-- Any successfully decoded right boundary uses two states from the fixed
bank fibre.  This includes the fibre/fibre shapes, where either member of
each dormant receiver fork may be selected. -/
theorem profiledRawJointRecurrentOwnerFibreRightBoundaryData?_atKey
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        one two = some data) :
    data.AtKey A strategy hwin key := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  rcases hone with ⟨honeBase, honeRight, honeLeft⟩
  rcases htwo with ⟨htwoBase, htwoRight, htwoLeft⟩
  cases oneBase with
  | inl oneBridge =>
      cases oneBridge with
      | inl oneStaged =>
          cases twoBase with
          | inl twoBridge =>
              cases twoBridge with
              | inl twoStaged =>
                  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                    at hdecode
              | inr twoInstalled =>
                  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                    at hdecode
          | inr twoPending =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                at hdecode
      | inr oneInstalled =>
          cases twoBase with
          | inl twoBridge =>
              cases twoBridge with
              | inl twoStaged =>
                  obtain ⟨rightState, rightReceiver, rightOwner,
                    leftTemplate, packet, leftMove, hinstalled, hstaged,
                    hmove, hdata⟩ :=
                    profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged_inv
                      A strategy hwin oneInstalled twoStaged oneCoordinates
                        twoCoordinates data hdecode
                  subst oneInstalled
                  subst twoStaged
                  subst data
                  exact ⟨honeBase, htwoBase.2 packet rfl⟩
              | inr twoInstalled =>
                  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                    at hdecode
          | inr twoPending =>
              obtain ⟨rightOwner, leftTemplate, hinstalled, hdata⟩ :=
                profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
                  A strategy hwin oneInstalled twoPending oneCoordinates
                    twoCoordinates data hdecode
              subst oneInstalled
              subst data
              exact ⟨honeBase, honeLeft⟩
  | inr onePending =>
      cases twoBase with
      | inl twoBridge =>
          cases twoBridge with
          | inl twoStaged =>
              rcases twoStaged with ⟨stagedState, receiver, packet⟩
              change stagedState.AtKey A strategy hwin key ∧ _ at htwoBase
              cases packet with
              | none =>
                  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                    at hdecode
              | some packet =>
                  have hpacket := htwoBase.2 packet rfl
                  cases hmove : packet.successor.2.1.2.2 with
                  | none =>
                      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                        hmove] at hdecode
                  | some move =>
                      apply
                        profiledRawJointRecurrentOwnerFibreMakeRight?_indices A
                          strategy hwin key stagedState
                            (profiledRawJointRightOwnerFibreExceptional A
                              onePending.2.1.1)
                            (onePending.2.1.1.receiverAt A receiver)
                            packet.successor
                            ⟨move,
                              (move.memberController A false).initial⟩
                            (initialProfiledRawJointLeftPhysicalSiblingReceiver
                              A move .first) data htwoBase.1 hpacket
                      simpa [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                        hmove] using hdecode
          | inr twoInstalled =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                at hdecode
      | inr twoPending =>
          have hright := htwoBase.receiver A strategy hwin key twoPending
          have hleft := honeBase.receiver A strategy hwin key onePending
          simp only [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
            at hdecode
          split at hdecode
          · apply
              profiledRawJointRecurrentOwnerFibreMakeRight?_indices A strategy
                hwin key
                  (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A
                    strategy hwin twoPending).1
                  (profiledRawJointRightOwnerFibreExceptional A
                    onePending.2.1.1)
                  (onePending.2.1.1.receiverAt A
                    (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A
                      strategy hwin twoPending).2)
                  (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A
                    strategy hwin onePending).1
                  (profiledRawJointLeftOwnerFibreExceptional A
                    twoPending.2.1.1)
                  (twoPending.2.1.1.receiverAt A
                    (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A
                      strategy hwin onePending).2)
                  data hright hleft hdecode
          · simp at hdecode

/-- Mirrored decoder theorem for a successfully decoded left boundary. -/
theorem profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_atKey
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hdecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        one two = some data) :
    data.AtKey A strategy hwin key := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  rcases hone with ⟨honeBase, honeRight, honeLeft⟩
  rcases htwo with ⟨htwoBase, htwoRight, htwoLeft⟩
  cases oneBase with
  | inl oneBridge =>
      cases oneBridge with
      | inl oneStaged =>
          cases twoBase with
          | inl twoBridge =>
              cases twoBridge with
              | inl twoStaged =>
                  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                    at hdecode
              | inr twoInstalled =>
                  obtain ⟨leftState, leftReceiver, leftOwner,
                    rightTemplate, packet, rightMove, hstaged, hinstalled,
                    hmove, hdata⟩ :=
                    profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled_inv
                      A strategy hwin oneStaged twoInstalled oneCoordinates
                        twoCoordinates data hdecode
                  subst oneStaged
                  subst twoInstalled
                  subst data
                  exact ⟨htwoBase, honeBase.2 packet rfl⟩
          | inr twoPending =>
              rcases oneStaged with ⟨stagedState, receiver, packet⟩
              change stagedState.AtKey A strategy hwin key ∧ _ at honeBase
              cases hmember : twoPending.1 with
              | false =>
                  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                    hmember] at hdecode
              | true =>
                  cases packet with
                  | none =>
                      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                        hmember] at hdecode
                  | some packet =>
                      have hpacket := honeBase.2 packet rfl
                      cases hmove : packet.successor.2.1.2.1 with
                      | none =>
                          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                            hmember, hmove] at hdecode
                      | some move =>
                          apply
                            profiledRawJointRecurrentOwnerFibreMakeLeft?_indices
                              A strategy hwin key stagedState
                                (profiledRawJointLeftOwnerFibreExceptional A
                                  twoPending.2.1.1)
                                (twoPending.2.1.1.receiverAt A receiver)
                                packet.successor
                                ⟨move,
                                  (move.memberController A false).initial⟩
                                (initialProfiledRawJointRightPhysicalSiblingReceiver
                                  A move .first) data honeBase.1 hpacket
                          simpa [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                            hmember, hmove] using hdecode
      | inr oneInstalled =>
          cases twoBase with
          | inl twoBridge =>
              cases twoBridge <;>
                simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                  at hdecode
          | inr twoPending =>
              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                at hdecode
  | inr onePending =>
      cases twoBase with
      | inl twoBridge =>
          cases twoBridge with
          | inl twoStaged =>
              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                at hdecode
          | inr twoInstalled =>
              obtain ⟨leftOwner, rightTemplate, hinstalled, hdata⟩ :=
                profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
                  A strategy hwin onePending twoInstalled oneCoordinates
                    twoCoordinates data hdecode
              subst twoInstalled
              subst data
              exact ⟨htwoBase, htwoRight⟩
      | inr twoPending =>
          have hleft := honeBase.receiver A strategy hwin key onePending
          have hright := htwoBase.receiver A strategy hwin key twoPending
          simp only [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
            at hdecode
          split at hdecode
          · apply
              profiledRawJointRecurrentOwnerFibreMakeLeft?_indices A strategy
                hwin key
                  (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A
                    strategy hwin onePending).1
                  (profiledRawJointLeftOwnerFibreExceptional A
                    twoPending.2.1.1)
                  (twoPending.2.1.1.receiverAt A
                    (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A
                      strategy hwin onePending).2)
                  (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A
                    strategy hwin twoPending).1
                  (profiledRawJointRightOwnerFibreExceptional A
                    onePending.2.1.1)
                  (onePending.2.1.1.receiverAt A
                    (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A
                      strategy hwin twoPending).2)
                  data hleft hright hdecode
          · simp at hdecode

theorem ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive_atKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hkey : data.AtKey A strategy hwin key)
    (input : In₁ × In₂) :
    let result := data.ownerFibreReceive A strategy hwin input
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1.closedControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.2.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.2.1.closedControl := by
  rcases data with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases hkey with ⟨hstate, hold⟩
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state
        ((
          ((receiver.1.memberController A false).labelOf owner).2
            receiver.2.2.1 (input.2, input.1)).target receiver.2.1)
  have hpacket : packet.AtKey A strategy hwin key := by
    change state.1 = key
    exact hstate
  have hphase :=
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork_atKey A
      strategy hwin key ⟨receiver.1, owner⟩ oldState oldReceiver oldOwner
        packet input hold hpacket
  have hbridge :=
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo_atKey A strategy
      hwin key state receiver owner (input.2, input.1) hstate
  rcases hphase with ⟨hphaseOpen, hphaseClosed⟩
  rcases hbridge with ⟨hbridgeOpen, hbridgeClosed⟩
  exact ⟨⟨hphaseOpen, hstate, hold⟩,
    ⟨hphaseClosed, hstate, hpacket⟩,
    ⟨hbridgeOpen, hstate, hpacket⟩,
    ⟨hbridgeClosed, hstate, hpacket⟩⟩

theorem ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive_atKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hkey : data.AtKey A strategy hwin key)
    (input : In₁ × In₂) :
    let result := data.ownerFibreReceive A strategy hwin input
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1.closedControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.2.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.2.1.closedControl := by
  rcases data with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases hkey with ⟨hstate, hold⟩
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin state
        ((((receiver.1.memberController A false).labelOf owner).2
          receiver.2.2.1 input).target receiver.2.1)
  have hpacket : packet.AtKey A strategy hwin key := by
    change state.1 = key
    exact hstate
  have hphase :=
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork_atKey A
      strategy hwin key ⟨receiver.1, owner⟩ oldState oldReceiver oldOwner
        packet (input.2, input.1) hold hpacket
  have hbridge :=
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne_atKey A strategy
      hwin key state receiver owner input hstate
  rcases hphase with ⟨hphaseOpen, hphaseClosed⟩
  rcases hbridge with ⟨hbridgeOpen, hbridgeClosed⟩
  exact ⟨⟨hbridgeOpen, hpacket, hstate⟩,
    ⟨hbridgeClosed, hpacket, hstate⟩,
    ⟨hphaseOpen, hold, hstate⟩,
    ⟨hphaseClosed, hpacket, hstate⟩⟩

/-! ## Total receive maps -/

theorem profiledRawJointRecurrentOwnerFibreBoundaryReceive?_atKey
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (input : In₁ × In₂)
    (result :
      (FiniteDelayedFork
          (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy
            hwin) × Out₁) ×
        (FiniteDelayedFork
          (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy
            hwin) × Out₂))
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one
        two input = some result) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1.closedControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.2.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.2.1.closedControl := by
  cases hright :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        one two with
  | some data =>
      have hdata :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_atKey A strategy
          hwin key one two data hone htwo hright
      have hresult := data.ownerFibreReceive_atKey A strategy hwin key hdata
        input
      rw [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright] at hreceive
      cases Option.some.inj hreceive
      exact hresult
  | none =>
      cases hleft :
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
            one two with
      | some data =>
          have hdata :=
            profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_atKey A
              strategy hwin key one two data hone htwo hleft
          have hresult := data.ownerFibreReceive_atKey A strategy hwin key
            hdata input
          rw [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
            hleft] at hreceive
          cases Option.some.inj hreceive
          exact hresult
      | none =>
          simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
            hleft] at hreceive

theorem profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne_atKey
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one inputOne two inputTwo).1 := by
  cases hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one
        two (inputOne, inputTwo) with
  | none =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
        hreceive] using hone.noRecv A strategy hwin key one inputOne
  | some result =>
      have hall :=
        profiledRawJointRecurrentOwnerFibreBoundaryReceive?_atKey A strategy
          hwin key one two (inputOne, inputTwo) result hone htwo hreceive
      simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
        hreceive] using hall.1

theorem profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo_atKey
    (key : RootKey A strategy)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two inputTwo one inputOne).1 := by
  cases hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one
        two (inputOne, inputTwo) with
  | none =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
        hreceive] using htwo.noRecv A strategy hwin key two inputTwo
  | some result =>
      have hall :=
        profiledRawJointRecurrentOwnerFibreBoundaryReceive?_atKey A strategy
          hwin key one two (inputOne, inputTwo) result hone htwo hreceive
      simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
        hreceive] using hall.2.2.1

theorem profiledRawJointRecurrentOwnerFibreBoundaryClose_atKey
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two) :
    let result :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        inputOne two inputTwo
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1 ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.2 := by
  cases hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one
        two (inputOne, inputTwo) with
  | none =>
      exact ⟨by
          simpa [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
            using hone.noRecv A strategy hwin key one inputOne,
        by
          simpa [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
            using htwo.noRecv A strategy hwin key two inputTwo⟩
  | some result =>
      have hall :=
        profiledRawJointRecurrentOwnerFibreBoundaryReceive?_atKey A strategy
          hwin key one two (inputOne, inputTwo) result hone htwo hreceive
      exact ⟨by
          simpa [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
            using hall.2.1,
        by
          simpa [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
            using hall.2.2.2⟩

/-! ## Exact-closing forks and the acknowledged relay trace -/

theorem profiledRawJointRecurrentOwnerFibreExactClosingRecvForkOne_atKey
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      one inputOne two inputTwo
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        fork.1.closedControl := by
  exact ⟨
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne_atKey A strategy
      hwin key one inputOne two inputTwo hone htwo,
    (profiledRawJointRecurrentOwnerFibreBoundaryClose_atKey A strategy hwin
      key one inputOne two inputTwo hone htwo).1⟩

theorem profiledRawJointRecurrentOwnerFibreExactClosingRecvForkTwo_atKey
    (key : RootKey A strategy)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      two inputTwo one inputOne
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        fork.1.closedControl := by
  exact ⟨
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo_atKey A strategy
      hwin key two inputTwo one inputOne htwo hone,
    (profiledRawJointRecurrentOwnerFibreBoundaryClose_atKey A strategy hwin
      key one inputOne two inputTwo hone htwo).2⟩

private abbrev OneRelay :=
  FiniteAcknowledgedDelayedCarrier (Fin 5)
    (ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)

private abbrev TwoRelay :=
  FiniteAcknowledgedDelayedCarrier (Fin 5)
    (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)

/-- Every meaning still represented by either endpoint relay lies in the
same bank fibre.  This is stronger than a statement about only the mutually
selected controls. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey
    (key : RootKey A strategy)
    (one : OneRelay A strategy hwin) (two : TwoRelay A strategy hwin) : Prop :=
  FiniteAcknowledgedDelayedCarrier.CarrierAll
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key)
      one ∧
    FiniteAcknowledgedDelayedCarrier.CarrierAll
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key)
      two

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey.advance
    (key : RootKey A strategy)
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (one : OneRelay A strategy hwin) (two : TwoRelay A strategy hwin)
    (hall :
      ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey A strategy hwin
        key one two)
    (round : EnvironmentRound In₁ In₂) :
    let controller :=
      profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo
    let next := controller.semanticAdvanceControls (one, two) round
    ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey A strategy hwin key
      next.1 next.2 := by
  let OneAtKey :=
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
  let TwoAtKey :=
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
  have hone := hall.1
  have htwo := hall.2
  have hactualOne : OneAtKey
      (FiniteAcknowledgedDelayedCarrier.resolvedControl one two) :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_resolvedControl OneAtKey one
      two hone
  have hactualTwo : TwoAtKey
      (FiniteAcknowledgedDelayedCarrier.resolvedControl two one) :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_resolvedControl TwoAtKey two
      one htwo
  have hnoRecvOne :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_noRecvMealy OneAtKey
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
      one round.inputOne
      (fun control hcontrol ↦ hcontrol.noRecv A strategy hwin key control
        round.inputOne) hone
  have hnoRecvTwo :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_noRecvMealy TwoAtKey
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
      two round.inputTwo
      (fun control hcontrol ↦ hcontrol.noRecv A strategy hwin key control
        round.inputTwo) htwo
  cases hgraph : round.graph with
  | right =>
      have hrecvTwo :=
        FiniteAcknowledgedDelayedCarrier.carrierAll_recvReforkMealy TwoAtKey
          (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
            (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
              hwin)
            (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin))
          two round.inputTwo one round.inputOne
          (profiledRawJointRecurrentOwnerFibreExactClosingRecvForkTwo_atKey A
            strategy hwin key
              (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
              round.inputTwo
              (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
              round.inputOne hactualTwo hactualOne)
      simpa [FinitePairedMealyController.semanticAdvanceControls,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey, OneAtKey,
        TwoAtKey, hgraph] using And.intro hnoRecvOne hrecvTwo
  | left =>
      have hrecvOne :=
        FiniteAcknowledgedDelayedCarrier.carrierAll_recvReforkMealy OneAtKey
          (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
            (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
              hwin)
            (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin))
          one round.inputOne two round.inputTwo
          (profiledRawJointRecurrentOwnerFibreExactClosingRecvForkOne_atKey A
            strategy hwin key
              (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
              round.inputOne
              (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
              round.inputTwo hactualOne hactualTwo)
      simpa [FinitePairedMealyController.semanticAdvanceControls,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey, OneAtKey,
        TwoAtKey, hgraph] using And.intro hrecvOne hnoRecvTwo
  | both =>
      have hrecvOne :=
        FiniteAcknowledgedDelayedCarrier.carrierAll_recvReforkMealy OneAtKey
          (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
            (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
              hwin)
            (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin))
          one round.inputOne two round.inputTwo
          (profiledRawJointRecurrentOwnerFibreExactClosingRecvForkOne_atKey A
            strategy hwin key
              (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
              round.inputOne
              (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
              round.inputTwo hactualOne hactualTwo)
      have hrecvTwo :=
        FiniteAcknowledgedDelayedCarrier.carrierAll_recvReforkMealy TwoAtKey
          (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
            (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
              hwin)
            (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin))
          two round.inputTwo one round.inputOne
          (profiledRawJointRecurrentOwnerFibreExactClosingRecvForkTwo_atKey A
            strategy hwin key
              (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
              round.inputTwo
              (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
              round.inputOne hactualTwo hactualOne)
      simpa [FinitePairedMealyController.semanticAdvanceControls,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey, OneAtKey,
        TwoAtKey, hgraph] using And.intro hrecvOne hrecvTwo

/-- All bank-state occurrences in the actual acknowledged relay trace retain
the initial key at every finite prefix. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticControlTrace_atKey
    (key : RootKey A strategy)
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        initialOne)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let controls :=
      (profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo).semanticControlTrace env n
    ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey A strategy hwin key
      controls.1 controls.2 := by
  induction n with
  | zero =>
      simpa [FinitePairedMealyController.semanticControlTrace,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey] using
          And.intro hone htwo
  | succ n ih =>
      simpa only [FinitePairedMealyController.semanticControlTrace] using
        (ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysAtKey.advance A
          strategy hwin key initialOne initialTwo
            ((profiledRawJointRecurrentOwnerFibreBoundaryController A strategy
              hwin initialOne initialTwo).semanticControlTrace env n).1
            ((profiledRawJointRecurrentOwnerFibreBoundaryController A strategy
              hwin initialOne initialTwo).semanticControlTrace env n).2
            ih (env n))

/-! ## Canonical recurrent entries -/

theorem profiledRawJointRecurrentOwnerFibreRightEntry_atKey
    (key : RootKey A strategy)
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hstate : rightState.AtKey A strategy hwin key)
    (hpacket : packet.AtKey A strategy hwin key) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
          rightState rightReceiver rightOwner leftTemplate packet) ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
          rightState rightReceiver packet) := by
  exact ⟨⟨hstate, hstate, hpacket⟩,
    ⟨⟨hstate, by
        intro candidate hc
        cases Option.some.inj hc
        exact hpacket⟩,
      hstate, hpacket⟩⟩

theorem profiledRawJointRecurrentOwnerFibreLeftEntry_atKey
    (key : RootKey A strategy)
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hstate : leftState.AtKey A strategy hwin key)
    (hpacket : packet.AtKey A strategy hwin key) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
          leftState leftReceiver packet) ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
          leftState leftReceiver leftOwner rightTemplate packet) := by
  exact ⟨
    ⟨⟨hstate, by
        intro candidate hc
        cases Option.some.inj hc
        exact hpacket⟩,
      hpacket, hstate⟩,
    ⟨hstate, hpacket, hstate⟩⟩

/-! ## Exact resolver observations at selected receives -/

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)

/-- A staged packet is an exact edge out of its retained source state.  This
is stronger than fixed-key alignment: it rules out a packet whose successor
happens to lie in the same bank but was resolved from an unrelated state. -/
structure
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget.ExactFrom
    (source : BankControl A strategy hwin)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) : Prop where
  source_reachable :
    ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
      source
  resolved :
    packet =
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin source packet.target
  realizes :
    ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
      hwin source packet.target packet.childCode

namespace
  ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget.ExactFrom

theorem child_exact
    (source : BankControl A strategy hwin)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin source) :
    packet.childCode.1 = packet.target := by
  rcases hexact.realizes with
    ⟨move, semanticSource, actual, hcode, hmove, hcompatible, hchildren,
      hchildCode, hbare, hsuccessor⟩
  exact hbare

theorem successor_eq
    (source : BankControl A strategy hwin)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin source) :
    packet.successor =
      profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        source packet.childCode := by
  rw [hexact.resolved]
  rfl

theorem successor_key
    (source : BankControl A strategy hwin)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin source) :
    packet.successor.1 = source.1 := by
  rw [hexact.successor_eq A strategy hwin source packet]
  rfl

theorem successor_reachable
    (source : BankControl A strategy hwin)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin source) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
      packet.successor := by
  rw [hexact.successor_eq A strategy hwin source packet]
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankSuccessor_reachable A
      strategy hwin source hexact.source_reachable packet.childCode

end ExactFrom
end ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget

/-- Two outer coordinates are adjacent in the fixed policy, with either the
right state or the left state as the exact parent.  Both orientations are
needed because successive resolver calls alternate physical side. -/
def ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact
    (coordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin) :
    Prop :=
  (∃ packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin,
    packet.ExactFrom A strategy hwin coordinates.1 ∧
      coordinates.2 = packet.successor) ∨
  (∃ packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin,
    packet.ExactFrom A strategy hwin coordinates.2 ∧
      coordinates.1 = packet.successor)

/-- Exact classification of a change of active bank parent.  Besides a
stationary step, the new parent is either a successor of the old parent in
the one fixed bank policy, or the old parent is a successor of the new one.
The last disjunct is a literal rollback certificate; it is deliberately not
identified with forward policy progress. -/
def ProfiledRawJointRecurrentBankParentStep
    (current next : BankControl A strategy hwin) : Prop :=
  current = next ∨
    (∃ packet :
        ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin,
      packet.ExactFrom A strategy hwin current ∧
        next = packet.successor) ∨
    (∃ packet :
        ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A
          strategy hwin,
      packet.ExactFrom A strategy hwin next ∧
        current = packet.successor)

/-- Every exact parent step stays inside one bank key. -/
theorem ProfiledRawJointRecurrentBankParentStep.index_eq
    (current next : BankControl A strategy hwin)
    (hstep :
      ProfiledRawJointRecurrentBankParentStep A strategy hwin current next) :
    next.1 = current.1 := by
  rcases hstep with hneutral | hforward | hrollback
  · exact congrArg Sigma.fst hneutral.symm
  · rcases hforward with ⟨packet, hexact, hnext⟩
    rw [hnext, hexact.successor_key A strategy hwin current packet]
  · rcases hrollback with ⟨packet, hexact, hcurrent⟩
    rw [hcurrent, hexact.successor_key A strategy hwin next packet]

/-- A sufficient parity strengthening at one recurrent bank entry.  It asks
the parent-linked DPA to accept every reachable infinite walk generated by
the projected neutral/forward/rollback relation, from the DPA state stored at
the entry.  Unlike ordinary `BankPath` acceptance, this condition includes
reverse crossings.  The projection can contain walks that no full pair of
owner-fibre controls realizes, so this is an intentionally strong interface,
not yet the certificate whose existence follows from `hwin`. -/
def ProfiledRawJointRecurrentBankRollbackSafeFrom
    (initial : BankControl A strategy hwin) : Prop :=
  ∀ parent : Nat → BankControl A strategy hwin,
    parent 0 = initial →
      (∀ n : Nat,
        ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy
          hwin (parent n)) →
      (∀ n : Nat,
        ProfiledRawJointRecurrentBankParentStep A strategy hwin (parent n)
          (parent (n + 1))) →
      (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
          (profiledRawJointOneSidedCodeParityDPA A initial.1.1.1)).AcceptsFrom
        initial.2.2 (fun n ↦ (parent (n + 1)).2.1)

/-- Product state used to check rollback safety on a finite graph.  The first
coordinate is the active bank parent; the second is the actual DPA state
obtained while reading the possibly backward-moving parent word.  These two
states cannot be identified on a rollback. -/
abbrev ProfiledRawJointRecurrentBankRollbackMonitorState
    (initial : BankControl A strategy hwin) :=
  BankControl A strategy hwin ×
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A initial.1.1.1)).State

/-- The complete finite product graph of the projected rollback relation.
Its edges combine a reachable exact parent move with the actual DPA update on
the new parent's linked code.  Forgetting the full owner-fibre control pair
makes this a finite overapproximation of concrete executions. -/
noncomputable def ProfiledRawJointRecurrentBankRollbackMonitorEdges
    (initial : BankControl A strategy hwin) :
    Finset
      (ProfiledRawJointRecurrentBankRollbackMonitorState A strategy hwin
          initial ×
        ProfiledRawJointRecurrentBankRollbackMonitorState A strategy hwin
          initial) := by
  classical
  let D :=
    sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A initial.1.1.1)
  exact Finset.univ.filter (fun edge ↦
    edge.1.1.1 = initial.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        edge.1.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        edge.2.1 ∧
      ProfiledRawJointRecurrentBankParentStep A strategy hwin edge.1.1
        edge.2.1 ∧
      edge.2.2 = D.step edge.1.2 edge.2.1.2.1)

/-- Finite-graph sufficient condition for rollback safety.  Every path from
the concrete entry in the projected rollback-monitor graph has even minimum
recurrent DPA priority.  Since the graph is a `Finset`, an SCC or
progress-measure checker can decide this condition; a later construction may
instead certify the smaller graph of fully realizable owner-fibre states. -/
def ProfiledRawJointRecurrentBankRollbackMonitorAccepting
    (initial : BankControl A strategy hwin) : Prop :=
  let D :=
    sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A initial.1.1.1)
  ∀ walk : Nat →
      ProfiledRawJointRecurrentBankRollbackMonitorState A strategy hwin
        initial,
    walk 0 = (initial, initial.2.2) →
      (∀ n : Nat,
        (walk n, walk (n + 1)) ∈
          ProfiledRawJointRecurrentBankRollbackMonitorEdges A strategy hwin
            initial) →
      ∃ p : Nat,
        NatEven p ∧
          (∀ n : Nat, ∃ k : Nat,
            n ≤ k ∧ D.priority (walk k).2 = p) ∧
          ∀ q : Nat,
            (∀ n : Nat, ∃ k : Nat,
              n ≤ k ∧ D.priority (walk k).2 = q) →
            p ≤ q

/-- The finite rollback-monitor certificate implies the semantic universal
rollback-safety contract.  The auxiliary monitor coordinate is the literal
DPA run on the parent-code word; the exact-parent-step theorem keeps every
bank coordinate at the initial key. -/
theorem profiledRawJointRecurrentBankRollbackSafeFrom_of_monitorAccepting
    (initial : BankControl A strategy hwin)
    (haccepting :
      ProfiledRawJointRecurrentBankRollbackMonitorAccepting A strategy hwin
        initial) :
    ProfiledRawJointRecurrentBankRollbackSafeFrom A strategy hwin initial := by
  intro parent hzero hreachable hstep
  let D :=
    sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A initial.1.1.1)
  let word : OmegaWord _ := fun n ↦ (parent (n + 1)).2.1
  let walk : Nat →
      ProfiledRawJointRecurrentBankRollbackMonitorState A strategy hwin
        initial :=
    fun n ↦ (parent n, D.runFrom initial.2.2 word n)
  have hkey : ∀ n : Nat, (parent n).1 = initial.1 := by
    intro n
    induction n with
    | zero => exact congrArg Sigma.fst hzero
    | succ n ih =>
        exact
          (ProfiledRawJointRecurrentBankParentStep.index_eq A strategy hwin
            (parent n) (parent (n + 1)) (hstep n)).trans ih
  have hwalkZero : walk 0 = (initial, initial.2.2) := by
    simp [walk, D, word, hzero, DetParityAutomaton.runFrom]
  have hwalkEdge : ∀ n : Nat,
      (walk n, walk (n + 1)) ∈
        ProfiledRawJointRecurrentBankRollbackMonitorEdges A strategy hwin
          initial := by
    intro n
    simp only [ProfiledRawJointRecurrentBankRollbackMonitorEdges,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hkey n, hreachable n, hreachable (n + 1), hstep n, ?_⟩
    rfl
  unfold ProfiledRawJointRecurrentBankRollbackMonitorAccepting at haccepting
  obtain ⟨p, hpEven, hpInf, hpMin⟩ :=
    haccepting walk hwalkZero hwalkEdge
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    obtain ⟨k, hnk, hk⟩ := hpInf n
    refine ⟨k, hnk, ?_⟩
    simpa only [walk] using hk
  · intro q hq
    apply hpMin q
    intro n
    obtain ⟨k, hnk, hk⟩ := hq n
    refine ⟨k, hnk, ?_⟩
    simpa only [walk] using hk

/-! ## Exactness of packets retained for a delayed reversal -/

/-- The dormant receiver fork in a right-to-left pending control retains the
successor of an exact edge from `source`.  The source is stored by the outer
boundary coordinate; the fork's open branch is instead the old dormant left
state and need not equal `source`. -/
def ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom
    (source : BankControl A strategy hwin)
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin) :
    Prop :=
  ∃ packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin,
    packet.ExactFrom A strategy hwin source ∧
      control.2.1.2.closedControl.1 = packet.successor

/-- Mirrored exact-edge certificate for a left-to-right pending control. -/
def ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom
    (source : BankControl A strategy hwin)
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin) :
    Prop :=
  ∃ packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin,
    packet.ExactFrom A strategy hwin source ∧
      control.2.1.2.closedControl.1 = packet.successor

/-- An exact packet boundary creates the same retained exact edge in both
member-labelled right-to-left candidates. -/
theorem
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork_edgeExact
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (source : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂)
    (hexact : packet.ExactFrom A strategy hwin source) :
    let fork :=
      (profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom A strategy
        hwin source fork.openControl ∧
      ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom A strategy
        hwin source fork.closedControl := by
  exact ⟨⟨packet, hexact, rfl⟩, ⟨packet, hexact, rfl⟩⟩

/-- Mirrored exact packet-boundary certificate. -/
theorem
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork_edgeExact
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (source : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁)
    (hexact : packet.ExactFrom A strategy hwin source) :
    let fork :=
      (profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom A strategy
        hwin source fork.openControl ∧
      ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom A strategy
        hwin source fork.closedControl := by
  exact ⟨⟨packet, hexact, rfl⟩, ⟨packet, hexact, rfl⟩⟩

/-- Any packet retained by a right-to-left staged receiver was resolved from
the source bank state stored beside that receiver. -/
def ProfiledRawJointRecurrentRightToLeftBridgePacketExact
    (control :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin) :
    Prop :=
  match control with
  | .inl staged =>
      ∀ packet, staged.2.2 = some packet →
        packet.ExactFrom A strategy hwin staged.1
  | .inr _ => True

/-- Mirrored exactness predicate for left-to-right staged packets. -/
def ProfiledRawJointRecurrentLeftToRightBridgePacketExact
    (control :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin) :
    Prop :=
  match control with
  | .inl staged =>
      ∀ packet, staged.2.2 = some packet →
        packet.ExactFrom A strategy hwin staged.1
  | .inr _ => True

/-- Packet exactness for the only packet-bearing summand of process one. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :
    Prop :=
  match control.1 with
  | .inl bridge =>
      ProfiledRawJointRecurrentLeftToRightBridgePacketExact A strategy hwin
        bridge
  | .inr _ => True

/-- Packet exactness for the only packet-bearing summand of process two. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  match control.1 with
  | .inl bridge =>
      ProfiledRawJointRecurrentRightToLeftBridgePacketExact A strategy hwin
        bridge
  | .inr _ => True

/-- Every delayed object stored by process one has exact policy provenance:
an explicit bridge carries an exact packet, while an owner fibre carries an
exact open-to-closed edge. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :
    Prop :=
  match control.1 with
  | .inl bridge =>
      ProfiledRawJointRecurrentLeftToRightBridgePacketExact A strategy hwin
        bridge
  | .inr pending =>
      ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom A strategy
        hwin control.2.1 pending

/-- Process-two mirror of `BoundaryOneDeferredExact`. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  match control.1 with
  | .inl bridge =>
      ProfiledRawJointRecurrentRightToLeftBridgePacketExact A strategy hwin
        bridge
  | .inr pending =>
      ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom A strategy
        hwin control.2.2 pending

/-- Complete delayed-edge provenance for one selected underlying control
pair. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy hwin
      one ∧
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
      hwin two

/-- Process one's two outer bank coordinates retain their semantic meaning.
A staged left receiver is anchored at the left coordinate and records its
successor in the right coordinate; an installed right owner is at the right
coordinate; a pending dormant-left fibre selects the left coordinate. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :
    Prop :=
  match control.1 with
  | .inl (.inl staged) =>
      control.2.2 = staged.1 ∧
        ∀ packet, staged.2.2 = some packet →
          control.2.1 = packet.successor
  | .inl (.inr installed) => control.2.1 = installed.1
  | .inr pending =>
      control.2.2 =
        (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy
          hwin pending).1

/-- Mirrored coordinate semantics for process two. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  match control.1 with
  | .inl (.inl staged) =>
      control.2.1 = staged.1 ∧
        ∀ packet, staged.2.2 = some packet →
          control.2.2 = packet.successor
  | .inl (.inr installed) => control.2.2 = installed.1
  | .inr pending =>
      control.2.1 =
        (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy
          hwin pending).1

def ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A strategy
      hwin one ∧
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A strategy
      hwin two

/-- Both local copies of the right/left bank-coordinate pair are genuine
policy edges.  The two copies need not be equal: a strict round can update
only the receiving endpoint. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      one.2 ∧
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      two.2

/-- When both endpoints are unresolved fibres, the decoder mixes the first
coordinate of process two with the second coordinate of process one.  One
coordinate equality is exactly what makes that mixed pair coincide with one
of the two certified local edges.  No cross-endpoint equality is imposed in
the other six decoder shapes. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  match one.1, two.1 with
  | .inr _, .inr _ =>
      one.2.1 = two.2.1 ∨ one.2.2 = two.2.2
  | _, _ => True

theorem ProfiledRawJointRecurrentRightToLeftBridgePacketExact.noRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentRightToLeftBridgePacketExact A strategy hwin
        control)
    (input : In₂) :
    ProfiledRawJointRecurrentRightToLeftBridgePacketExact A strategy hwin
      (profiledRawJointRecurrentRightToLeftBridgeNoRecv A strategy hwin
        control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      cases packet with
      | none => exact hexact
      | some packet =>
          cases hmove : packet.successor.2.1.2.2 with
          | none =>
              simpa [profiledRawJointRecurrentRightToLeftBridgeNoRecv,
                hmove] using hexact
          | some move =>
              simp [profiledRawJointRecurrentRightToLeftBridgeNoRecv, hmove,
                ProfiledRawJointRecurrentRightToLeftBridgePacketExact]
  | inr installed => trivial

theorem ProfiledRawJointRecurrentLeftToRightBridgePacketExact.noRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentLeftToRightBridgePacketExact A strategy hwin
        control)
    (input : In₁) :
    ProfiledRawJointRecurrentLeftToRightBridgePacketExact A strategy hwin
      (profiledRawJointRecurrentLeftToRightBridgeNoRecv A strategy hwin
        control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      cases packet with
      | none => exact hexact
      | some packet =>
          cases hmove : packet.successor.2.1.2.1 with
          | none =>
              simpa [profiledRawJointRecurrentLeftToRightBridgeNoRecv,
                hmove] using hexact
          | some move =>
              simp [profiledRawJointRecurrentLeftToRightBridgeNoRecv, hmove,
                ProfiledRawJointRecurrentLeftToRightBridgePacketExact]
  | inr installed => trivial

/-- Owner-only evolution changes the owner fibre but leaves the dormant
receiver fork, and hence its exact edge certificate, unchanged. -/
theorem ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom.noRecv
    (source : BankControl A strategy hwin)
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom A strategy
        hwin source control)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom A strategy hwin
      source (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy
        hwin control input).1 := by
  exact hexact

/-- Mirrored preservation under owner-only evolution. -/
theorem ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom.noRecv
    (source : BankControl A strategy hwin)
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom A strategy
        hwin source control)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom A strategy hwin
      source (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy
        hwin control input).1 := by
  exact hexact

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact.noRecv
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy
        hwin control)
    (input : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        control input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      exact
        ProfiledRawJointRecurrentLeftToRightBridgePacketExact.noRecv A
          strategy hwin bridge hexact input
  | inr pending => trivial

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact.noRecv
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy
        hwin control)
    (input : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        control input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      exact
        ProfiledRawJointRecurrentRightToLeftBridgePacketExact.noRecv A
          strategy hwin bridge hexact input
  | inr pending => trivial

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact.noRecv
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin control)
    (input : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          control input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      exact
        ProfiledRawJointRecurrentLeftToRightBridgePacketExact.noRecv A
          strategy hwin bridge hexact input
  | inr pending =>
      exact
        ProfiledRawJointRecurrentRightToLeftOwnerFibreEdgeExactFrom.noRecv A
          strategy hwin coordinates.1 pending hexact input

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact.noRecv
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin control)
    (input : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          control input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      exact
        ProfiledRawJointRecurrentRightToLeftBridgePacketExact.noRecv A
          strategy hwin bridge hexact input
  | inr pending =>
      exact
        ProfiledRawJointRecurrentLeftToRightOwnerFibreEdgeExactFrom.noRecv A
          strategy hwin coordinates.2 pending hexact input

/-- Owner-only evolution leaves process one's outer coordinates unchanged. -/
theorem ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact.noRecvOne
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin control.2)
    (input : In₁) :
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        control input).1.2 := by
  rcases control with ⟨base, coordinates⟩
  cases base <;>
    simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne] using hexact

/-- Owner-only evolution leaves process two's outer coordinates unchanged. -/
theorem ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact.noRecvTwo
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hexact :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin control.2)
    (input : In₂) :
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        control input).1.2 := by
  rcases control with ⟨base, coordinates⟩
  cases base <;>
    simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo] using hexact

theorem
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned.noRecv
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A
        strategy hwin control)
    (input : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          control input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      cases bridge with
      | inl staged =>
          rcases staged with ⟨state, receiver, packet⟩
          rcases haligned with ⟨hsource, hsuccessor⟩
          cases packet with
          | none =>
              exact ⟨hsource, hsuccessor⟩
          | some packet =>
              cases hmove : packet.successor.2.1.2.1 with
              | none =>
                  simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
                    profiledRawJointRecurrentLeftToRightBridgeNoRecv, hmove,
                    ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned]
                    using And.intro hsource hsuccessor
              | some move =>
                  simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
                    profiledRawJointRecurrentLeftToRightBridgeNoRecv, hmove,
                    ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned]
                    using hsuccessor packet rfl
      | inr installed =>
          exact haligned
  | inr pending =>
      rcases pending with ⟨member, shared, payload⟩
      cases member <;> exact haligned

theorem
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned.noRecv
    (control :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A
        strategy hwin control)
    (input : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          control input).1 := by
  rcases control with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      cases bridge with
      | inl staged =>
          rcases staged with ⟨state, receiver, packet⟩
          rcases haligned with ⟨hsource, hsuccessor⟩
          cases packet with
          | none =>
              exact ⟨hsource, hsuccessor⟩
          | some packet =>
              cases hmove : packet.successor.2.1.2.2 with
              | none =>
                  simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
                    profiledRawJointRecurrentRightToLeftBridgeNoRecv, hmove,
                    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned]
                    using And.intro hsource hsuccessor
              | some move =>
                  simpa [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
                    profiledRawJointRecurrentRightToLeftBridgeNoRecv, hmove,
                    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned]
                    using hsuccessor packet rfl
      | inr installed =>
          exact haligned
  | inr pending =>
      rcases pending with ⟨member, shared, payload⟩
      cases member <;> exact haligned

/-- Proof-side data witnessing which oriented boundary the executable decoder
selected at a receive.  The input is part of the observation because it fixes
the target evaluated by the finite receiver.  This is deliberately not yet a
completed policy edge: an acknowledgement may retain the open candidate. -/
inductive ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (input : In₁ × In₂) : Type _
  | right
      (phaseData :
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
      (decoded :
        profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          one two = some phaseData)
      (invariant :
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy
          hwin phaseData)
  | left
      (phaseData :
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
      (rightAbsent :
        profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          one two = none)
      (decoded :
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          one two = some phaseData)
      (invariant :
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy
          hwin phaseData)

namespace ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation

variable
  {one :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin}
  {two :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin}
  {input : In₁ × In₂}

/-- Orientation of the physical table whose receiver evaluated the target. -/
def side
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) : IndexedLineageSide :=
  match observation with
  | .right _ _ _ => .right
  | .left _ _ _ _ => .left

/-- Bank state read by the selected active receiver. -/
noncomputable def parent
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) : BankControl A strategy hwin :=
  match observation with
  | .right phaseData _ _ => phaseData.1.1
  | .left phaseData _ _ _ => phaseData.1.1

/-- The right/left bank-coordinate pair decoded at the current boundary.  In
a right-oriented phase the active parent is first; in a left-oriented phase
it is second. -/
noncomputable def phaseCoordinates
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin :=
  match observation with
  | .right phaseData _ _ => (phaseData.1.1, phaseData.2.1)
  | .left phaseData _ _ _ => (phaseData.2.1, phaseData.1.1)

@[simp] theorem phaseCoordinates_active
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    if observation.side A strategy hwin = .right then
      (observation.phaseCoordinates A strategy hwin).1 =
        observation.parent A strategy hwin
    else
      (observation.phaseCoordinates A strategy hwin).2 =
        observation.parent A strategy hwin := by
  cases observation <;> rfl

/-- On an installed/fibre boundary the installed process-one state is the
active parent.  This exposes a fact enforced by the decoder rather than by
the proof witness chosen for `Selected`. -/
theorem parent_eq_of_installedFibre
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin (.inl (.inr installed), oneCoordinates)
          (.inr pendingTwo, twoCoordinates) input) :
    observation.parent A strategy hwin = installed.1 := by
  cases observation with
  | right phaseData decoded invariant =>
      obtain ⟨rightOwner, leftTemplate, hinstalled, hphase⟩ :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
          A strategy hwin installed pendingTwo oneCoordinates twoCoordinates
            phaseData decoded
      simp only [parent]
      rw [hphase, hinstalled]
  | left phaseData rightAbsent decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded

/-- On the mirrored fibre/installed boundary the installed process-two state
is the active parent. -/
theorem parent_eq_of_fibreInstalled
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin (.inr pendingOne, oneCoordinates)
          (.inl (.inr installed), twoCoordinates) input) :
    observation.parent A strategy hwin = installed.1 := by
  cases observation with
  | right phaseData decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
  | left phaseData rightAbsent decoded invariant =>
      obtain ⟨leftOwner, rightTemplate, hinstalled, hphase⟩ :=
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
          A strategy hwin pendingOne installed oneCoordinates twoCoordinates
            phaseData decoded
      simp only [parent]
      rw [hphase, hinstalled]

/-- In the installed/fibre decoder shape, process one's complete coordinate
pair is exactly the decoded right/left phase pair. -/
theorem phaseCoordinates_eq_one_of_installedFibre
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A
        strategy hwin (.inl (.inr installed), oneCoordinates))
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin (.inl (.inr installed), oneCoordinates)
          (.inr pendingTwo, twoCoordinates) input) :
    observation.phaseCoordinates A strategy hwin = oneCoordinates := by
  cases observation with
  | right phaseData decoded invariant =>
      obtain ⟨rightOwner, leftTemplate, hinstalled, hphase⟩ :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
          A strategy hwin installed pendingTwo oneCoordinates twoCoordinates
            phaseData decoded
      have hstate :
          (profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy
            hwin pendingTwo).1 = oneCoordinates.1 := by
        have hinstalledState := congrArg
          (fun value :
            ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin
              ↦ value.1) hinstalled
        exact hinstalledState.symm.trans haligned.symm
      simp only [phaseCoordinates]
      rw [hphase]
      exact Prod.ext hstate rfl
  | left phaseData rightAbsent decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded

/-- Mirrored fibre/installed coordinate identification. -/
theorem phaseCoordinates_eq_two_of_fibreInstalled
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A
        strategy hwin (.inl (.inr installed), twoCoordinates))
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin (.inr pendingOne, oneCoordinates)
          (.inl (.inr installed), twoCoordinates) input) :
    observation.phaseCoordinates A strategy hwin = twoCoordinates := by
  cases observation with
  | right phaseData decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
  | left phaseData rightAbsent decoded invariant =>
      obtain ⟨leftOwner, rightTemplate, hinstalled, hphase⟩ :=
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
          A strategy hwin pendingOne installed oneCoordinates twoCoordinates
            phaseData decoded
      have hstate :
          (profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy
            hwin pendingOne).1 = twoCoordinates.2 := by
        have hinstalledState := congrArg
          (fun value :
            ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin
              ↦ value.1) hinstalled
        exact hinstalledState.symm.trans haligned.symm
      simp only [phaseCoordinates]
      rw [hphase]
      exact Prod.ext rfl hstate

/-- In the fibre/fibre quadrant the decoder reads the selected right state
from process two and the selected left state from process one.  Coordinate
alignment therefore identifies its phase pair with the corresponding mixed
outer-coordinate pair. -/
theorem phaseCoordinates_eq_mixed_of_fibreFibre
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (halignedOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A
        strategy hwin (.inr pendingOne, oneCoordinates))
    (halignedTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A
        strategy hwin (.inr pendingTwo, twoCoordinates))
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin (.inr pendingOne, oneCoordinates)
          (.inr pendingTwo, twoCoordinates) input) :
    observation.phaseCoordinates A strategy hwin =
      (twoCoordinates.1, oneCoordinates.2) := by
  cases observation with
  | right phaseData decoded invariant =>
      simp only [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
      split at decoded
      · have hstates :=
          profiledRawJointRecurrentOwnerFibreMakeRight?_states A strategy hwin
            _ _ _ _ _ _ phaseData decoded
        apply Prod.ext
        · simpa only [phaseCoordinates] using hstates.1.trans halignedTwo.symm
        · simpa only [phaseCoordinates] using hstates.2.trans halignedOne.symm
      · simp at decoded
  | left phaseData rightAbsent decoded invariant =>
      simp only [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded
      split at decoded
      · have hstates :=
          profiledRawJointRecurrentOwnerFibreMakeLeft?_states A strategy hwin
            _ _ _ _ _ _ phaseData decoded
        apply Prod.ext
        · simpa only [phaseCoordinates] using hstates.2.trans halignedTwo.symm
        · simpa only [phaseCoordinates] using hstates.1.trans halignedOne.symm
      · simp at decoded

/-- If process two is pending and the decoder selects a right phase, its
active parent is the first outer coordinate of process two. -/
theorem parent_eq_twoFirst_of_right_pendingTwo
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one (.inr pendingTwo, twoCoordinates))
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one (.inr pendingTwo, twoCoordinates) input)
    (hside : observation.side A strategy hwin = .right) :
    observation.parent A strategy hwin = twoCoordinates.1 := by
  cases observation with
  | left phaseData rightAbsent decoded invariant =>
      simp only [side] at hside
      cases hside
  | right phaseData decoded invariant =>
      rcases one with ⟨oneBase, oneCoordinates⟩
      cases oneBase with
      | inl oneBridge =>
          cases oneBridge with
          | inl stagedOne =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                at decoded
          | inr installed =>
              obtain ⟨rightOwner, leftTemplate, hinstalled, hphase⟩ :=
                profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
                  A strategy hwin installed pendingTwo oneCoordinates
                    twoCoordinates phaseData decoded
              simp only [parent]
              rw [hphase]
              exact haligned.2.symm
      | inr pendingOne =>
          have hphase :=
            phaseCoordinates_eq_mixed_of_fibreFibre A strategy hwin pendingOne
              pendingTwo oneCoordinates twoCoordinates haligned.1 haligned.2
                (.right phaseData decoded invariant) (input := input)
          simpa only [phaseCoordinates, parent] using congrArg Prod.fst hphase

/-- Whenever process two holds a usable staged right receiver, every selected
observation reads its active parent from the staged source state.  The peer
may be installed or an unresolved fibre. -/
theorem parent_eq_of_rightStaged
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : packet.successor.2.1.2.2 = some leftMove)
    (twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one
          (.inl (.inl (rightState, rightReceiver, some packet)),
            twoCoordinates)
          input) :
    observation.side A strategy hwin = .right ∧
      observation.parent A strategy hwin = rightState := by
  cases observation with
  | right phaseData decoded invariant =>
      refine ⟨rfl, ?_⟩
      simp only [parent]
      rcases one with ⟨oneBase, oneCoordinates⟩
      cases oneBase with
      | inl bridge =>
          cases bridge with
          | inl stagedOne =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
          | inr installed =>
              obtain ⟨state, receiver, owner, template, resolved, move,
                  hinstalled, hstaged, hmove, hphase⟩ :=
                profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged_inv
                  A strategy hwin installed
                    (rightState, rightReceiver, some packet) oneCoordinates
                      twoCoordinates phaseData decoded
              rw [hphase]
              exact
                (congrArg
                  (fun staged :
                    ProfiledRawJointRecurrentRightToLeftStagedReceiver A
                      strategy hwin ↦ staged.1) hstaged).symm
      | inr pending =>
          simp only [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
            hleftMove] at decoded
          exact
            (profiledRawJointRecurrentOwnerFibreMakeRight?_states A strategy
              hwin _ _ _ _ _ _ phaseData decoded).1
  | left phaseData rightAbsent decoded invariant =>
      rcases one with ⟨oneBase, oneCoordinates⟩
      cases oneBase with
      | inl bridge =>
          cases bridge <;>
            simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded
      | inr pending =>
          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded

/-- A usable staged right receiver exposes the complete exact edge decoded by
the selected observation, not only its active endpoint. -/
theorem phaseCoordinates_eq_of_rightStaged
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : packet.successor.2.1.2.2 = some leftMove)
    (twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one
          (.inl (.inl (rightState, rightReceiver, some packet)),
            twoCoordinates)
          input) :
    observation.phaseCoordinates A strategy hwin =
      (rightState, packet.successor) := by
  have hsource :=
    observation.parent_eq_of_rightStaged A strategy hwin one rightState
      rightReceiver packet leftMove hleftMove twoCoordinates
  have hside := hsource.1
  have hparent := hsource.2
  cases observation with
  | right phaseData decoded invariant =>
      apply Prod.ext
      · simpa only [phaseCoordinates, parent] using hparent
      · rcases one with ⟨oneBase, oneCoordinates⟩
        cases oneBase with
        | inl bridge =>
            cases bridge with
            | inl stagedOne =>
                simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                  at decoded
            | inr installed =>
                obtain ⟨state, receiver, owner, template, resolved, move,
                    hinstalled, hstaged, hmove, hphase⟩ :=
                  profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged_inv
                    A strategy hwin installed
                      (rightState, rightReceiver, some packet) oneCoordinates
                        twoCoordinates phaseData decoded
                have hpacket : resolved = packet := by
                  have := congrArg
                    (fun staged :
                      ProfiledRawJointRecurrentRightToLeftStagedReceiver A
                        strategy hwin ↦ staged.2.2) hstaged
                  simpa using Option.some.inj this.symm
                simp only [phaseCoordinates]
                rw [hphase, hpacket]
        | inr pending =>
            have hstates :=
              profiledRawJointRecurrentOwnerFibreMakeRight?_states A strategy
                hwin rightState
                  (profiledRawJointRightOwnerFibreExceptional A
                    pending.2.1.1)
                  (pending.2.1.1.receiverAt A rightReceiver)
                  packet.successor
                  ⟨leftMove, (leftMove.memberController A false).initial⟩
                  (initialProfiledRawJointLeftPhysicalSiblingReceiver A
                    leftMove .first)
                  phaseData (by
                    simpa only [
                      profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                      hleftMove] using decoded)
            simpa only [phaseCoordinates] using hstates.2
  | left phaseData rightAbsent decoded invariant =>
      simp only [side] at hside
      cases hside

/-- Mirrored source-identification theorem for a usable staged left
receiver at process one. -/
theorem parent_eq_of_leftStaged
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : packet.successor.2.1.2.1 = some rightMove)
    (oneCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin
          (.inl (.inl (leftState, leftReceiver, some packet)),
            oneCoordinates)
          two input) :
    observation.side A strategy hwin = .left ∧
      observation.parent A strategy hwin = leftState := by
  cases observation with
  | right phaseData decoded invariant =>
      rcases two with ⟨twoBase, twoCoordinates⟩
      cases twoBase with
      | inl bridge =>
          cases bridge <;>
            simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
      | inr pending =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
  | left phaseData rightAbsent decoded invariant =>
      refine ⟨rfl, ?_⟩
      simp only [parent]
      rcases two with ⟨twoBase, twoCoordinates⟩
      cases twoBase with
      | inl bridge =>
          cases bridge with
          | inl stagedTwo =>
              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded
          | inr installed =>
              obtain ⟨state, receiver, owner, template, resolved, move,
                  hstaged, hinstalled, hmove, hphase⟩ :=
                profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled_inv
                  A strategy hwin (leftState, leftReceiver, some packet)
                    installed oneCoordinates twoCoordinates phaseData decoded
              rw [hphase]
              exact
                (congrArg
                  (fun staged :
                    ProfiledRawJointRecurrentLeftToRightStagedReceiver A
                      strategy hwin ↦ staged.1) hstaged).symm
      | inr pending =>
          by_cases hpending : pending.1 = true
          · simp only [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
              hpending, if_pos, hrightMove] at decoded
            exact
              (profiledRawJointRecurrentOwnerFibreMakeLeft?_states A strategy
                hwin _ _ _ _ _ _ phaseData decoded).1
          · simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
              hpending] at decoded

/-- Mirrored full-coordinate identification for a usable staged left
receiver. -/
theorem phaseCoordinates_eq_of_leftStaged
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : packet.successor.2.1.2.1 = some rightMove)
    (oneCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin
          (.inl (.inl (leftState, leftReceiver, some packet)),
            oneCoordinates)
          two input) :
    observation.phaseCoordinates A strategy hwin =
      (packet.successor, leftState) := by
  have hsource :=
    observation.parent_eq_of_leftStaged A strategy hwin leftState leftReceiver
      packet rightMove hrightMove oneCoordinates two
  have hside := hsource.1
  have hparent := hsource.2
  cases observation with
  | right phaseData decoded invariant =>
      simp only [side] at hside
      cases hside
  | left phaseData rightAbsent decoded invariant =>
      apply Prod.ext
      · rcases two with ⟨twoBase, twoCoordinates⟩
        cases twoBase with
        | inl bridge =>
            cases bridge with
            | inl stagedTwo =>
                simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                  at decoded
            | inr installed =>
                obtain ⟨state, receiver, owner, template, resolved, move,
                    hstaged, hinstalled, hmove, hphase⟩ :=
                  profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled_inv
                    A strategy hwin
                      (leftState, leftReceiver, some packet) installed
                        oneCoordinates twoCoordinates phaseData decoded
                have hpacket : resolved = packet := by
                  have := congrArg
                    (fun staged :
                      ProfiledRawJointRecurrentLeftToRightStagedReceiver A
                        strategy hwin ↦ staged.2.2) hstaged
                  simpa using (Option.some.inj this).symm
                simp only [phaseCoordinates]
                rw [hphase, hpacket]
        | inr pending =>
            by_cases hpending : pending.1 = true
            · have hstates :=
                profiledRawJointRecurrentOwnerFibreMakeLeft?_states A strategy
                  hwin leftState
                    (profiledRawJointLeftOwnerFibreExceptional A
                      pending.2.1.1)
                    (pending.2.1.1.receiverAt A leftReceiver)
                    packet.successor
                    ⟨rightMove, (rightMove.memberController A false).initial⟩
                    (initialProfiledRawJointRightPhysicalSiblingReceiver A
                      rightMove .first)
                    phaseData (by
                      simpa only [
                        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                        hpending, if_pos, hrightMove] using decoded)
              simpa only [phaseCoordinates] using hstates.2
            · simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                hpending] at decoded
      · simpa only [phaseCoordinates, parent] using hparent

/-- The decoder's current right/left phase pair is always one genuine policy
edge.  Staged shapes use the retained exact packet, installed/fibre shapes
use the installed endpoint's local coordinate certificate, and fibre/fibre
uses the single pending-only cross-coordinate condition. -/
theorem phaseCoordinates_edgeExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin one two)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one two)
    (hedges :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin one two)
    (hcoherent :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin one two) :
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      (observation.phaseCoordinates A strategy hwin) := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  rcases hdeferred with ⟨hdeferredOne, hdeferredTwo⟩
  rcases haligned with ⟨halignedOne, halignedTwo⟩
  rcases hedges with ⟨hedgeOne, hedgeTwo⟩
  cases oneBase with
  | inl oneBridge =>
      cases oneBridge with
      | inl stagedOne =>
          rcases stagedOne with ⟨leftState, leftReceiver, stored⟩
          cases twoBase with
          | inl twoBridge =>
              cases twoBridge with
              | inl stagedTwo =>
                  cases observation with
                  | right phaseData decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                        at decoded
                  | left phaseData rightAbsent decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                        at decoded
              | inr installed =>
                  cases stored with
                  | none =>
                      cases observation with
                      | right phaseData decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                            at decoded
                      | left phaseData rightAbsent decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                            at decoded
                  | some packet =>
                      cases hrightMove : packet.successor.2.1.2.1 with
                      | none =>
                          cases observation with
                          | right phaseData decoded invariant =>
                              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                                at decoded
                          | left phaseData rightAbsent decoded invariant =>
                              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                                hrightMove] at decoded
                      | some rightMove =>
                          have hphase :=
                            phaseCoordinates_eq_of_leftStaged A strategy hwin
                              leftState leftReceiver packet rightMove
                                hrightMove oneCoordinates
                                  (.inl (.inr installed), twoCoordinates)
                                    observation
                          rw [hphase]
                          exact Or.inr
                            ⟨packet, hdeferredOne packet rfl, rfl⟩
          | inr pendingTwo =>
              cases stored with
              | none =>
                  cases observation with
                  | right phaseData decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                        at decoded
                  | left phaseData rightAbsent decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                        at decoded
              | some packet =>
                  cases hrightMove : packet.successor.2.1.2.1 with
                  | none =>
                      cases observation with
                      | right phaseData decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                            at decoded
                      | left phaseData rightAbsent decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                            hrightMove] at decoded
                  | some rightMove =>
                      have hphase :=
                        phaseCoordinates_eq_of_leftStaged A strategy hwin
                          leftState leftReceiver packet rightMove hrightMove
                            oneCoordinates (.inr pendingTwo, twoCoordinates)
                              observation
                      rw [hphase]
                      exact Or.inr ⟨packet, hdeferredOne packet rfl, rfl⟩
      | inr installed =>
          cases twoBase with
          | inl twoBridge =>
              cases twoBridge with
              | inl stagedTwo =>
                  rcases stagedTwo with ⟨rightState, rightReceiver, stored⟩
                  cases stored with
                  | none =>
                      cases observation with
                      | right phaseData decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                            at decoded
                      | left phaseData rightAbsent decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                            at decoded
                  | some packet =>
                      cases hleftMove : packet.successor.2.1.2.2 with
                      | none =>
                          cases observation with
                          | right phaseData decoded invariant =>
                              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                                hleftMove] at decoded
                          | left phaseData rightAbsent decoded invariant =>
                              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                                at decoded
                      | some leftMove =>
                          have hphase :=
                            phaseCoordinates_eq_of_rightStaged A strategy hwin
                              (.inl (.inr installed), oneCoordinates)
                                rightState rightReceiver packet leftMove
                                  hleftMove twoCoordinates observation
                          rw [hphase]
                          exact Or.inl
                            ⟨packet, hdeferredTwo packet rfl, rfl⟩
              | inr installedTwo =>
                  cases observation with
                  | right phaseData decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                        at decoded
                  | left phaseData rightAbsent decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                        at decoded
          | inr pendingTwo =>
              have hphase :=
                phaseCoordinates_eq_one_of_installedFibre A strategy hwin
                  installed pendingTwo oneCoordinates twoCoordinates
                    halignedOne observation
              rw [hphase]
              exact hedgeOne
  | inr pendingOne =>
      cases twoBase with
      | inl twoBridge =>
          cases twoBridge with
          | inl stagedTwo =>
              rcases stagedTwo with ⟨rightState, rightReceiver, stored⟩
              cases stored with
              | none =>
                  cases observation with
                  | right phaseData decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                        at decoded
                  | left phaseData rightAbsent decoded invariant =>
                      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                        at decoded
              | some packet =>
                  cases hleftMove : packet.successor.2.1.2.2 with
                  | none =>
                      cases observation with
                      | right phaseData decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                            hleftMove] at decoded
                      | left phaseData rightAbsent decoded invariant =>
                          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                            at decoded
                  | some leftMove =>
                      have hphase :=
                        phaseCoordinates_eq_of_rightStaged A strategy hwin
                          (.inr pendingOne, oneCoordinates) rightState
                            rightReceiver packet leftMove hleftMove
                              twoCoordinates observation
                      rw [hphase]
                      exact Or.inl ⟨packet, hdeferredTwo packet rfl, rfl⟩
          | inr installed =>
              have hphase :=
                phaseCoordinates_eq_two_of_fibreInstalled A strategy hwin
                  pendingOne installed oneCoordinates twoCoordinates
                    halignedTwo observation
              rw [hphase]
              exact hedgeTwo
      | inr pendingTwo =>
          have hphase :=
            phaseCoordinates_eq_mixed_of_fibreFibre A strategy hwin pendingOne
              pendingTwo oneCoordinates twoCoordinates halignedOne halignedTwo
                observation
          rw [hphase]
          change oneCoordinates.1 = twoCoordinates.1 ∨
              oneCoordinates.2 = twoCoordinates.2 at hcoherent
          rcases hcoherent with hfirst | hsecond
          · rw [← hfirst]
            exact hedgeOne
          · rw [hsecond]
            exact hedgeTwo

/-- Bare target locally evaluated by the selected active receiver. -/
noncomputable def target
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  match observation with
  | .right phaseData _ _ =>
      phaseData.1.target A strategy hwin input
  | .left phaseData _ _ _ =>
      phaseData.1.target A strategy hwin input

/-- Exact finite packet computed by the informed endpoint at this receive. -/
noncomputable def packet
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin :=
  profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy hwin
    (observation.parent A strategy hwin)
    (observation.target A strategy hwin)

/-- The pair of local receive-created forks selected by this observation. -/
noncomputable def receiveResult
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :=
  match observation with
  | .right phaseData _ _ =>
      phaseData.ownerFibreReceive A strategy hwin input
  | .left phaseData _ _ _ =>
      phaseData.ownerFibreReceive A strategy hwin input

/-- The observation's receive result is exactly the value returned by the
total executable decoder. -/
theorem boundaryReceive?_eq
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one two
        input =
      some (observation.receiveResult A strategy hwin) := by
  cases observation with
  | right phaseData decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?,
        receiveResult, decoded]
  | left phaseData rightAbsent decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?,
        receiveResult, rightAbsent, decoded]

/-- Semantic selection proves that an observation of the actual executable
decoder exists. -/
theorem nonempty_ofSelected
    (selected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two) :
    Nonempty
      (ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) := by
  cases selected with
  | right phaseData decoded invariant =>
      exact ⟨.right phaseData decoded invariant⟩
  | left phaseData rightAbsent decoded invariant =>
      exact ⟨.left phaseData rightAbsent decoded invariant⟩

/-- Canonical proof-side observation selected from the actual decoder
witness.  Classical choice is confined to proof bookkeeping; the executable
receiver still uses the finite decoder and resolver above. -/
noncomputable def ofSelected
    (selected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A strategy
      hwin one two input :=
  Classical.choice (nonempty_ofSelected A strategy hwin selected)

/-- Change only the input used to query the next receiver.  Decoder
selection and phase invariants are properties of the controls, so this
operation leaves the observed side and parent unchanged. -/
def reinput
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (nextInput : In₁ × In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A strategy
      hwin one two nextInput :=
  match observation with
  | .right phaseData decoded invariant =>
      .right phaseData decoded invariant
  | .left phaseData rightAbsent decoded invariant =>
      .left phaseData rightAbsent decoded invariant

@[simp] theorem reinput_side
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (nextInput : In₁ × In₂) :
    (observation.reinput A strategy hwin nextInput).side A strategy hwin =
      observation.side A strategy hwin := by
  cases observation <;> rfl

@[simp] theorem reinput_parent
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (nextInput : In₁ × In₂) :
    (observation.reinput A strategy hwin nextInput).parent A strategy hwin =
      observation.parent A strategy hwin := by
  cases observation <;> rfl

/-- The active bank parent is independent of the proof witness used to expose
the deterministic decoder result. -/
theorem parent_eq
    (first second :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    first.parent A strategy hwin = second.parent A strategy hwin := by
  cases first with
  | right firstData firstDecoded firstInvariant =>
      cases second with
      | right secondData secondDecoded secondInvariant =>
          have hdata : firstData = secondData := by
            exact Option.some.inj (firstDecoded.symm.trans secondDecoded)
          subst secondData
          rfl
      | left secondData secondAbsent secondDecoded secondInvariant =>
          rw [secondAbsent] at firstDecoded
          contradiction
  | left firstData firstAbsent firstDecoded firstInvariant =>
      cases second with
      | right secondData secondDecoded secondInvariant =>
          rw [firstAbsent] at secondDecoded
          contradiction
      | left secondData secondAbsent secondDecoded secondInvariant =>
          have hdata : firstData = secondData := by
            exact Option.some.inj (firstDecoded.symm.trans secondDecoded)
          subst secondData
          rfl

/-- Uniform proof-side certificate for one policy edge that has actually
become active.  It records the exact resolver packet, source equality through
`ExactFrom`, the next active parent, and the orientation flip. -/
def CommittedEdge
    {nextOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin}
    {nextTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin}
    {nextInput : In₁ × In₂}
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (nextObservation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin nextOne nextTwo nextInput) : Prop :=
  ∃ packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin,
    packet.ExactFrom A strategy hwin
        (observation.parent A strategy hwin) ∧
      nextObservation.parent A strategy hwin = packet.successor ∧
      nextObservation.side A strategy hwin =
        (observation.side A strategy hwin).other

/-- The selected parent is reachable inside the policy fixed by its bank
key. -/
theorem parent_reachable
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
      (observation.parent A strategy hwin) := by
  cases observation with
  | right phaseData decoded invariant =>
      have hactive := invariant.1
      dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactive
      rcases hactive with
        ⟨code, root, past, hreachable, hcode, hroot, hmove, howner,
          hmonitor⟩
      exact hreachable
  | left phaseData rightAbsent decoded invariant =>
      have hactive := invariant.1
      dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactive
      rcases hactive with
        ⟨code, root, past, hreachable, hcode, hroot, hmove, howner,
          hmonitor⟩
      exact hreachable

/-- The current bank code contains a live root on the selected orientation. -/
theorem exists_current_live_root
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
      ∃ root : ProfiledRawJointThreadRoot A,
        (observation.parent A strategy hwin).2.1.1 = code ∧
          profiledRawJointOneSidedCurrentSlots A
              (observation.side A strategy hwin) code () = some root := by
  cases observation with
  | right phaseData decoded invariant =>
      have hactive := invariant.1
      dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactive
      rcases hactive with
        ⟨code, root, past, hreachable, hcode, hroot, hmove, howner,
          hmonitor⟩
      exact ⟨code, root, hcode, hroot⟩
  | left phaseData rightAbsent decoded invariant =>
      have hactive := invariant.1
      dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactive
      rcases hactive with
        ⟨code, root, past, hreachable, hcode, hroot, hmove, howner,
          hmonitor⟩
      exact ⟨code, root, hcode, hroot⟩

/-- The locally evaluated target contains a live root on the crossed
orientation. -/
theorem exists_target_live_root
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ∃ root : ProfiledRawJointThreadRoot A,
      profiledRawJointOneSidedCurrentSlots A
          (observation.side A strategy hwin).other
          (observation.target A strategy hwin) () = some root := by
  cases observation with
  | right phaseData decoded invariant =>
      obtain ⟨hrealizes, root, hroot⟩ :=
        (profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy hwin
          phaseData.1 invariant.1) input
      exact ⟨root, hroot⟩
  | left phaseData rightAbsent decoded invariant =>
      obtain ⟨hrealizes, root, hroot⟩ :=
        (profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy hwin
          phaseData.1 invariant.1) input
      exact ⟨root, hroot⟩

/-- The packet is the exact realizing child selected by the fixed bank
resolver.  In particular, its successor keeps the parent key and is reachable
inside the same rational policy. -/
theorem packet_spec
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let parent := observation.parent A strategy hwin
    let target := observation.target A strategy hwin
    let packet := observation.packet A strategy hwin
    packet.target = target ∧
      packet.childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
          hwin parent target packet.childCode ∧
      packet.successor =
        profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin parent packet.childCode ∧
      packet.successor.1 = parent.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        packet.successor := by
  cases observation with
  | right phaseData decoded invariant =>
      have hactive := invariant.1
      have hactiveCopy := hactive
      dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
      rcases hactiveCopy with
        ⟨currentCode, currentRoot, past, hreachable, hcurrentCode,
          hcurrentRoot, hmove, howner, hmonitor⟩
      obtain ⟨hrealizes, targetRoot, htargetRoot⟩ :=
        (profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy hwin
          phaseData.1 hactive) input
      let target := phaseData.1.target A strategy hwin input
      let childCode :=
        profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
          hwin phaseData.1.1 target
      have hresolve :=
        profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_spec A
          strategy hwin phaseData.1.1 hreachable target
            ⟨childCode, hrealizes⟩
      rcases hresolve with
        ⟨hexact, hrealizesResolved, hkey, hsuccessorReachable⟩
      exact ⟨rfl, hexact, hrealizesResolved, rfl, hkey,
        hsuccessorReachable⟩

  | left phaseData rightAbsent decoded invariant =>
      have hactive := invariant.1
      have hactiveCopy := hactive
      dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
      rcases hactiveCopy with
        ⟨currentCode, currentRoot, past, hreachable, hcurrentCode,
          hcurrentRoot, hmove, howner, hmonitor⟩
      obtain ⟨hrealizes, targetRoot, htargetRoot⟩ :=
        (profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy hwin
          phaseData.1 hactive) input
      let target := phaseData.1.target A strategy hwin input
      let childCode :=
        profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
          hwin phaseData.1.1 target
      have hresolve :=
        profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_spec A
          strategy hwin phaseData.1.1 hreachable target
            ⟨childCode, hrealizes⟩
      rcases hresolve with
        ⟨hexact, hrealizesResolved, hkey, hsuccessorReachable⟩
      exact ⟨rfl, hexact, hrealizesResolved, rfl, hkey,
        hsuccessorReachable⟩

/-- Every selected receive computes an exact edge from its observed parent.
This statement still does not assert that the edge is committed. -/
theorem packet_exactFrom
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    (observation.packet A strategy hwin).ExactFrom A strategy hwin
      (observation.parent A strategy hwin) := by
  have hspec := observation.packet_spec A strategy hwin
  exact
    { source_reachable := observation.parent_reachable A strategy hwin
      resolved := rfl
      realizes := hspec.2.2.1 }

/-- In a right-oriented receive, the open process-two candidate literally
stores the packet computed by the selected resolver, with the observed parent
as its staged source.  This is stronger than packet exactness: it identifies
the packet that a later strict-left round can consume. -/
theorem receiveResult_openTwo_stages_packet_of_right
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .right) :
    ∃ receiver : ProfiledRawJointRightPhysicalSiblingReceiver A,
      ∃ coordinates :
          ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin,
        (observation.receiveResult A strategy hwin).2.1.openControl =
          (.inl (.inl
            (observation.parent A strategy hwin, receiver,
              some (observation.packet A strategy hwin))), coordinates) := by
  cases observation with
  | right phaseData decoded invariant =>
      refine ⟨
        (profiledRawJointRecurrentRightReceiveFor A strategy hwin
          phaseData.1.1 (phaseData.1.receiver A strategy hwin)
            (phaseData.1.owner A strategy hwin) (input.2, input.1)).1.2.1,
        (phaseData.1.1, phaseData.1.successor A strategy hwin input), ?_⟩
      simp only [receiveResult,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
        profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
        parent, packet, target]
      split <;> rfl
  | left phaseData rightAbsent decoded invariant =>
      simp [side] at hside

/-- Mirrored literal staging fact for a left-oriented receive. -/
theorem receiveResult_openOne_stages_packet_of_left
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .left) :
    ∃ receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A,
      ∃ coordinates :
          ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin,
        (observation.receiveResult A strategy hwin).1.1.openControl =
          (.inl (.inl
            (observation.parent A strategy hwin, receiver,
              some (observation.packet A strategy hwin))), coordinates) := by
  cases observation with
  | right phaseData decoded invariant =>
      simp [side] at hside
  | left phaseData rightAbsent decoded invariant =>
      refine ⟨
        (profiledRawJointRecurrentLeftReceiveFor A strategy hwin
          phaseData.1.1 (phaseData.1.receiver A strategy hwin)
            (phaseData.1.owner A strategy hwin) input).1.2.1,
        (phaseData.1.successor A strategy hwin input, phaseData.1.1), ?_⟩
      simp only [receiveResult,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
        profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
        parent, packet, target]
      split <;> rfl

/-- Decoder-facing form of literal right-receiver staging. -/
theorem openRecvTwo_stages_packet_of_right
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .right) :
    ∃ receiver : ProfiledRawJointRightPhysicalSiblingReceiver A,
      ∃ coordinates :
          ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin,
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
            hwin two input.2 one input.1).1 =
          (.inl (.inl
            (observation.parent A strategy hwin, receiver,
              some (observation.packet A strategy hwin))), coordinates) := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  obtain ⟨receiver, coordinates, hstaged⟩ :=
    observation.receiveResult_openTwo_stages_packet_of_right A strategy hwin
      hside
  refine ⟨receiver, coordinates, ?_⟩
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    using hstaged

/-- Decoder-facing form of literal left-receiver staging. -/
theorem openRecvOne_stages_packet_of_left
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .left) :
    ∃ receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A,
      ∃ coordinates :
          ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin,
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
            hwin one input.1 two input.2).1 =
          (.inl (.inl
            (observation.parent A strategy hwin, receiver,
              some (observation.packet A strategy hwin))), coordinates) := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  obtain ⟨receiver, coordinates, hstaged⟩ :=
    observation.receiveResult_openOne_stages_packet_of_left A strategy hwin
      hside
  refine ⟨receiver, coordinates, ?_⟩
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    using hstaged

/-- A right-oriented observation's exact target supplies the physical
left-move stored in the resolver successor.  Hence the staged packet created
above cannot take the fallback branch when a strict-left round consumes it. -/
theorem packet_leftMove_exists_of_right
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .right) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (observation.packet A strategy hwin).successor.2.1.2.2 = some move := by
  obtain ⟨root, hroot⟩ :=
    observation.exists_target_live_root A strategy hwin
  have hrootLeft :
      profiledRawJointOneSidedCurrentSlots A .left
          (observation.target A strategy hwin) () = some root := by
    simpa [hside] using hroot
  have hrealizes :=
    (observation.packet_spec A strategy hwin).2.2.1
  simpa [packet,
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
    (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin (observation.parent A strategy hwin)
        (observation.target A strategy hwin) hrealizes root hrootLeft)

/-- Mirrored physical-move existence for a left-oriented observation. -/
theorem packet_rightMove_exists_of_left
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .left) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (observation.packet A strategy hwin).successor.2.1.2.1 = some move := by
  obtain ⟨root, hroot⟩ :=
    observation.exists_target_live_root A strategy hwin
  have hrootRight :
      profiledRawJointOneSidedCurrentSlots A .right
          (observation.target A strategy hwin) () = some root := by
    simpa [hside] using hroot
  have hrealizes :=
    (observation.packet_spec A strategy hwin).2.2.1
  simpa [packet,
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] using
    (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin (observation.parent A strategy hwin)
        (observation.target A strategy hwin) hrealizes root hrootRight)

private theorem rightBridgeFork_packetExact
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (hexact :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state
          (((receiver.1.memberController A false).labelOf owner).2
            receiver.2.2.1 input |>.target receiver.2.1)).ExactFrom A strategy
              hwin state) :
    let fork :=
      (profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo A strategy hwin
        state receiver owner input).1
    ProfiledRawJointRecurrentRightToLeftBridgePacketExact A strategy hwin
        fork.openControl ∧
      ProfiledRawJointRecurrentRightToLeftBridgePacketExact A strategy hwin
        fork.closedControl := by
  simp only [profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo]
  split
  · constructor <;>
      simpa [ProfiledRawJointRecurrentRightToLeftBridgePacketExact,
        profiledRawJointRecurrentRightReceiveFor] using hexact
  · refine ⟨?_, trivial⟩
    simpa [ProfiledRawJointRecurrentRightToLeftBridgePacketExact,
      profiledRawJointRecurrentRightReceiveFor] using hexact

private theorem leftBridgeFork_packetExact
    (state : BankControl A strategy hwin)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hexact :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state
          (((receiver.1.memberController A false).labelOf owner).2
            receiver.2.2.1 input |>.target receiver.2.1)).ExactFrom A strategy
              hwin state) :
    let fork :=
      (profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne A strategy hwin
        state receiver owner input).1
    ProfiledRawJointRecurrentLeftToRightBridgePacketExact A strategy hwin
        fork.openControl ∧
      ProfiledRawJointRecurrentLeftToRightBridgePacketExact A strategy hwin
        fork.closedControl := by
  simp only [profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne]
  split
  · constructor <;>
      simpa [ProfiledRawJointRecurrentLeftToRightBridgePacketExact,
        profiledRawJointRecurrentLeftReceiveFor] using hexact
  · refine ⟨?_, trivial⟩
    simpa [ProfiledRawJointRecurrentLeftToRightBridgePacketExact,
      profiledRawJointRecurrentLeftReceiveFor] using hexact

/-- Every packet-bearing open or closed candidate created by a selected
receive retains an exact resolver edge.  Pending owner-fibre candidates carry
no staged packet and satisfy the property vacuously. -/
theorem receiveResult_packetExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let result := observation.receiveResult A strategy hwin
    ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        result.1.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        result.1.1.closedControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        result.2.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        result.2.1.closedControl := by
  cases observation with
  | right phaseData decoded invariant =>
      have hpacket :=
        packet_exactFrom A strategy hwin
          (ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.right
            phaseData decoded invariant (input := input))
      have hbridge :=
        rightBridgeFork_packetExact A strategy hwin phaseData.1.1
          (phaseData.1.receiver A strategy hwin)
          (phaseData.1.owner A strategy hwin) (input.2, input.1) hpacket
      exact ⟨trivial, trivial, hbridge.1, hbridge.2⟩
  | left phaseData rightAbsent decoded invariant =>
      have hpacket :=
        packet_exactFrom A strategy hwin
          (ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.left
            phaseData rightAbsent decoded invariant (input := input))
      have hbridge :=
        leftBridgeFork_packetExact A strategy hwin phaseData.1.1
          (phaseData.1.receiver A strategy hwin)
          (phaseData.1.owner A strategy hwin) input hpacket
      exact ⟨hbridge.1, hbridge.2, trivial, trivial⟩

/-- Every receive-created candidate has complete delayed-edge provenance.
On the selected side, the owner fibre stores the resolver edge as its
open/closed bank pair.  On the opposite endpoint, the staged bridge stores
the same exact packet explicitly. -/
theorem receiveResult_deferredExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let result := observation.receiveResult A strategy hwin
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin result.1.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
          hwin result.1.1.closedControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
          hwin result.2.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin result.2.1.closedControl := by
  cases observation with
  | right phaseData decoded invariant =>
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.right
          phaseData decoded invariant (input := input)
      have hpacket := observation.packet_exactFrom A strategy hwin
      have hfibre :=
        profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork_edgeExact
          A strategy hwin
            ⟨(phaseData.1.receiver A strategy hwin).1,
              phaseData.1.owner A strategy hwin⟩
            phaseData.2.1 phaseData.1.1 phaseData.1.2.2 phaseData.2.2
            (observation.packet A strategy hwin) input hpacket
      have hbridge :=
        rightBridgeFork_packetExact A strategy hwin phaseData.1.1
          (phaseData.1.receiver A strategy hwin)
          (phaseData.1.owner A strategy hwin) (input.2, input.1) hpacket
      simpa only [receiveResult,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact,
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact,
        observation, packet, parent, target] using
          And.intro hfibre.1 (And.intro hfibre.2
            (And.intro hbridge.1 hbridge.2))
  | left phaseData rightAbsent decoded invariant =>
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.left
          phaseData rightAbsent decoded invariant (input := input)
      have hpacket := observation.packet_exactFrom A strategy hwin
      have hbridge :=
        leftBridgeFork_packetExact A strategy hwin phaseData.1.1
          (phaseData.1.receiver A strategy hwin)
          (phaseData.1.owner A strategy hwin) input hpacket
      have hfibre :=
        profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork_edgeExact
          A strategy hwin
            ⟨(phaseData.1.receiver A strategy hwin).1,
              phaseData.1.owner A strategy hwin⟩
            phaseData.2.1 phaseData.1.1 phaseData.1.2.2 phaseData.2.2
            (observation.packet A strategy hwin) (input.2, input.1) hpacket
      simpa only [receiveResult,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact,
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact,
        observation, packet, parent, target] using
          And.intro hbridge.1 (And.intro hbridge.2
            (And.intro hfibre.1 hfibre.2))

/-- Every open and closed receive candidate gives its two outer bank
coordinates their literal semantic meaning. -/
theorem receiveResult_coordinateAligned
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let result := observation.receiveResult A strategy hwin
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A strategy
        hwin result.1.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A
          strategy hwin result.1.1.closedControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A
          strategy hwin result.2.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A
        strategy hwin result.2.1.closedControl := by
  cases observation with
  | right phaseData decoded invariant =>
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.right
          phaseData decoded invariant (input := input)
      obtain ⟨move, hmove⟩ :=
        observation.packet_leftMove_exists_of_right A strategy hwin rfl
      have hmove' :
          (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
            strategy hwin phaseData.1.1
              (phaseData.1.target A strategy hwin input)).successor.2.1.2.2 =
            some move := by
        simpa only [observation, packet, parent, target] using hmove
      dsimp only [
        profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
        ProfiledRawJointRecurrentRightBoundaryData.target,
        ProfiledRawJointRecurrentRightBoundaryData.receiver,
        ProfiledRawJointRecurrentRightBoundaryData.owner] at hmove'
      simp [receiveResult,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
        profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
        profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
        profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
        profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
        profiledRawJointRecurrentRightToLeftPhaseLiveShared,
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned,
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned,
        profiledRawJointRecurrentRightToLeftOwnerFibreReceiver,
        profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
        profiledRawJointRecurrentRightReceiveFor,
        ProfiledRawJointRecurrentRightBoundaryData.successor,
        ProfiledRawJointRecurrentRightBoundaryData.target,
        ProfiledRawJointRecurrentRightBoundaryData.receiver,
        ProfiledRawJointRecurrentRightBoundaryData.owner,
        FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
        observation, packet, parent, target, hmove']

  | left phaseData rightAbsent decoded invariant =>
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.left
          phaseData rightAbsent decoded invariant (input := input)
      obtain ⟨move, hmove⟩ :=
        observation.packet_rightMove_exists_of_left A strategy hwin rfl
      have hmove' :
          (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
            strategy hwin phaseData.1.1
              (phaseData.1.target A strategy hwin input)).successor.2.1.2.1 =
            some move := by
        simpa only [observation, packet, parent, target] using hmove
      dsimp only [
        profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
        ProfiledRawJointRecurrentLeftBoundaryData.target,
        ProfiledRawJointRecurrentLeftBoundaryData.receiver,
        ProfiledRawJointRecurrentLeftBoundaryData.owner] at hmove'
      simp [receiveResult,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
        profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
        profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
        profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
        profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
        profiledRawJointRecurrentLeftToRightPhaseLiveShared,
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned,
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned,
        profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
        profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
        profiledRawJointRecurrentLeftReceiveFor,
        ProfiledRawJointRecurrentLeftBoundaryData.successor,
        ProfiledRawJointRecurrentLeftBoundaryData.target,
        ProfiledRawJointRecurrentLeftBoundaryData.receiver,
        ProfiledRawJointRecurrentLeftBoundaryData.owner,
        FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
        observation, packet, parent, target, hmove']

/-- If the currently decoded right/left coordinate pair is an exact policy
edge, then every receive-created candidate again carries an exact outer
coordinate edge.  The open owner-fibre candidate inherits the old edge; the
other three candidates carry the newly resolved edge. -/
theorem receiveResult_coordinateEdgeExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hcoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (observation.phaseCoordinates A strategy hwin)) :
    let result := observation.receiveResult A strategy hwin
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin result.1.1.openControl.2 ∧
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
          hwin result.1.1.closedControl.2 ∧
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
          hwin result.2.1.openControl.2 ∧
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin result.2.1.closedControl.2 := by
  cases observation with
  | right phaseData decoded invariant =>
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.right
          phaseData decoded invariant (input := input)
      have hpacket := observation.packet_exactFrom A strategy hwin
      have hnew :
          ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A
            strategy hwin
              (observation.parent A strategy hwin,
                (observation.packet A strategy hwin).successor) :=
        Or.inl ⟨observation.packet A strategy hwin, hpacket, rfl⟩
      simpa [receiveResult,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentRightBoundaryData.successor,
        phaseCoordinates, observation, packet, parent, target] using
          And.intro hcoordinates (And.intro hnew (And.intro hnew hnew))
  | left phaseData rightAbsent decoded invariant =>
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.left
          phaseData rightAbsent decoded invariant (input := input)
      have hpacket := observation.packet_exactFrom A strategy hwin
      have hnew :
          ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A
            strategy hwin
              ((observation.packet A strategy hwin).successor,
                observation.parent A strategy hwin) :=
        Or.inr ⟨observation.packet A strategy hwin, hpacket, rfl⟩
      simpa [receiveResult,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentLeftBoundaryData.successor,
        phaseCoordinates, observation, packet, parent, target] using
          And.intro hnew (And.intro hnew
            (And.intro hcoordinates hnew))

/-- Both process-one meanings installed by the exact-closing receive fork
retain only exact staged packets. -/
theorem exactClosingRecvForkOne_packetExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      one input.1 two input.2
    ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        fork.1.closedControl := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_packetExact A strategy hwin
  simpa [FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne,
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
    profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive] using
      And.intro hall.1 hall.2.1

/-- Process-two mirror of `exactClosingRecvForkOne_packetExact`. -/
theorem exactClosingRecvForkTwo_packetExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      two input.2 one input.1
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        fork.1.closedControl := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_packetExact A strategy hwin
  simpa [FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo,
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
    profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive] using
      And.intro hall.2.2.1 hall.2.2.2

/-- The process-one acknowledgement fork preserves complete delayed-edge
provenance in both of its meanings. -/
theorem exactClosingRecvForkOne_deferredExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      one input.1 two input.2
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin fork.1.closedControl := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_deferredExact A strategy hwin
  simpa [FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne,
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
    profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive] using
      And.intro hall.1 hall.2.1

/-- Process-two mirror of `exactClosingRecvForkOne_deferredExact`. -/
theorem exactClosingRecvForkTwo_deferredExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      two input.2 one input.1
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin fork.1.closedControl := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_deferredExact A strategy hwin
  simpa [FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo,
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
    profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive] using
      And.intro hall.2.2.1 hall.2.2.2

/-- Direct semantic receive at process one selects the exact open candidate. -/
theorem openRecvOne_deferredExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
          hwin one input.1 two input.2).1 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_deferredExact A strategy hwin
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    using hall.1

/-- Direct semantic receive at process two selects the exact open candidate. -/
theorem openRecvTwo_deferredExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
          hwin two input.2 one input.1).1 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_deferredExact A strategy hwin
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    using hall.2.2.1

/-- A simultaneous semantic receive selects the exact closed candidates at
both endpoints. -/
theorem close_deferredExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let next :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        input.1 two input.2
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin next.1 ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin next.2 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_deferredExact A strategy hwin
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive] using
    And.intro hall.2.1 hall.2.2.2

theorem openRecvOne_coordinateAligned
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneCoordinateAligned A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
          hwin one input.1 two input.2).1 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_coordinateAligned A strategy hwin
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    using hall.1

theorem openRecvTwo_coordinateAligned
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoCoordinateAligned A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
          hwin two input.2 one input.1).1 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_coordinateAligned A strategy hwin
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    using hall.2.2.1

theorem close_coordinateAligned
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let next :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        input.1 two input.2
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
      strategy hwin next.1 next.2 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_coordinateAligned A strategy hwin
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive,
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned] using
      And.intro hall.2.1 hall.2.2.2

theorem openRecvOne_coordinateEdgeExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hphase :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (observation.phaseCoordinates A strategy hwin)) :
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1 two input.2).1.2 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_coordinateEdgeExact A strategy hwin
    hphase
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    using hall.1

theorem openRecvTwo_coordinateEdgeExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hphase :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (observation.phaseCoordinates A strategy hwin)) :
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2 one input.1).1.2 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_coordinateEdgeExact A strategy hwin
    hphase
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    using hall.2.2.1

theorem close_coordinateEdgeExact
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hphase :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (observation.phaseCoordinates A strategy hwin)) :
    let next :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        input.1 two input.2
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
      strategy hwin next.1 next.2 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have hall := observation.receiveResult_coordinateEdgeExact A strategy hwin
    hphase
  simpa [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive,
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact] using
      And.intro hall.2.1 hall.2.2.2

/-- A strict-right round can create a pending/pending pair only from a
left-oriented receive.  In that case the newly open process-two fibre stores
the active left state already selected by process one's pending fibre, so the
two second coordinates agree. -/
theorem strictRight_pendingCoordinateCoherent
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one two) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent A
      strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one input.1).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
          hwin two input.2 one input.1).1 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have halignedOne := haligned.1
  cases observation with
  | right phaseData decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive,
        receiveResult,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent]
  | left phaseData rightAbsent decoded invariant =>
      rcases one with ⟨oneBase, oneCoordinates⟩
      cases oneBase with
      | inl oneBridge =>
          simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
            profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive,
            receiveResult,
            ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent]
      | inr pendingOne =>
          have hactive : oneCoordinates.2 = phaseData.1.1 := by
            rcases two with ⟨twoBase, twoCoordinates⟩
            cases twoBase with
            | inl twoBridge =>
                cases twoBridge with
                | inl stagedTwo =>
                    simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                      at decoded
                | inr installed =>
                    obtain ⟨leftOwner, rightTemplate, hinstalled, hphase⟩ :=
                      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
                        A strategy hwin pendingOne installed oneCoordinates
                          twoCoordinates phaseData decoded
                    rw [hphase]
                    exact halignedOne
            | inr pendingTwo =>
                have hphase :=
                  phaseCoordinates_eq_mixed_of_fibreFibre A strategy hwin
                    pendingOne pendingTwo oneCoordinates twoCoordinates
                      halignedOne haligned.2
                        (.left phaseData rightAbsent decoded invariant)
                          (input := input)
                exact (congrArg Prod.snd hphase).symm
          simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
            profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive,
            receiveResult,
            ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent,
            hactive]

/-- Mirrored preservation for a strict-left round.  A new process-one fibre
can coexist with an old process-two fibre only after a right-oriented
receive, and then their first coordinates are the same active right state. -/
theorem strictLeft_pendingCoordinateCoherent
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one two) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent A
      strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
          hwin one input.1 two input.2).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two input.2).1 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  have halignedTwo := haligned.2
  cases observation with
  | left phaseData rightAbsent decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive,
        receiveResult,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
        ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent]
  | right phaseData decoded invariant =>
      rcases two with ⟨twoBase, twoCoordinates⟩
      cases twoBase with
      | inl twoBridge =>
          simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
            profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive,
            receiveResult,
            ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent]
      | inr pendingTwo =>
          have hactive : phaseData.1.1 = twoCoordinates.1 := by
            rcases one with ⟨oneBase, oneCoordinates⟩
            cases oneBase with
            | inl oneBridge =>
                cases oneBridge with
                | inl stagedOne =>
                    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                      at decoded
                | inr installed =>
                    obtain ⟨rightOwner, leftTemplate, hinstalled, hphase⟩ :=
                      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
                        A strategy hwin installed pendingTwo oneCoordinates
                          twoCoordinates phaseData decoded
                    rw [hphase]
                    exact halignedTwo.symm
            | inr pendingOne =>
                have hphase :=
                  phaseCoordinates_eq_mixed_of_fibreFibre A strategy hwin
                    pendingOne pendingTwo oneCoordinates twoCoordinates
                      haligned.1 halignedTwo
                        (.right phaseData decoded invariant) (input := input)
                exact congrArg Prod.fst hphase
          simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
            profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive,
            receiveResult,
            ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent,
            hactive]

/-- Closing both receive candidates never leaves two pending fibres: the
closed successor is installed as an explicit bridge at one endpoint. -/
theorem close_pendingCoordinateCoherent
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let next :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        input.1 two input.2
    ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent A
      strategy hwin next.1 next.2 := by
  have hreceive := observation.boundaryReceive?_eq A strategy hwin
  cases observation <;>
    simp [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive,
      receiveResult,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent]

/-- Fixed-fibre control data pins both the observed parent and the resolver
packet successor to that same key. -/
theorem atKey
    (key : RootKey A strategy)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two) :
    (observation.parent A strategy hwin).AtKey A strategy hwin key ∧
      (observation.packet A strategy hwin).AtKey A strategy hwin key := by
  cases observation with
  | right phaseData decoded invariant =>
      have hdata :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_atKey A strategy
          hwin key one two phaseData hone htwo decoded
      exact ⟨hdata.1, hdata.1⟩
  | left phaseData rightAbsent decoded invariant =>
      have hdata :=
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_atKey A strategy
          hwin key one two phaseData hone htwo decoded
      exact ⟨hdata.1, hdata.1⟩

/-! ## Committed simultaneous boundaries -/

/-- A simultaneous round commits the packet computed by the selected
receiver: the closed controls decode in the opposite orientation, and the
new active parent is literally the packet successor.  This is the first
non-speculative policy edge extracted from the acknowledged controller. -/
theorem exists_both_successor
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input) :
    let result :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        input.1 two input.2
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin result.1 result.2 input,
      nextObservation.side A strategy hwin =
          (observation.side A strategy hwin).other ∧
        nextObservation.parent A strategy hwin =
          (observation.packet A strategy hwin).successor := by
  cases observation with
  | right phaseData decoded invariant =>
      obtain ⟨move, hmove, hnextInvariant⟩ :=
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant.afterOwnerFibreBoth
          A strategy hwin phaseData invariant input
      let receiveResult :=
        phaseData.ownerFibreReceive A strategy hwin input
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two input = some receiveResult := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, decoded,
          receiveResult]
      have hleftDecode :
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
              receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl =
            some
              (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
        simpa only [receiveResult] using
          phaseData.ownerFibreClose_decodes_left A strategy hwin input move
            hmove
      have hrightReject :
          profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy
              hwin receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl = none := by
        simpa only [receiveResult] using
          phaseData.ownerFibreClose_rejects_right A strategy hwin input move
            hmove
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      refine ⟨.left
        (phaseData.afterOwnerFibreBoth A strategy hwin input move)
          hrightReject hleftDecode hnextInvariant, rfl, ?_⟩
      rfl
  | left phaseData rightAbsent decoded invariant =>
      obtain ⟨move, hmove, hnextInvariant⟩ :=
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant.afterOwnerFibreBoth
          A strategy hwin phaseData invariant input
      let receiveResult :=
        phaseData.ownerFibreReceive A strategy hwin input
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two input = some receiveResult := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, rightAbsent,
          decoded, receiveResult]
      have hrightDecode :
          profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy
              hwin receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl =
            some
              (phaseData.afterOwnerFibreBoth A strategy hwin input move) := by
        simpa only [receiveResult] using
          phaseData.ownerFibreClose_decodes_right A strategy hwin input move
            hmove
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      refine ⟨.right
        (phaseData.afterOwnerFibreBoth A strategy hwin input move)
          hrightDecode hnextInvariant, rfl, ?_⟩
      rfl

/-- Simultaneous close as a uniform committed edge, reindexed by the input
used for the next observation. -/
theorem exists_both_committedEdge
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (nextInput : In₁ × In₂) :
    let result :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        input.1 two input.2
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin result.1 result.2 nextInput,
      CommittedEdge A strategy hwin observation nextObservation := by
  dsimp only
  obtain ⟨sameInputObservation, hside, hparent⟩ :=
    observation.exists_both_successor A strategy hwin
  let nextObservation :=
    sameInputObservation.reinput A strategy hwin nextInput
  refine ⟨nextObservation, observation.packet A strategy hwin,
    observation.packet_exactFrom A strategy hwin, ?_, ?_⟩
  · simpa only [nextObservation, reinput_parent] using hparent
  · simpa only [nextObservation, reinput_side] using hside

/-- A strict-left reversal commits the packet retained by an
installed/staged right boundary.  Unlike the speculative packet computed in
the present receive, `oldPacket` is consumed by the nonreceiving second
endpoint; the decoder then exposes its successor as the next active parent. -/
theorem exists_strictLeft_staged_successor
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates))
    (hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy
        hwin
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        input.1
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates)
        input.2).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates)
        input.2).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo input,
      nextObservation.side A strategy hwin = .left ∧
        nextObservation.parent A strategy hwin = oldPacket.successor ∧
        oldPacket.ExactFrom A strategy hwin rightState := by
  dsimp only
  have hpacket : oldPacket.ExactFrom A strategy hwin rightState := by
    exact hpacketExact oldPacket rfl
  cases observation with
  | right phaseData decoded invariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              (.inl
                (.inr
                  (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
                oneCoordinates)
              (.inl (.inl (rightState, rightReceiver, some oldPacket)),
                twoCoordinates)
              input =
            some (phaseData.ownerFibreReceive A strategy hwin input) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, decoded]
      let pendingNext :=
        (phaseData.1.ownerFibreReceive A strategy hwin phaseData.2.1
          phaseData.2.2 input).1.openControl
      have hone :
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
            hwin
              (.inl
                (.inr
                  (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
                oneCoordinates)
              input.1
              (.inl (.inl (rightState, rightReceiver, some oldPacket)),
                twoCoordinates)
              input.2).1 =
            (.inr pendingNext, (phaseData.1.1, phaseData.2.1)) := by
        rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
        rfl
      let leftAdvancedOwner :=
        (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove false
          (leftMove.memberController A false).initial input.2).2
      let installedNext :
          ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin :=
        (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩, rightReceiver)
      have htwo :
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy
            hwin
              (.inl (.inl (rightState, rightReceiver, some oldPacket)),
                twoCoordinates)
              input.2).1 =
            (.inl (.inr installedNext), twoCoordinates) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
          profiledRawJointRecurrentRightToLeftBridgeNoRecv, hleftMove,
          installedNext, leftAdvancedOwner]
      have hnext :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft A
          strategy hwin _ _ hoperational input.1 input.2
      rw [hone, htwo] at hnext
      rw [hone, htwo]
      cases hnext.selected with
      | right nextData nextDecoded nextInvariant =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at nextDecoded
      | left nextData rightAbsent nextDecoded nextInvariant =>
          let nextObservation :
              ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
                strategy hwin
                  (.inr pendingNext, (phaseData.1.1, phaseData.2.1))
                  (.inl (.inr installedNext), twoCoordinates) input :=
            .left nextData rightAbsent nextDecoded nextInvariant
          refine ⟨nextObservation, rfl, ?_, hpacket⟩
          simpa only [installedNext] using
            (parent_eq_of_fibreInstalled A strategy hwin pendingNext
              installedNext (phaseData.1.1, phaseData.2.1) twoCoordinates
                nextObservation)
  | left phaseData rightAbsent decoded invariant =>
      rw [profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged
        A strategy hwin rightState rightReceiver rightOwner leftTemplate
          oldPacket leftMove hleftMove oneCoordinates twoCoordinates] at rightAbsent
      simp at rightAbsent

/-- Mirrored strict-right commitment of the packet retained by a
staged/installed left boundary. -/
theorem exists_strictRight_staged_successor
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates)
          input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates))
    (hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy
        hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        input.1).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates)
        input.2
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        input.1).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo input,
      nextObservation.side A strategy hwin = .right ∧
        nextObservation.parent A strategy hwin = oldPacket.successor ∧
        oldPacket.ExactFrom A strategy hwin leftState := by
  dsimp only
  have hpacket : oldPacket.ExactFrom A strategy hwin leftState := by
    exact hpacketExact oldPacket rfl
  cases observation with
  | right phaseData decoded invariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
  | left phaseData rightAbsent decoded invariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              (.inl (.inl (leftState, leftReceiver, some oldPacket)),
                oneCoordinates)
              (.inl
                (.inr
                  (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
                twoCoordinates)
              input =
            some (phaseData.ownerFibreReceive A strategy hwin input) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, rightAbsent,
          decoded]
      let pendingNext :=
        (phaseData.1.ownerFibreReceive A strategy hwin phaseData.2.1
          phaseData.2.2 input).1.openControl
      have htwo :
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
            hwin
              (.inl
                (.inr
                  (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
                twoCoordinates)
              input.2
              (.inl (.inl (leftState, leftReceiver, some oldPacket)),
                oneCoordinates)
              input.1).1 =
            (.inr pendingNext, (phaseData.2.1, phaseData.1.1)) := by
        rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
        rfl
      let rightAdvancedOwner :=
        (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove false
          (rightMove.memberController A false).initial input.1).2
      let installedNext :
          ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin :=
        (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩, leftReceiver)
      have hone :
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy
            hwin
              (.inl (.inl (leftState, leftReceiver, some oldPacket)),
                oneCoordinates)
              input.1).1 =
            (.inl (.inr installedNext), oneCoordinates) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
          profiledRawJointRecurrentLeftToRightBridgeNoRecv, hrightMove,
          installedNext, rightAdvancedOwner]
      have hnext :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight A
          strategy hwin _ _ hoperational input.1 input.2
      rw [hone, htwo] at hnext
      rw [hone, htwo]
      cases hnext.selected with
      | right nextData nextDecoded nextInvariant =>
          let nextObservation :
              ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
                strategy hwin
                  (.inl (.inr installedNext), oneCoordinates)
                  (.inr pendingNext, (phaseData.2.1, phaseData.1.1)) input :=
            .right nextData nextDecoded nextInvariant
          refine ⟨nextObservation, rfl, ?_, hpacket⟩
          simpa only [installedNext] using
            (parent_eq_of_installedFibre A strategy hwin installedNext
              pendingNext oneCoordinates (phaseData.2.1, phaseData.1.1)
                nextObservation)
      | left nextData rightAbsent nextDecoded nextInvariant =>
          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at nextDecoded

/-- Peer-independent strict-left commitment.  The process-one control may be
an installed bridge or an unresolved owner fibre; only the staged process-two
packet is consumed.  Thus this theorem covers both operational reversal
shapes. -/
theorem exists_strictLeft_staged_successor_of_anyPeer
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.2.2 = some leftMove)
    (twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates))
    (hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy
        hwin
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates)
        input.2).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates)
        input.2).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo input,
      nextObservation.side A strategy hwin = .left ∧
        nextObservation.parent A strategy hwin = oldPacket.successor ∧
        oldPacket.ExactFrom A strategy hwin rightState := by
  dsimp only
  have hpacket : oldPacket.ExactFrom A strategy hwin rightState := by
    exact hpacketExact oldPacket rfl
  cases observation with
  | right phaseData decoded invariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one
              (.inl (.inl (rightState, rightReceiver, some oldPacket)),
                twoCoordinates)
              input =
            some (phaseData.ownerFibreReceive A strategy hwin input) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, decoded]
      let pendingNext :=
        (phaseData.1.ownerFibreReceive A strategy hwin phaseData.2.1
          phaseData.2.2 input).1.openControl
      have hone :
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
            hwin one input.1
              (.inl (.inl (rightState, rightReceiver, some oldPacket)),
                twoCoordinates)
              input.2).1 =
            (.inr pendingNext, (phaseData.1.1, phaseData.2.1)) := by
        rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
        rfl
      let leftAdvancedOwner :=
        (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove false
          (leftMove.memberController A false).initial input.2).2
      let installedNext :
          ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin :=
        (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩, rightReceiver)
      have htwo :
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy
            hwin
              (.inl (.inl (rightState, rightReceiver, some oldPacket)),
                twoCoordinates)
              input.2).1 =
            (.inl (.inr installedNext), twoCoordinates) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
          profiledRawJointRecurrentRightToLeftBridgeNoRecv, hleftMove,
          installedNext, leftAdvancedOwner]
      have hnext :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft A
          strategy hwin _ _ hoperational input.1 input.2
      rw [hone, htwo] at hnext
      rw [hone, htwo]
      cases hnext.selected with
      | right nextData nextDecoded nextInvariant =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at nextDecoded
      | left nextData rightAbsent nextDecoded nextInvariant =>
          let nextObservation :
              ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
                strategy hwin
                  (.inr pendingNext, (phaseData.1.1, phaseData.2.1))
                  (.inl (.inr installedNext), twoCoordinates) input :=
            .left nextData rightAbsent nextDecoded nextInvariant
          refine ⟨nextObservation, rfl, ?_, hpacket⟩
          simpa only [installedNext] using
            (parent_eq_of_fibreInstalled A strategy hwin pendingNext
              installedNext (phaseData.1.1, phaseData.2.1) twoCoordinates
                nextObservation)
  | left phaseData rightAbsent decoded invariant =>
      rcases one with ⟨oneBase, oneCoordinates⟩
      cases oneBase with
      | inl bridge =>
          cases bridge <;>
            simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded
      | inr pending =>
          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at decoded

/-- Peer-independent strict-right mirror.  It covers both staged/installed
and staged/fibre operational reversal shapes. -/
theorem exists_strictRight_staged_successor_of_anyPeer
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.2.1 = some rightMove)
    (oneCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          two input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        two)
    (hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy
        hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        input.1).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        input.1).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo input,
      nextObservation.side A strategy hwin = .right ∧
        nextObservation.parent A strategy hwin = oldPacket.successor ∧
        oldPacket.ExactFrom A strategy hwin leftState := by
  dsimp only
  have hpacket : oldPacket.ExactFrom A strategy hwin leftState := by
    exact hpacketExact oldPacket rfl
  cases observation with
  | right phaseData decoded invariant =>
      rcases two with ⟨twoBase, twoCoordinates⟩
      cases twoBase with
      | inl bridge =>
          cases bridge <;>
            simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
      | inr pending =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at decoded
  | left phaseData rightAbsent decoded invariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              (.inl (.inl (leftState, leftReceiver, some oldPacket)),
                oneCoordinates)
              two input =
            some (phaseData.ownerFibreReceive A strategy hwin input) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, rightAbsent,
          decoded]
      let pendingNext :=
        (phaseData.1.ownerFibreReceive A strategy hwin phaseData.2.1
          phaseData.2.2 input).1.openControl
      have htwo :
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
            hwin two input.2
              (.inl (.inl (leftState, leftReceiver, some oldPacket)),
                oneCoordinates)
              input.1).1 =
            (.inr pendingNext, (phaseData.2.1, phaseData.1.1)) := by
        rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
        rfl
      let rightAdvancedOwner :=
        (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove false
          (rightMove.memberController A false).initial input.1).2
      let installedNext :
          ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin :=
        (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩, leftReceiver)
      have hone :
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy
            hwin
              (.inl (.inl (leftState, leftReceiver, some oldPacket)),
                oneCoordinates)
              input.1).1 =
            (.inl (.inr installedNext), oneCoordinates) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
          profiledRawJointRecurrentLeftToRightBridgeNoRecv, hrightMove,
          installedNext, rightAdvancedOwner]
      have hnext :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight A
          strategy hwin _ _ hoperational input.1 input.2
      rw [hone, htwo] at hnext
      rw [hone, htwo]
      cases hnext.selected with
      | right nextData nextDecoded nextInvariant =>
          let nextObservation :
              ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
                strategy hwin
                  (.inl (.inr installedNext), oneCoordinates)
                  (.inr pendingNext, (phaseData.2.1, phaseData.1.1)) input :=
            .right nextData nextDecoded nextInvariant
          refine ⟨nextObservation, rfl, ?_, hpacket⟩
          simpa only [installedNext] using
            (parent_eq_of_installedFibre A strategy hwin installedNext
              pendingNext oneCoordinates (phaseData.2.1, phaseData.1.1)
                nextObservation)
      | left nextData rightAbsent nextDecoded nextInvariant =>
          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at nextDecoded

/-- Uniform committed-edge form of peer-independent strict-left packet
consumption. -/
theorem exists_strictLeft_staged_committedEdge_of_anyPeer
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.2.2 = some leftMove)
    (twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates))
    (hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy
        hwin
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates))
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates)
        input.2).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates)
        input.2).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      CommittedEdge A strategy hwin observation nextObservation := by
  dsimp only
  obtain ⟨sameInputObservation, hside, hparent, hexact⟩ :=
    exists_strictLeft_staged_successor_of_anyPeer A strategy hwin one
      rightState rightReceiver oldPacket leftMove hleftMove twoCoordinates
        observation hoperational hpacketExact
  have hcurrent :=
    parent_eq_of_rightStaged A strategy hwin one rightState rightReceiver
      oldPacket leftMove hleftMove twoCoordinates observation
  let nextObservation :=
    sameInputObservation.reinput A strategy hwin nextInput
  refine ⟨nextObservation, oldPacket, ?_, ?_, ?_⟩
  · rw [hcurrent.2]
    exact hexact
  · simpa only [nextObservation, reinput_parent] using hparent
  · simp only [nextObservation, reinput_side, hside, hcurrent.1]
    rfl

/-- Uniform committed-edge form of peer-independent strict-right packet
consumption. -/
theorem exists_strictRight_staged_committedEdge_of_anyPeer
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.2.1 = some rightMove)
    (oneCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          two input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        two)
    (hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy
        hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates))
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        input.1).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        input.1).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      CommittedEdge A strategy hwin observation nextObservation := by
  dsimp only
  obtain ⟨sameInputObservation, hside, hparent, hexact⟩ :=
    exists_strictRight_staged_successor_of_anyPeer A strategy hwin leftState
      leftReceiver oldPacket rightMove hrightMove oneCoordinates two
        observation hoperational hpacketExact
  have hcurrent :=
    parent_eq_of_leftStaged A strategy hwin leftState leftReceiver oldPacket
      rightMove hrightMove oneCoordinates two observation
  let nextObservation :=
    sameInputObservation.reinput A strategy hwin nextInput
  refine ⟨nextObservation, oldPacket, ?_, ?_, ?_⟩
  · rw [hcurrent.2]
    exact hexact
  · simpa only [nextObservation, reinput_parent] using hparent
  · simp only [nextObservation, reinput_side, hside, hcurrent.1]
    rfl

/-! ## Orientation-opposed strict rounds with unresolved fibres -/

/-- If a left-oriented observation has an unresolved process-one fibre, a
strict-right round selects the dormant right endpoint of the current phase.
This is a coordinate crossing, not necessarily a forward policy edge. -/
theorem exists_strictRight_pending_phaseFirst
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (oneCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin (.inr pendingOne, oneCoordinates) two input)
    (hside : observation.side A strategy hwin = .left)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        (.inr pendingOne, oneCoordinates) two)
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) input.1).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2 (.inr pendingOne, oneCoordinates) input.1).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      nextObservation.side A strategy hwin = .right ∧
        nextObservation.parent A strategy hwin =
          (observation.phaseCoordinates A strategy hwin).1 := by
  dsimp only
  cases observation with
  | right phaseData decoded invariant =>
      simp only [side] at hside
      cases hside
  | left phaseData rightAbsent decoded invariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              (.inr pendingOne, oneCoordinates) two input =
            some (phaseData.ownerFibreReceive A strategy hwin input) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, rightAbsent,
          decoded]
      let nextPendingOne :=
        (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
          pendingOne input.1).1
      let nextPendingTwo :=
        (phaseData.1.ownerFibreReceive A strategy hwin phaseData.2.1
          phaseData.2.2 input).1.openControl
      have hone :
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy
            hwin (.inr pendingOne, oneCoordinates) input.1).1 =
            (.inr nextPendingOne, oneCoordinates) := by
        rfl
      have htwo :
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
            hwin two input.2 (.inr pendingOne, oneCoordinates) input.1).1 =
            (.inr nextPendingTwo, (phaseData.2.1, phaseData.1.1)) := by
        rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
        rfl
      have hnext :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight A
          strategy hwin _ _ hoperational input.1 input.2
      rw [hone, htwo] at hnext
      rw [hone, htwo]
      cases hnext.selected with
      | right nextData nextDecoded nextInvariant =>
          let nextObservation :
              ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
                strategy hwin (.inr nextPendingOne, oneCoordinates)
                  (.inr nextPendingTwo, (phaseData.2.1, phaseData.1.1))
                    nextInput :=
            .right nextData nextDecoded nextInvariant
          refine ⟨nextObservation, rfl, ?_⟩
          have hstates :=
            profiledRawJointRecurrentOwnerFibreMakeRight?_states A strategy
              hwin _ _ _ _ _ _ nextData (by
                simpa only [
                  profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                  nextPendingTwo,
                  ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
                  profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
                  FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
                  profiledRawJointRecurrentLeftToRightOwnerFibreReceiver,
                  Bool.not_false, Bool.or_true, if_pos] using nextDecoded)
          simpa only [nextObservation, parent, phaseCoordinates,
            nextPendingTwo,
            ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
            profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
            FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
            profiledRawJointRecurrentLeftToRightOwnerFibreReceiver, if_neg]
              using hstates.1
      | left nextData nextRightAbsent nextDecoded nextInvariant =>
          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
            nextPendingTwo,
            ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
            profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
            FiniteAcknowledgedDelayedCarrier.deferredMemberFork] at nextDecoded

/-- Complete orientation-opposed strict-right classification.  Whether the
left phase is represented by a staged bridge or by a pending fibre, the next
active parent is exactly its dormant right coordinate. -/
theorem exists_strictRight_phaseFirst_of_left
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .left)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (hdeferredOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin one)
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one input.1).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2 one input.1).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      nextObservation.side A strategy hwin = .right ∧
        nextObservation.parent A strategy hwin =
          (observation.phaseCoordinates A strategy hwin).1 := by
  dsimp only
  rcases one with ⟨oneBase, oneCoordinates⟩
  cases oneBase with
  | inl oneBridge =>
      cases oneBridge with
      | inl staged =>
          rcases staged with ⟨leftState, leftReceiver, stored⟩
          cases stored with
          | none =>
              cases observation with
              | right phaseData decoded invariant =>
                  simp only [side] at hside
                  cases hside
              | left phaseData rightAbsent decoded invariant =>
                  rcases two with ⟨twoBase, twoCoordinates⟩
                  cases twoBase with
                  | inl twoBridge =>
                      cases twoBridge <;>
                        simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                          at decoded
                  | inr pendingTwo =>
                      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                        at decoded
          | some oldPacket =>
              cases hrightMove : oldPacket.successor.2.1.2.1 with
              | none =>
                  cases observation with
                  | right phaseData decoded invariant =>
                      simp only [side] at hside
                      cases hside
                  | left phaseData rightAbsent decoded invariant =>
                      rcases two with ⟨twoBase, twoCoordinates⟩
                      cases twoBase with
                      | inl twoBridge =>
                          cases twoBridge <;>
                            simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                              hrightMove] at decoded
                      | inr pendingTwo =>
                          simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                            hrightMove] at decoded
              | some rightMove =>
                  have hpacketExact :
                      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact
                        A strategy hwin
                          (.inl (.inl
                            (leftState, leftReceiver, some oldPacket)),
                            oneCoordinates) :=
                    hdeferredOne
                  obtain ⟨sameInputObservation, hnextSide, hnextParent,
                      hexact⟩ :=
                    exists_strictRight_staged_successor_of_anyPeer A strategy
                      hwin leftState leftReceiver oldPacket rightMove
                        hrightMove oneCoordinates two observation hoperational
                          hpacketExact
                  have hphase :=
                    phaseCoordinates_eq_of_leftStaged A strategy hwin
                      leftState leftReceiver oldPacket rightMove hrightMove
                        oneCoordinates two observation
                  let nextObservation :=
                    sameInputObservation.reinput A strategy hwin nextInput
                  refine ⟨nextObservation, ?_, ?_⟩
                  · simpa only [nextObservation, reinput_side] using hnextSide
                  · have hfirst := congrArg Prod.fst hphase
                    simpa only [nextObservation, reinput_parent] using
                      hnextParent.trans hfirst.symm
      | inr installed =>
          cases observation with
          | right phaseData decoded invariant =>
              simp only [side] at hside
              cases hside
          | left phaseData rightAbsent decoded invariant =>
              rcases two with ⟨twoBase, twoCoordinates⟩
              cases twoBase with
              | inl twoBridge =>
                  cases twoBridge <;>
                    simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                      at decoded
              | inr pendingTwo =>
                  simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                    at decoded
  | inr pendingOne =>
      exact
        exists_strictRight_pending_phaseFirst A strategy hwin pendingOne
          oneCoordinates two observation hside hoperational nextInput

/-- Pending-fibre half of the mirrored opposed transition.  The open
candidate can leave the decoder right-oriented (a neutral parent step) or
make it left-oriented (a crossing to the dormant left coordinate). -/
theorem exists_strictLeft_pending_neutralOrPhaseSecond
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one (.inr pendingTwo, twoCoordinates) input)
    (hside : observation.side A strategy hwin = .right)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one (.inr pendingTwo, twoCoordinates))
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one (.inr pendingTwo, twoCoordinates))
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1 (.inr pendingTwo, twoCoordinates) input.2).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) input.2).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      (nextObservation.side A strategy hwin = .right ∧
          nextObservation.parent A strategy hwin =
            observation.parent A strategy hwin) ∨
        (nextObservation.side A strategy hwin = .left ∧
          nextObservation.parent A strategy hwin =
            (observation.phaseCoordinates A strategy hwin).2) := by
  dsimp only
  have hcurrentParent :=
    observation.parent_eq_twoFirst_of_right_pendingTwo A strategy hwin one
      pendingTwo twoCoordinates haligned hside
  cases observation with
  | left phaseData rightAbsent decoded invariant =>
      simp only [side] at hside
      cases hside
  | right phaseData decoded invariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one (.inr pendingTwo, twoCoordinates) input =
            some (phaseData.ownerFibreReceive A strategy hwin input) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, decoded]
      let nextPendingOne :=
        (phaseData.1.ownerFibreReceive A strategy hwin phaseData.2.1
          phaseData.2.2 input).1.openControl
      let nextPendingTwo :=
        (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
          pendingTwo input.2).1
      have hone :
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
            hwin one input.1 (.inr pendingTwo, twoCoordinates) input.2).1 =
            (.inr nextPendingOne, (phaseData.1.1, phaseData.2.1)) := by
        rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
        rfl
      have htwo :
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy
            hwin (.inr pendingTwo, twoCoordinates) input.2).1 =
            (.inr nextPendingTwo, twoCoordinates) := by
        rfl
      have hnextOperational :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft A
          strategy hwin _ _ hoperational input.1 input.2
      have hnextAlignedOne :=
        (ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.right
          phaseData decoded invariant (input := input)
          ).openRecvOne_coordinateAligned A strategy hwin
      have hnextAlignedTwo :=
        haligned.2.noRecv A strategy hwin
          (.inr pendingTwo, twoCoordinates) input.2
      rw [hone, htwo] at hnextOperational
      rw [hone] at hnextAlignedOne
      rw [htwo] at hnextAlignedTwo
      rw [hone, htwo]
      cases hnextOperational.selected with
      | right nextData nextDecoded nextInvariant =>
          let nextObservation :
              ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
                strategy hwin
                  (.inr nextPendingOne, (phaseData.1.1, phaseData.2.1))
                  (.inr nextPendingTwo, twoCoordinates) nextInput :=
            .right nextData nextDecoded nextInvariant
          have hphase :=
            phaseCoordinates_eq_mixed_of_fibreFibre A strategy hwin
              nextPendingOne nextPendingTwo
                (phaseData.1.1, phaseData.2.1) twoCoordinates
                  hnextAlignedOne hnextAlignedTwo nextObservation
          refine ⟨nextObservation, Or.inl ⟨rfl, ?_⟩⟩
          have hnextParent :
              nextObservation.parent A strategy hwin = twoCoordinates.1 := by
            simpa only [nextObservation, phaseCoordinates, parent] using
              congrArg Prod.fst hphase
          exact hnextParent.trans hcurrentParent.symm
      | left nextData nextRightAbsent nextDecoded nextInvariant =>
          let nextObservation :
              ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
                strategy hwin
                  (.inr nextPendingOne, (phaseData.1.1, phaseData.2.1))
                  (.inr nextPendingTwo, twoCoordinates) nextInput :=
            .left nextData nextRightAbsent nextDecoded nextInvariant
          have hphase :=
            phaseCoordinates_eq_mixed_of_fibreFibre A strategy hwin
              nextPendingOne nextPendingTwo
                (phaseData.1.1, phaseData.2.1) twoCoordinates
                  hnextAlignedOne hnextAlignedTwo nextObservation
          refine ⟨nextObservation, Or.inr ⟨rfl, ?_⟩⟩
          simpa only [nextObservation, phaseCoordinates, parent] using
            congrArg Prod.snd hphase

/-- Complete orientation-opposed strict-left classification.  An explicit
staged packet crosses to its successor.  An unresolved fibre either keeps
the right parent or crosses to the dormant left coordinate, according to its
member bit. -/
theorem exists_strictLeft_neutralOrPhaseSecond_of_right
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .right)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (hdeferredTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin two)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one two)
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1 two input.2).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two input.2).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      (nextObservation.side A strategy hwin = .right ∧
          nextObservation.parent A strategy hwin =
            observation.parent A strategy hwin) ∨
        (nextObservation.side A strategy hwin = .left ∧
          nextObservation.parent A strategy hwin =
            (observation.phaseCoordinates A strategy hwin).2) := by
  dsimp only
  rcases two with ⟨twoBase, twoCoordinates⟩
  cases twoBase with
  | inl twoBridge =>
      cases twoBridge with
      | inl staged =>
          rcases staged with ⟨rightState, rightReceiver, stored⟩
          cases stored with
          | none =>
              cases observation with
              | right phaseData decoded invariant =>
                  rcases one with ⟨oneBase, oneCoordinates⟩
                  cases oneBase with
                  | inl oneBridge =>
                      cases oneBridge <;>
                        simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                          at decoded
                  | inr pendingOne =>
                      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                        at decoded
              | left phaseData rightAbsent decoded invariant =>
                  simp only [side] at hside
                  cases hside
          | some oldPacket =>
              cases hleftMove : oldPacket.successor.2.1.2.2 with
              | none =>
                  cases observation with
                  | right phaseData decoded invariant =>
                      rcases one with ⟨oneBase, oneCoordinates⟩
                      cases oneBase with
                      | inl oneBridge =>
                          cases oneBridge <;>
                            simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                              hleftMove] at decoded
                      | inr pendingOne =>
                          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                            hleftMove] at decoded
                  | left phaseData rightAbsent decoded invariant =>
                      simp only [side] at hside
                      cases hside
              | some leftMove =>
                  have hpacketExact :
                      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact
                        A strategy hwin
                          (.inl (.inl
                            (rightState, rightReceiver, some oldPacket)),
                            twoCoordinates) :=
                    hdeferredTwo
                  obtain ⟨sameInputObservation, hnextSide, hnextParent,
                      hexact⟩ :=
                    exists_strictLeft_staged_successor_of_anyPeer A strategy
                      hwin one rightState rightReceiver oldPacket leftMove
                        hleftMove twoCoordinates observation hoperational
                          hpacketExact
                  have hphase :=
                    phaseCoordinates_eq_of_rightStaged A strategy hwin one
                      rightState rightReceiver oldPacket leftMove hleftMove
                        twoCoordinates observation
                  let nextObservation :=
                    sameInputObservation.reinput A strategy hwin nextInput
                  refine ⟨nextObservation, Or.inr ⟨?_, ?_⟩⟩
                  · simpa only [nextObservation, reinput_side] using hnextSide
                  · have hsecond := congrArg Prod.snd hphase
                    simpa only [nextObservation, reinput_parent] using
                      hnextParent.trans hsecond.symm
      | inr installed =>
          cases observation with
          | right phaseData decoded invariant =>
              rcases one with ⟨oneBase, oneCoordinates⟩
              cases oneBase with
              | inl oneBridge =>
                  cases oneBridge <;>
                    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                      at decoded
              | inr pendingOne =>
                  simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                    at decoded
          | left phaseData rightAbsent decoded invariant =>
              simp only [side] at hside
              cases hside
  | inr pendingTwo =>
      exact
        exists_strictLeft_pending_neutralOrPhaseSecond A strategy hwin one
          pendingTwo twoCoordinates observation hside hoperational haligned
            nextInput

/-! ## Productive adjacent strict rounds -/

/-- If a right-oriented boundary is followed by a strict-right round and
then a strict-left round, the first round stages the observation's exact
packet and the second round commits it.  The middle observation therefore
has the same parent and participates in a genuine `CommittedEdge` to the
post-reversal observation. -/
theorem exists_committedEdge_after_right_left_of_right
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .right)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (nextInput afterInput : In₁ × In₂) :
    let middleOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one input.1).1
    let middleTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2 one input.1).1
    let afterOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        middleOne nextInput.1 middleTwo nextInput.2).1
    let afterTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        middleTwo nextInput.2).1
    ∃ middleObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin middleOne middleTwo nextInput,
      ∃ afterObservation :
          ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
            strategy hwin afterOne afterTwo afterInput,
        middleObservation.side A strategy hwin = .right ∧
          middleObservation.parent A strategy hwin =
            observation.parent A strategy hwin ∧
          CommittedEdge A strategy hwin middleObservation afterObservation := by
  dsimp only
  obtain ⟨receiver, coordinates, hstaged⟩ :=
    observation.openRecvTwo_stages_packet_of_right A strategy hwin hside
  obtain ⟨move, hmove⟩ :=
    observation.packet_leftMove_exists_of_right A strategy hwin hside
  have hmiddleOperational :=
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight A
      strategy hwin one two hoperational input.1 input.2
  rw [hstaged] at hmiddleOperational
  let middleObservation :=
    ofSelected A strategy hwin hmiddleOperational.selected
      (input := nextInput)
  have hmiddle :=
    parent_eq_of_rightStaged A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one input.1).1
      (observation.parent A strategy hwin) receiver
      (observation.packet A strategy hwin) move hmove coordinates
        middleObservation
  have hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy
        hwin
          (.inl (.inl
            (observation.parent A strategy hwin, receiver,
              some (observation.packet A strategy hwin))), coordinates) := by
    exact fun candidate hc ↦ by
      cases Option.some.inj hc
      exact observation.packet_exactFrom A strategy hwin
  obtain ⟨afterObservation, hedge⟩ :=
    exists_strictLeft_staged_committedEdge_of_anyPeer A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one input.1).1
      (observation.parent A strategy hwin) receiver
      (observation.packet A strategy hwin) move hmove coordinates
        middleObservation hmiddleOperational hpacketExact afterInput
  rw [hstaged]
  exact ⟨middleObservation, afterObservation, hmiddle.1, hmiddle.2, hedge⟩

/-- Mirrored productive adjacent strict pair. -/
theorem exists_committedEdge_after_left_right_of_left
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hside : observation.side A strategy hwin = .left)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (nextInput afterInput : In₁ × In₂) :
    let middleOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1 two input.2).1
    let middleTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two input.2).1
    let afterOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        middleOne nextInput.1).1
    let afterTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        middleTwo nextInput.2 middleOne nextInput.1).1
    ∃ middleObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin middleOne middleTwo nextInput,
      ∃ afterObservation :
          ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
            strategy hwin afterOne afterTwo afterInput,
        middleObservation.side A strategy hwin = .left ∧
          middleObservation.parent A strategy hwin =
            observation.parent A strategy hwin ∧
          CommittedEdge A strategy hwin middleObservation afterObservation := by
  dsimp only
  obtain ⟨receiver, coordinates, hstaged⟩ :=
    observation.openRecvOne_stages_packet_of_left A strategy hwin hside
  obtain ⟨move, hmove⟩ :=
    observation.packet_rightMove_exists_of_left A strategy hwin hside
  have hmiddleOperational :=
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft A
      strategy hwin one two hoperational input.1 input.2
  rw [hstaged] at hmiddleOperational
  let middleObservation :=
    ofSelected A strategy hwin hmiddleOperational.selected
      (input := nextInput)
  have hmiddle :=
    parent_eq_of_leftStaged A strategy hwin
      (observation.parent A strategy hwin) receiver
      (observation.packet A strategy hwin) move hmove coordinates
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two input.2).1 middleObservation
  have hpacketExact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy
        hwin
          (.inl (.inl
            (observation.parent A strategy hwin, receiver,
              some (observation.packet A strategy hwin))), coordinates) := by
    exact fun candidate hc ↦ by
      cases Option.some.inj hc
      exact observation.packet_exactFrom A strategy hwin
  obtain ⟨afterObservation, hedge⟩ :=
    exists_strictRight_staged_committedEdge_of_anyPeer A strategy hwin
      (observation.parent A strategy hwin) receiver
      (observation.packet A strategy hwin) move hmove coordinates
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two input.2).1 middleObservation hmiddleOperational hpacketExact
          afterInput
  rw [hstaged]
  exact ⟨middleObservation, afterObservation, hmiddle.1, hmiddle.2, hedge⟩

/-- One-step parent classification for every strict-right round.  A right
phase is parent-neutral; a left phase crosses to its dormant right
coordinate.  In either case the next decoder is right-oriented. -/
theorem exists_strictRight_parentStep
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (hdeferredOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin one)
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one input.1).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2 one input.1).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      nextObservation.side A strategy hwin = .right ∧
        (nextObservation.parent A strategy hwin =
            observation.parent A strategy hwin ∨
          nextObservation.parent A strategy hwin =
            (observation.phaseCoordinates A strategy hwin).1) := by
  cases hside : observation.side A strategy hwin with
  | right =>
      obtain ⟨middleObservation, afterObservation, hmiddleSide,
          hmiddleParent, hedge⟩ :=
        observation.exists_committedEdge_after_right_left_of_right A strategy
          hwin hside hoperational nextInput nextInput
      exact ⟨middleObservation, hmiddleSide, Or.inl hmiddleParent⟩
  | left =>
      obtain ⟨nextObservation, hnextSide, hnextParent⟩ :=
        observation.exists_strictRight_phaseFirst_of_left A strategy hwin
          hside hoperational hdeferredOne nextInput
      exact ⟨nextObservation, hnextSide, Or.inr hnextParent⟩

/-- One-step parent classification for every strict-left round.  A left
phase is parent-neutral.  From a right phase, an unresolved open member can
remain neutral; otherwise the decoder crosses to the dormant left
coordinate. -/
theorem exists_strictLeft_parentStep
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (hdeferredTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin two)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one two)
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1 two input.2).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two input.2).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      nextObservation.parent A strategy hwin =
          observation.parent A strategy hwin ∨
        (nextObservation.side A strategy hwin = .left ∧
          nextObservation.parent A strategy hwin =
            (observation.phaseCoordinates A strategy hwin).2) := by
  cases hside : observation.side A strategy hwin with
  | left =>
      obtain ⟨middleObservation, afterObservation, hmiddleSide,
          hmiddleParent, hedge⟩ :=
        observation.exists_committedEdge_after_left_right_of_left A strategy
          hwin hside hoperational nextInput nextInput
      exact ⟨middleObservation, Or.inl hmiddleParent⟩
  | right =>
      obtain ⟨nextObservation, hneutral | hcross⟩ :=
        observation.exists_strictLeft_neutralOrPhaseSecond_of_right A strategy
          hwin hside hoperational hdeferredTwo haligned nextInput
      · exact ⟨nextObservation, Or.inl hneutral.2⟩
      · exact ⟨nextObservation, Or.inr hcross⟩

/-- Exact orientation-sensitive classification of a strict-right step.  A
right-oriented phase is stationary.  From a left-oriented phase, exactness
of the decoded coordinate edge says precisely whether the crossing is a
forward policy edge or a rollback of one. -/
theorem exists_strictRight_exactParentStep
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (hdeferredOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneDeferredExact A strategy
        hwin one)
    (hphase :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (observation.phaseCoordinates A strategy hwin))
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one input.1).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two input.2 one input.1).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      nextObservation.side A strategy hwin = .right ∧
        ProfiledRawJointRecurrentBankParentStep A strategy hwin
          (observation.parent A strategy hwin)
          (nextObservation.parent A strategy hwin) := by
  dsimp only
  cases hside : observation.side A strategy hwin with
  | right =>
      obtain ⟨middleObservation, afterObservation, hmiddleSide,
          hmiddleParent, hedge⟩ :=
        observation.exists_committedEdge_after_right_left_of_right A strategy
          hwin hside hoperational nextInput nextInput
      exact ⟨middleObservation, hmiddleSide, Or.inl hmiddleParent.symm⟩
  | left =>
      obtain ⟨nextObservation, hnextSide, hnextParent⟩ :=
        observation.exists_strictRight_phaseFirst_of_left A strategy hwin
          hside hoperational hdeferredOne nextInput
      have hactive :
          (observation.phaseCoordinates A strategy hwin).2 =
            observation.parent A strategy hwin := by
        simpa [hside] using observation.phaseCoordinates_active A strategy hwin
      refine ⟨nextObservation, hnextSide, ?_⟩
      rcases hphase with ⟨packet, hexact, hsuccessor⟩ |
          ⟨packet, hexact, hsuccessor⟩
      · refine Or.inr (Or.inr ⟨packet, ?_, ?_⟩)
        · rw [hnextParent]
          exact hexact
        · exact hactive.symm.trans hsuccessor
      · refine Or.inr (Or.inl ⟨packet, ?_, ?_⟩)
        · rw [← hactive]
          exact hexact
        · exact hnextParent.trans hsuccessor

/-- Strict-left mirror of `exists_strictRight_exactParentStep`.  The neutral
pending-member case remains explicit; every non-neutral step is certified as
either a fixed-policy successor or a rollback of one. -/
theorem exists_strictLeft_exactParentStep
    (observation :
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
        strategy hwin one two input)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (hdeferredTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoDeferredExact A strategy
        hwin two)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin one two)
    (hphase :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (observation.phaseCoordinates A strategy hwin))
    (nextInput : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one input.1 two input.2).1
    let nextTwo :=
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two input.2).1
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextOne nextTwo nextInput,
      ProfiledRawJointRecurrentBankParentStep A strategy hwin
        (observation.parent A strategy hwin)
        (nextObservation.parent A strategy hwin) := by
  dsimp only
  cases hside : observation.side A strategy hwin with
  | left =>
      obtain ⟨middleObservation, afterObservation, hmiddleSide,
          hmiddleParent, hedge⟩ :=
        observation.exists_committedEdge_after_left_right_of_left A strategy
          hwin hside hoperational nextInput nextInput
      exact ⟨middleObservation, Or.inl hmiddleParent.symm⟩
  | right =>
      obtain ⟨nextObservation, hneutral | hcross⟩ :=
        observation.exists_strictLeft_neutralOrPhaseSecond_of_right A strategy
          hwin hside hoperational hdeferredTwo haligned nextInput
      · exact ⟨nextObservation, Or.inl hneutral.2.symm⟩
      · have hactive :
            (observation.phaseCoordinates A strategy hwin).1 =
              observation.parent A strategy hwin := by
          simpa [hside] using
            observation.phaseCoordinates_active A strategy hwin
        refine ⟨nextObservation, ?_⟩
        rcases hphase with ⟨packet, hexact, hsuccessor⟩ |
            ⟨packet, hexact, hsuccessor⟩
        · refine Or.inr (Or.inl ⟨packet, ?_, ?_⟩)
          · rw [← hactive]
            exact hexact
          · exact hcross.2.trans hsuccessor
        · refine Or.inr (Or.inr ⟨packet, ?_, ?_⟩)
          · rw [hcross.2]
            exact hexact
          · exact hactive.symm.trans hsuccessor

end ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation

/-! ## Exact staged packets throughout the acknowledged relay -/

theorem
    profiledRawJointRecurrentOwnerFibreExactClosingRecvForkOne_packetExact
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (selected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two)
    (input : In₁ × In₂) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      one input.1 two input.2
    ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        fork.1.closedControl := by
  cases selected with
  | right phaseData decoded invariant =>
      exact
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.exactClosingRecvForkOne_packetExact
          A strategy hwin
            (.right phaseData decoded invariant (input := input))
  | left phaseData rightAbsent decoded invariant =>
      exact
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.exactClosingRecvForkOne_packetExact
          A strategy hwin
            (.left phaseData rightAbsent decoded invariant (input := input))

theorem
    profiledRawJointRecurrentOwnerFibreExactClosingRecvForkTwo_packetExact
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (selected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two)
    (input : In₁ × In₂) :
    let fork := FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      two input.2 one input.1
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        fork.1.openControl ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        fork.1.closedControl := by
  cases selected with
  | right phaseData decoded invariant =>
      exact
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.exactClosingRecvForkTwo_packetExact
          A strategy hwin
            (.right phaseData decoded invariant (input := input))
  | left phaseData rightAbsent decoded invariant =>
      exact
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.exactClosingRecvForkTwo_packetExact
          A strategy hwin
            (.left phaseData rightAbsent decoded invariant (input := input))

/-- Every staged-packet meaning retained by either relay is an exact edge
from the source state stored beside it. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact
    (one : OneRelay A strategy hwin) (two : TwoRelay A strategy hwin) : Prop :=
  FiniteAcknowledgedDelayedCarrier.CarrierAll
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy
        hwin) one ∧
    FiniteAcknowledgedDelayedCarrier.CarrierAll
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy
        hwin) two

/-- The semantic relay invariant identifies its proof-side operational pair
with the two controls actually selected by the acknowledgement metadata. -/
theorem
    profiledRawJointRecurrentOwnerFibreExactClosingRelayInvariant_resolved_operational
    (one : OneRelay A strategy hwin) (two : TwoRelay A strategy hwin)
    (hinvariant :
      FiniteAcknowledgedDelayedCarrier.ExactClosingRelayInvariant
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
        (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy
          hwin) one two) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
      (FiniteAcknowledgedDelayedCarrier.resolvedControl two one) := by
  rcases hinvariant.selected with
    ⟨actualOne, actualTwo, hselects, hoperational⟩
  rcases hselects with ⟨hone, htwo⟩
  change FiniteAcknowledgedDelayedCarrier.resolvedControl one two = actualOne
    at hone
  change FiniteAcknowledgedDelayedCarrier.resolvedControl two one = actualTwo
    at htwo
  rw [hone, htwo]
  exact hoperational

theorem
    ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact.advance
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (one : OneRelay A strategy hwin) (two : TwoRelay A strategy hwin)
    (hall :
      ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact A strategy
        hwin one two)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
        (FiniteAcknowledgedDelayedCarrier.resolvedControl two one))
    (round : EnvironmentRound In₁ In₂) :
    let controller :=
      profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo
    let next := controller.semanticAdvanceControls (one, two) round
    ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact A strategy
      hwin next.1 next.2 := by
  let OneExact :=
    ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
  let TwoExact :=
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
  have hnoRecvOne :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_noRecvMealy OneExact
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
      one round.inputOne
      (fun control hcontrol ↦
        ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact.noRecv A
          strategy hwin control hcontrol round.inputOne) hall.1
  have hnoRecvTwo :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_noRecvMealy TwoExact
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
      two round.inputTwo
      (fun control hcontrol ↦
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact.noRecv A
          strategy hwin control hcontrol round.inputTwo) hall.2
  have hrecvOne :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_recvReforkMealy OneExact
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
          hwin)
        (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin))
      one round.inputOne two round.inputTwo
      (profiledRawJointRecurrentOwnerFibreExactClosingRecvForkOne_packetExact
        A strategy hwin
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
          hoperational.selected (round.inputOne, round.inputTwo))
  have hrecvTwo :=
    FiniteAcknowledgedDelayedCarrier.carrierAll_recvReforkMealy TwoExact
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
          hwin)
        (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin))
      two round.inputTwo one round.inputOne
      (profiledRawJointRecurrentOwnerFibreExactClosingRecvForkTwo_packetExact
        A strategy hwin
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
          hoperational.selected (round.inputOne, round.inputTwo))
  cases hgraph : round.graph with
  | right =>
      simpa [FinitePairedMealyController.semanticAdvanceControls,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact,
        OneExact, TwoExact, hgraph] using And.intro hnoRecvOne hrecvTwo
  | left =>
      simpa [FinitePairedMealyController.semanticAdvanceControls,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact,
        OneExact, TwoExact, hgraph] using And.intro hrecvOne hnoRecvTwo
  | both =>
      simpa [FinitePairedMealyController.semanticAdvanceControls,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact,
        OneExact, TwoExact, hgraph] using And.intro hrecvOne hrecvTwo

/-- From exact-packet initial controls, every staged meaning in the actual
acknowledged trace remains an exact fixed-policy edge at every prefix. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticControlTrace_packetExact
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy
        hwin initialOne)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy
        hwin initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let controls :=
      (profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo).semanticControlTrace env n
    ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact A strategy
      hwin controls.1 controls.2 := by
  induction n with
  | zero =>
      simpa [FinitePairedMealyController.semanticControlTrace,
        profiledRawJointRecurrentOwnerFibreBoundaryController,
        FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
        FiniteAcknowledgedDelayedCarrier.pairedMealyController,
        ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact] using
          And.intro hone htwo
  | succ n ih =>
      let controls :=
        (profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
          initialOne initialTwo).semanticControlTrace env n
      have hrelay :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticControlTrace_relayInvariant
          A strategy hwin initialOne initialTwo hinitial env n
      have hoperational :=
        profiledRawJointRecurrentOwnerFibreExactClosingRelayInvariant_resolved_operational
          A strategy hwin controls.1 controls.2 hrelay
      simpa only [FinitePairedMealyController.semanticControlTrace] using
        (ProfiledRawJointRecurrentOwnerFibreBoundaryRelaysPacketExact.advance A
          strategy hwin initialOne initialTwo controls.1 controls.2 ih
            hoperational (env n))

/-! ## Exactness at canonical recurrent entries -/

theorem profiledRawJointRecurrentOwnerFibreRightEntry_packetExact
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin rightState) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
          rightState rightReceiver rightOwner leftTemplate packet) ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
          rightState rightReceiver packet) := by
  exact ⟨trivial, fun candidate hc ↦ by
    cases Option.some.inj hc
    exact hexact⟩

theorem profiledRawJointRecurrentOwnerFibreLeftEntry_packetExact
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin leftState) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOnePacketExact A strategy hwin
        (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
          leftState leftReceiver packet) ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoPacketExact A strategy hwin
        (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
          leftState leftReceiver leftOwner rightTemplate packet) := by
  exact ⟨(fun candidate hc ↦ by
      cases Option.some.inj hc
      exact hexact), trivial⟩

/-- Canonical right entry has complete delayed-edge provenance.  Its first
endpoint is installed and its second endpoint carries the exact staged
packet. -/
theorem profiledRawJointRecurrentOwnerFibreRightEntry_deferredExact
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin rightState) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
          rightState rightReceiver rightOwner leftTemplate packet)
        (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
          rightState rightReceiver packet) := by
  exact ⟨trivial, fun candidate hc ↦ by
    cases Option.some.inj hc
    exact hexact⟩

/-- Mirrored complete provenance at the canonical left entry. -/
theorem profiledRawJointRecurrentOwnerFibreLeftEntry_deferredExact
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin leftState) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
          leftState leftReceiver packet)
        (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
          leftState leftReceiver leftOwner rightTemplate packet) := by
  exact ⟨(fun candidate hc ↦ by
      cases Option.some.inj hc
      exact hexact), trivial⟩

theorem profiledRawJointRecurrentOwnerFibreRightEntry_coordinateAligned
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
          rightState rightReceiver rightOwner leftTemplate packet)
        (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
          rightState rightReceiver packet) := by
  exact ⟨rfl, ⟨rfl, fun candidate hc ↦ by
    cases Option.some.inj hc
    rfl⟩⟩

theorem profiledRawJointRecurrentOwnerFibreLeftEntry_coordinateAligned
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A strategy
      hwin
        (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
          leftState leftReceiver packet)
        (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
          leftState leftReceiver leftOwner rightTemplate packet) := by
  exact ⟨⟨rfl, fun candidate hc ↦ by
      cases Option.some.inj hc
      rfl⟩, rfl⟩

/-- Both local coordinate copies at a canonical right entry are the same
fresh exact edge. -/
theorem profiledRawJointRecurrentOwnerFibreRightEntry_coordinateEdgeExact
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin rightState) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
      strategy hwin
        (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
          rightState rightReceiver rightOwner leftTemplate packet)
        (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
          rightState rightReceiver packet) := by
  let hedge :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (rightState, packet.successor) :=
    Or.inl ⟨packet, hexact, rfl⟩
  exact ⟨hedge, hedge⟩

/-- Mirrored exact coordinate copies at a canonical left entry. -/
theorem profiledRawJointRecurrentOwnerFibreLeftEntry_coordinateEdgeExact
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (hexact : packet.ExactFrom A strategy hwin leftState) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
      strategy hwin
        (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
          leftState leftReceiver packet)
        (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
          leftState leftReceiver leftOwner rightTemplate packet) := by
  let hedge :
      ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy
        hwin (packet.successor, leftState) :=
    Or.inr ⟨packet, hexact, rfl⟩
  exact ⟨hedge, hedge⟩

/-- Canonical entry pairs are not both pending, so the pending-only
cross-coordinate condition is vacuous. -/
theorem profiledRawJointRecurrentOwnerFibreRightEntry_pendingCoordinateCoherent
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent A
      strategy hwin
        (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
          rightState rightReceiver rightOwner leftTemplate packet)
        (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
          rightState rightReceiver packet) := by
  trivial

theorem profiledRawJointRecurrentOwnerFibreLeftEntry_pendingCoordinateCoherent
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent A
      strategy hwin
        (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
          leftState leftReceiver packet)
        (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
          leftState leftReceiver leftOwner rightTemplate packet) := by
  trivial

/-! ## Committed edges on the canonical semantic trace -/

/-- The underlying deterministic control pair selected by the acknowledged
relay before round `n`. -/
noncomputable def
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace initialOne
    initialTwo
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin) env n

theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_right
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1) =
      let pair :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A
          strategy hwin initialOne initialTwo env n
      ((profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          pair.1 (env n).inputOne).1,
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          pair.2 (env n).inputTwo pair.1 (env n).inputOne).1) := by
  simp [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hgraph]

theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_left
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1) =
      let pair :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A
          strategy hwin initialOne initialTwo env n
      ((profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          pair.1 (env n).inputOne pair.2 (env n).inputTwo).1,
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          pair.2 (env n).inputTwo).1) := by
  simp [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hgraph]

theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_both
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .both) :
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1) =
      let pair :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A
          strategy hwin initialOne initialTwo env n
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin pair.1
        (env n).inputOne pair.2 (env n).inputTwo := by
  simp [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hgraph]

/-- The compact operational invariant holds directly on the canonical
underlying-control trace. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      pair.1 pair.2 := by
  intro n
  induction n with
  | zero =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace] using
        hinitial
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using
            (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight
              A strategy hwin _ _ ih (env n).inputOne (env n).inputTwo)
      | left =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using
            (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft
              A strategy hwin _ _ ih (env n).inputOne (env n).inputTwo)
      | both =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using
            (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.both A
              strategy hwin _ _ ih (env n).inputOne (env n).inputTwo)

/-- Complete delayed-edge provenance is invariant on every prefix of the
canonical selected-control trace.  This includes both explicit staged
packets and the successor hidden in each pending owner fibre. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_deferredExact
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hexact :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
      hwin pair.1 pair.2 := by
  intro n
  induction n with
  | zero =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace] using
          hexact
  | succ n ih =>
      let pair :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A
          strategy hwin initialOne initialTwo env n
      have hoperational :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational
          A strategy hwin initialOne initialTwo hinitial env n
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.ofSelected
          A strategy hwin hoperational.selected
            (input := ((env n).inputOne, (env n).inputTwo))
      have hnoRecvOne :=
        ih.1.noRecv A strategy hwin pair.1 (env n).inputOne
      have hnoRecvTwo :=
        ih.2.noRecv A strategy hwin pair.2 (env n).inputTwo
      have hrecvOne := observation.openRecvOne_deferredExact A strategy hwin
      have hrecvTwo := observation.openRecvTwo_deferredExact A strategy hwin
      have hclose := observation.close_deferredExact A strategy hwin
      cases hgraph : (env n).graph with
      | right =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact,
            hgraph] using And.intro hnoRecvOne hrecvTwo
      | left =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact,
            hgraph] using And.intro hrecvOne hnoRecvTwo
      | both =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact,
            hgraph] using hclose

/-- The semantic meaning of both outer bank coordinates is likewise
preserved at every canonical trace prefix. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_coordinateAligned
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
      strategy hwin pair.1 pair.2 := by
  intro n
  induction n with
  | zero =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace] using
          haligned
  | succ n ih =>
      let pair :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A
          strategy hwin initialOne initialTwo env n
      have hoperational :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational
          A strategy hwin initialOne initialTwo hinitial env n
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.ofSelected
          A strategy hwin hoperational.selected
            (input := ((env n).inputOne, (env n).inputTwo))
      have hnoRecvOne :=
        ih.1.noRecv A strategy hwin pair.1 (env n).inputOne
      have hnoRecvTwo :=
        ih.2.noRecv A strategy hwin pair.2 (env n).inputTwo
      have hrecvOne := observation.openRecvOne_coordinateAligned A strategy
        hwin
      have hrecvTwo := observation.openRecvTwo_coordinateAligned A strategy
        hwin
      have hclose := observation.close_coordinateAligned A strategy hwin
      cases hgraph : (env n).graph with
      | right =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned,
            hgraph] using And.intro hnoRecvOne hrecvTwo
      | left =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned,
            hgraph] using And.intro hrecvOne hnoRecvTwo
      | both =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned,
            hgraph] using hclose

/-- Every trace prefix carries two exact local coordinate edges together with
the sole cross-endpoint equality needed when both controls are pending.  The
induction is mutually supporting: these certificates make the currently
decoded phase exact, and that phase exactness certifies the receive-created
coordinates at the next prefix. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_coordinateExact
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (hedges :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin initialOne initialTwo)
    (hcoherent :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin pair.1 pair.2 ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin pair.1 pair.2 := by
  intro n
  induction n with
  | zero =>
      simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace] using
          And.intro hedges hcoherent
  | succ n ih =>
      let pair :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A
          strategy hwin initialOne initialTwo env n
      have hoperational :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational
          A strategy hwin initialOne initialTwo hinitial env n
      have hdeferredNow :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_deferredExact
          A strategy hwin initialOne initialTwo hinitial hdeferred env n
      have halignedNow :=
        profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_coordinateAligned
          A strategy hwin initialOne initialTwo hinitial haligned env n
      let observation :=
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.ofSelected
          A strategy hwin hoperational.selected
            (input := ((env n).inputOne, (env n).inputTwo))
      have hphase := observation.phaseCoordinates_edgeExact A strategy hwin
        hdeferredNow halignedNow ih.1 ih.2
      have hnoRecvOne :=
        ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact.noRecvOne A
          strategy hwin pair.1 ih.1.1 (env n).inputOne
      have hnoRecvTwo :=
        ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact.noRecvTwo A
          strategy hwin pair.2 ih.1.2 (env n).inputTwo
      have hrecvOne := observation.openRecvOne_coordinateEdgeExact A strategy
        hwin hphase
      have hrecvTwo := observation.openRecvTwo_coordinateEdgeExact A strategy
        hwin hphase
      have hcloseEdges := observation.close_coordinateEdgeExact A strategy
        hwin hphase
      have hstrictRightCoherent :=
        observation.strictRight_pendingCoordinateCoherent A strategy hwin
          halignedNow
      have hstrictLeftCoherent :=
        observation.strictLeft_pendingCoordinateCoherent A strategy hwin
          halignedNow
      have hcloseCoherent :=
        observation.close_pendingCoordinateCoherent A strategy hwin
      cases hgraph : (env n).graph with
      | right =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact,
            hgraph] using
              And.intro (And.intro hnoRecvOne hrecvTwo)
                hstrictRightCoherent
      | left =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact,
            hgraph] using
              And.intro (And.intro hrecvOne hnoRecvTwo)
                hstrictLeftCoherent
      | both =>
          simpa [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using And.intro hcloseEdges hcloseCoherent

/-- Canonical resolver observation of the selected semantic controls at a
trace position.  Its query input is the input of that position's round. -/
noncomputable def
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A strategy
      hwin pair.1 pair.2 ((env n).inputOne, (env n).inputTwo) :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.ofSelected A
    strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational
        A strategy hwin initialOne initialTwo hinitial env n).selected

/-- Every canonical observation, including observations reached only through
strict rounds, decodes an exact policy edge in one of the two orientations. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation_phaseEdgeExact
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (hedges :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin initialOne initialTwo)
    (hcoherent :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    let observation :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n
    ProfiledRawJointRecurrentBoundaryBankCoordinates.EdgeExact A strategy hwin
      (observation.phaseCoordinates A strategy hwin) := by
  dsimp only
  let pair :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
      hwin initialOne initialTwo env n
  let observation :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n
  have hdeferredNow :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_deferredExact
      A strategy hwin initialOne initialTwo hinitial hdeferred env n
  have halignedNow :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_coordinateAligned
      A strategy hwin initialOne initialTwo hinitial haligned env n
  have hcoordinates :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_coordinateExact
      A strategy hwin initialOne initialTwo hinitial hdeferred haligned hedges
        hcoherent env n
  exact observation.phaseCoordinates_edgeExact A strategy hwin hdeferredNow
    halignedNow hcoordinates.1 hcoordinates.2

/-- Trace-level strict-right parent classification. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_right_parentStep
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    let nextPair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1)
    let observation :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextPair.1 nextPair.2
            ((env (n + 1)).inputOne, (env (n + 1)).inputTwo),
      nextObservation.side A strategy hwin = .right ∧
        (nextObservation.parent A strategy hwin =
            observation.parent A strategy hwin ∨
          nextObservation.parent A strategy hwin =
            (observation.phaseCoordinates A strategy hwin).1) := by
  dsimp only
  let pair :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
      hwin initialOne initialTwo env n
  let observation :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n
  have hoperational :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational A
      strategy hwin initialOne initialTwo hinitial env n
  have hdeferredNow :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_deferredExact
      A strategy hwin initialOne initialTwo hinitial hdeferred env n
  have hstep := observation.exists_strictRight_parentStep A strategy hwin
    hoperational hdeferredNow.1
      ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
  rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_right
    A strategy hwin initialOne initialTwo env n hgraph]
  exact hstep

/-- Trace-level strict-left parent classification. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_left_parentStep
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    let nextPair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1)
    let observation :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextPair.1 nextPair.2
            ((env (n + 1)).inputOne, (env (n + 1)).inputTwo),
      nextObservation.parent A strategy hwin =
          observation.parent A strategy hwin ∨
        (nextObservation.side A strategy hwin = .left ∧
          nextObservation.parent A strategy hwin =
            (observation.phaseCoordinates A strategy hwin).2) := by
  dsimp only
  let pair :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
      hwin initialOne initialTwo env n
  let observation :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n
  have hoperational :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational A
      strategy hwin initialOne initialTwo hinitial env n
  have hdeferredNow :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_deferredExact
      A strategy hwin initialOne initialTwo hinitial hdeferred env n
  have halignedNow :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_coordinateAligned
      A strategy hwin initialOne initialTwo hinitial haligned env n
  have hstep := observation.exists_strictLeft_parentStep A strategy hwin
    hoperational hdeferredNow.2 halignedNow
      ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
  rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_left A
    strategy hwin initialOne initialTwo env n hgraph]
  exact hstep

/-- At every position of the canonical semantic trace, the next active bank
parent is stationary, a genuine successor in the one fixed policy, or a
genuine predecessor whose edge is being rolled back.  This is stronger than
undirected phase adjacency and is the exact input needed by any later
cancellation or bounded-recurrence argument. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_exactParentStep
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (hedges :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin initialOne initialTwo)
    (hcoherent :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    let nextPair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1)
    let observation :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextPair.1 nextPair.2
            ((env (n + 1)).inputOne, (env (n + 1)).inputTwo),
      ProfiledRawJointRecurrentBankParentStep A strategy hwin
        (observation.parent A strategy hwin)
        (nextObservation.parent A strategy hwin) := by
  dsimp only
  let pair :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
      hwin initialOne initialTwo env n
  let observation :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n
  have hoperational :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational A
      strategy hwin initialOne initialTwo hinitial env n
  have hdeferredNow :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_deferredExact
      A strategy hwin initialOne initialTwo hinitial hdeferred env n
  have halignedNow :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_coordinateAligned
      A strategy hwin initialOne initialTwo hinitial haligned env n
  have hphase :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation_phaseEdgeExact
      A strategy hwin initialOne initialTwo hinitial hdeferred haligned hedges
        hcoherent env n
  cases hgraph : (env n).graph with
  | right =>
      have hstep := observation.exists_strictRight_exactParentStep A strategy
        hwin hoperational hdeferredNow.1 hphase
          ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
      rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_right
        A strategy hwin initialOne initialTwo env n hgraph]
      exact ⟨hstep.choose, hstep.choose_spec.2⟩
  | left =>
      have hstep := observation.exists_strictLeft_exactParentStep A strategy
        hwin hoperational hdeferredNow.2 halignedNow hphase
          ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
      rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_left
        A strategy hwin initialOne initialTwo env n hgraph]
      exact hstep
  | both =>
      obtain ⟨nextObservation, packet, hexact, hnextParent, hnextSide⟩ :=
        observation.exists_both_committedEdge A strategy hwin
          ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
      rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_both
        A strategy hwin initialOne initialTwo env n hgraph]
      exact ⟨nextObservation,
        Or.inr (Or.inl ⟨packet, hexact, hnextParent⟩)⟩

/-- Canonical active bank-parent stream of the recurrent semantic trace. -/
noncomputable def
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
    strategy hwin initialOne initialTwo hinitial env n).parent A strategy hwin

/-- The canonical parent stream itself, rather than an existentially chosen
decoder witness at each successor, follows the exact neutral/forward/rollback
transition relation. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent_step
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (hedges :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin initialOne initialTwo)
    (hcoherent :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ProfiledRawJointRecurrentBankParentStep A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
        strategy hwin initialOne initialTwo hinitial env n)
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
        strategy hwin initialOne initialTwo hinitial env (n + 1)) := by
  obtain ⟨nextObservation, hstep⟩ :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_exactParentStep
      A strategy hwin initialOne initialTwo hinitial hdeferred haligned hedges
        hcoherent env n
  let canonicalNext :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env (n + 1)
  have hparent := nextObservation.parent_eq A strategy hwin canonicalNext
  change ProfiledRawJointRecurrentBankParentStep A strategy hwin
    (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n |>.parent A strategy
        hwin)
    (canonicalNext.parent A strategy hwin)
  rw [← hparent]
  exact hstep

/-- A rollback-safe certificate at the initial active parent applies directly
to the canonical recurrent parent stream.  The proof has no hidden trace
selection: reachability comes from each canonical resolver observation, and
the transition premise is exactly `SemanticTraceParent_step`. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent_acceptsFrom
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (hedges :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin initialOne initialTwo)
    (hcoherent :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsafe :
      ProfiledRawJointRecurrentBankRollbackSafeFrom A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
          strategy hwin initialOne initialTwo hinitial env 0)) :
    (sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
        (profiledRawJointOneSidedCodeParityDPA A
          (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
            strategy hwin initialOne initialTwo hinitial env 0).1.1.1)).AcceptsFrom
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
        strategy hwin initialOne initialTwo hinitial env 0).2.2
      (fun n ↦
        (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
          strategy hwin initialOne initialTwo hinitial env (n + 1)).2.1) := by
  apply hsafe
  · rfl
  · intro n
    exact
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n).parent_reachable A
          strategy hwin
  · intro n
    exact
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent_step A
        strategy hwin initialOne initialTwo hinitial hdeferred haligned hedges
          hcoherent env n

/-- Finite sufficient-certificate-facing form of recurrent trace acceptance.
No additional semantic trace lemma remains between acceptance of the
projected rollback-monitor graph and acceptance of the canonical
active-parent word. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent_acceptsFrom_of_monitorAccepting
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hdeferred :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairDeferredExact A strategy
        hwin initialOne initialTwo)
    (haligned :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateAligned A
        strategy hwin initialOne initialTwo)
    (hedges :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPairCoordinateEdgeExact A
        strategy hwin initialOne initialTwo)
    (hcoherent :
      ProfiledRawJointRecurrentOwnerFibreBoundaryPendingPairCoordinateCoherent
        A strategy hwin initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hmonitor :
      ProfiledRawJointRecurrentBankRollbackMonitorAccepting A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
          strategy hwin initialOne initialTwo hinitial env 0)) :
    (sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
        (profiledRawJointOneSidedCodeParityDPA A
          (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
            strategy hwin initialOne initialTwo hinitial env 0).1.1.1)).AcceptsFrom
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
        strategy hwin initialOne initialTwo hinitial env 0).2.2
      (fun n ↦
        (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent A
          strategy hwin initialOne initialTwo hinitial env (n + 1)).2.1) := by
  apply
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceParent_acceptsFrom
      A strategy hwin initialOne initialTwo hinitial hdeferred haligned hedges
        hcoherent env
  exact
    profiledRawJointRecurrentBankRollbackSafeFrom_of_monitorAccepting A
      strategy hwin _ hmonitor

/-- Every simultaneous round contributes a committed edge between the
canonical observations before and after that round. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_both_committedEdge
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .both) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    let nextPair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1)
    let observation :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n
    ∃ nextObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin nextPair.1 nextPair.2
            ((env (n + 1)).inputOne, (env (n + 1)).inputTwo),
      ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.CommittedEdge
        A strategy hwin observation nextObservation := by
  dsimp only
  let observation :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n
  have hcommitted :=
    observation.exists_both_committedEdge A strategy hwin
      ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
  rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_both
    A strategy hwin initialOne initialTwo env n hgraph]
  exact hcommitted

/-- A canonical right/left adjacent reversal contributes a committed edge
whenever the observation before the pair is right-oriented. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_right_left_committedEdge
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right)
    (hnextGraph : (env (n + 1)).graph = .left)
    (hside :
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n).side A strategy
          hwin = .right) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    let middlePair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1)
    let afterPair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 2)
    let observation :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n
    ∃ middleObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin middlePair.1 middlePair.2
            ((env (n + 1)).inputOne, (env (n + 1)).inputTwo),
      ∃ afterObservation :
          ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
            strategy hwin afterPair.1 afterPair.2
              ((env (n + 2)).inputOne, (env (n + 2)).inputTwo),
        middleObservation.side A strategy hwin = .right ∧
          middleObservation.parent A strategy hwin =
            observation.parent A strategy hwin ∧
          ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.CommittedEdge
            A strategy hwin middleObservation afterObservation := by
  dsimp only
  let pair :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
      hwin initialOne initialTwo env n
  let observation :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n
  have hoperational :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational A
      strategy hwin initialOne initialTwo hinitial env n
  have hcommitted :=
    observation.exists_committedEdge_after_right_left_of_right A strategy hwin
      hside hoperational
      ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
      ((env (n + 2)).inputOne, (env (n + 2)).inputTwo)
  rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_right
    A strategy hwin initialOne initialTwo env n hgraph]
  rw [show n + 2 = (n + 1) + 1 by omega,
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_left A
      strategy hwin initialOne initialTwo env (n + 1) hnextGraph,
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_right A
      strategy hwin initialOne initialTwo env n hgraph]
  exact hcommitted

/-- Mirrored canonical adjacent-reversal theorem. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_left_right_committedEdge
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left)
    (hnextGraph : (env (n + 1)).graph = .right)
    (hside :
      (profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n).side A strategy
          hwin = .left) :
    let pair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env n
    let middlePair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 1)
    let afterPair :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
        hwin initialOne initialTwo env (n + 2)
    let observation :=
      profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
        strategy hwin initialOne initialTwo hinitial env n
    ∃ middleObservation :
        ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
          strategy hwin middlePair.1 middlePair.2
            ((env (n + 1)).inputOne, (env (n + 1)).inputTwo),
      ∃ afterObservation :
          ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation A
            strategy hwin afterPair.1 afterPair.2
              ((env (n + 2)).inputOne, (env (n + 2)).inputTwo),
        middleObservation.side A strategy hwin = .left ∧
          middleObservation.parent A strategy hwin =
            observation.parent A strategy hwin ∧
          ProfiledRawJointRecurrentOwnerFibreBoundaryResolverObservation.CommittedEdge
            A strategy hwin middleObservation afterObservation := by
  dsimp only
  let pair :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace A strategy
      hwin initialOne initialTwo env n
  let observation :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticTraceObservation A
      strategy hwin initialOne initialTwo hinitial env n
  have hoperational :=
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_operational A
      strategy hwin initialOne initialTwo hinitial env n
  have hcommitted :=
    observation.exists_committedEdge_after_left_right_of_left A strategy hwin
      hside hoperational
      ((env (n + 1)).inputOne, (env (n + 1)).inputTwo)
      ((env (n + 2)).inputOne, (env (n + 2)).inputTwo)
  rw [profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_left A
    strategy hwin initialOne initialTwo env n hgraph]
  rw [show n + 2 = (n + 1) + 1 by omega,
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_right A
      strategy hwin initialOne initialTwo env (n + 1) hnextGraph,
    profiledRawJointRecurrentOwnerFibreBoundarySemanticPairTrace_succ_left A
      strategy hwin initialOne initialTwo env n hgraph]
  exact hcommitted

end

end DetParityAutomaton

end DistributedSynthesis
