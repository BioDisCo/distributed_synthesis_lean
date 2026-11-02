/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicySelectionOwnerFibreSafetyAutomaton
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreTraceAlignment

/-!
# Fixed-key locality of a selected owner-fibre kernel

Two global policy selections that agree at one root key induce the same
packet resolution, receives, outputs, and closed-loop round at every boundary
whose stored bank states belong to that key.  This is the extensionality
needed to assemble independently regularized root fibres into one global
selection.
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

private abbrev OneControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin

private abbrev TwoControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin

private abbrev PolicySelection :=
  ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy hwin

namespace ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

variable (selection other : PolicySelection A strategy hwin)

theorem rightBoundaryOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : data.1.1 = key)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.rightBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input =
      other.rightBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input := by
  unfold rightBoundaryOwnerFibreReceive
  rw [selection.resolvePacket_congr_at A strategy hwin other key data.1 hkey
    (data.target A strategy hwin input) hagrees]

theorem leftBoundaryOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (oldState : BankControl A strategy hwin)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂)
    (hkey : data.1.1 = key)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.leftBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input =
      other.leftBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input := by
  unfold leftBoundaryOwnerFibreReceive
  rw [selection.resolvePacket_congr_at A strategy hwin other key data.1 hkey
    (data.target A strategy hwin input) hagrees]

theorem rightPhaseOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (hkey : data.AtKey A strategy hwin key)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.rightPhaseOwnerFibreReceive A strategy hwin data input =
      other.rightPhaseOwnerFibreReceive A strategy hwin data input := by
  simp only [rightPhaseOwnerFibreReceive]
  rw [selection.rightBoundaryOwnerFibreReceive_congr_at A strategy hwin other
    key data.1 data.2.1 data.2.2 input hkey.1 hagrees]

theorem leftPhaseOwnerFibreReceive_congr_at
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (hkey : data.AtKey A strategy hwin key)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.leftPhaseOwnerFibreReceive A strategy hwin data input =
      other.leftPhaseOwnerFibreReceive A strategy hwin data input := by
  simp only [leftPhaseOwnerFibreReceive]
  rw [selection.leftBoundaryOwnerFibreReceive_congr_at A strategy hwin other
    key data.1 data.2.1 data.2.2 input hkey.1 hagrees]

/-! ## Fixed-key preservation for an arbitrary selection -/

theorem rightPhaseOwnerFibreReceive_atKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hkey : data.AtKey A strategy hwin key)
    (input : In₁ × In₂) :
    let result :=
      selection.rightPhaseOwnerFibreReceive A strategy hwin data input
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
  let packet := selection.resolvePacket A strategy hwin state
    (((((receiver.1.memberController A false).labelOf owner).2
      receiver.2.2.1 (input.2, input.1)).target receiver.2.1))
  have hpacket : packet.AtKey A strategy hwin key := by
    change (selection.successor A strategy hwin state _).1 = key
    rw [selection.successor_index A strategy hwin]
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

theorem leftPhaseOwnerFibreReceive_atKey
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hkey : data.AtKey A strategy hwin key)
    (input : In₁ × In₂) :
    let result :=
      selection.leftPhaseOwnerFibreReceive A strategy hwin data input
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
  let packet := selection.resolvePacket A strategy hwin state
    (((((receiver.1.memberController A false).labelOf owner).2
      receiver.2.2.1 input).target receiver.2.1))
  have hpacket : packet.AtKey A strategy hwin key := by
    change (selection.successor A strategy hwin state _).1 = key
    rw [selection.successor_index A strategy hwin]
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

theorem ownerFibreBoundaryReceive?_congr_at
    (key : RootKey A strategy)
    (one : OneControl A strategy hwin)
    (two : TwoControl A strategy hwin)
    (input : In₁ × In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreBoundaryReceive? A strategy hwin one two input =
      other.ownerFibreBoundaryReceive? A strategy hwin one two input := by
  cases hright :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        one two with
  | some data =>
      have hdata :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_atKey A strategy
          hwin key one two data hone htwo hright
      simp only [ownerFibreBoundaryReceive?, hright]
      rw [selection.rightPhaseOwnerFibreReceive_congr_at A strategy hwin other
        key data input hdata hagrees]
  | none =>
      cases hleft :
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
            one two with
      | some data =>
          have hdata :=
            profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_atKey A
              strategy hwin key one two data hone htwo hleft
          simp only [ownerFibreBoundaryReceive?, hright, hleft]
          rw [selection.leftPhaseOwnerFibreReceive_congr_at A strategy hwin
            other key data input hdata hagrees]
      | none =>
          simp [ownerFibreBoundaryReceive?, hright, hleft]

theorem ownerFibreBoundaryReceive?_atKey
    (key : RootKey A strategy)
    (one : OneControl A strategy hwin)
    (two : TwoControl A strategy hwin)
    (input : In₁ × In₂)
    (result :
      (FiniteDelayedFork (OneControl A strategy hwin) × Out₁) ×
        (FiniteDelayedFork (TwoControl A strategy hwin) × Out₂))
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin one two
      input = some result) :
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
      have hresult := selection.rightPhaseOwnerFibreReceive_atKey A strategy
        hwin key data hdata input
      rw [ownerFibreBoundaryReceive?, hright] at hreceive
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
          have hresult := selection.leftPhaseOwnerFibreReceive_atKey A strategy
            hwin key data hdata input
          rw [ownerFibreBoundaryReceive?, hright, hleft] at hreceive
          cases Option.some.inj hreceive
          exact hresult
      | none =>
          simp [ownerFibreBoundaryReceive?, hright, hleft] at hreceive

theorem ownerFibreBoundaryOpenRecvOne_congr_at
    (key : RootKey A strategy)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo =
      other.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo := by
  unfold ownerFibreBoundaryOpenRecvOne
  rw [selection.ownerFibreBoundaryReceive?_congr_at A strategy hwin other key
    one two (inputOne, inputTwo) hone htwo hagrees]

theorem ownerFibreBoundaryOpenRecvTwo_congr_at
    (key : RootKey A strategy)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne =
      other.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne := by
  unfold ownerFibreBoundaryOpenRecvTwo
  rw [selection.ownerFibreBoundaryReceive?_congr_at A strategy hwin other key
    one two (inputOne, inputTwo) hone htwo hagrees]

theorem ownerFibreBoundaryCloseRound_congr_at
    (key : RootKey A strategy)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
        inputTwo =
      other.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
        inputTwo := by
  unfold ownerFibreBoundaryCloseRound
  rw [selection.ownerFibreBoundaryReceive?_congr_at A strategy hwin other key
    one two (inputOne, inputTwo) hone htwo hagrees]

theorem ownerFibreRound_congr_at
    (key : RootKey A strategy)
    (controls : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) (graph : Graph)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        controls.1)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        controls.2)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreRound A strategy hwin controls input graph =
      other.ownerFibreRound A strategy hwin controls input graph := by
  cases graph with
  | right =>
      unfold ownerFibreRound
      rw [selection.ownerFibreBoundaryOpenRecvTwo_congr_at A strategy hwin
        other key controls.2 input.2 controls.1 input.1 htwo hone hagrees]
  | left =>
      unfold ownerFibreRound
      rw [selection.ownerFibreBoundaryOpenRecvOne_congr_at A strategy hwin
        other key controls.1 input.1 controls.2 input.2 hone htwo hagrees]
  | both =>
      exact selection.ownerFibreBoundaryCloseRound_congr_at A strategy hwin
        other key controls.1 input.1 controls.2 input.2 hone htwo hagrees

theorem ownerFibreRoundRecord_congr_at
    (key : RootKey A strategy)
    (controls : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) (graph : Graph)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        controls.1)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        controls.2)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ownerFibreRoundRecord A strategy hwin controls input graph =
      other.ownerFibreRoundRecord A strategy hwin controls input graph := by
  unfold ownerFibreRoundRecord
  rw [selection.ownerFibreRound_congr_at A strategy hwin other key controls
    input graph hone htwo hagrees]

theorem ownerFibreBoundaryOpenRecvOne_atKey
    (key : RootKey A strategy)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
      (selection.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne
        two inputTwo).1 := by
  cases hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin one
      two (inputOne, inputTwo) with
  | none =>
      simpa [ownerFibreBoundaryOpenRecvOne, hreceive] using
        hone.noRecv A strategy hwin key one inputOne
  | some result =>
      have hall := selection.ownerFibreBoundaryReceive?_atKey A strategy hwin
        key one two (inputOne, inputTwo) result hone htwo hreceive
      simpa [ownerFibreBoundaryOpenRecvOne, hreceive] using hall.1

theorem ownerFibreBoundaryOpenRecvTwo_atKey
    (key : RootKey A strategy)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
      (selection.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo
        one inputOne).1 := by
  cases hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin one
      two (inputOne, inputTwo) with
  | none =>
      simpa [ownerFibreBoundaryOpenRecvTwo, hreceive] using
        htwo.noRecv A strategy hwin key two inputTwo
  | some result =>
      have hall := selection.ownerFibreBoundaryReceive?_atKey A strategy hwin
        key one two (inputOne, inputTwo) result hone htwo hreceive
      simpa [ownerFibreBoundaryOpenRecvTwo, hreceive] using hall.2.2.1

theorem ownerFibreBoundaryCloseRound_atKey
    (key : RootKey A strategy)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        one)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        two) :
    let result := selection.ownerFibreBoundaryCloseRound A strategy hwin one
      inputOne two inputTwo
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1 ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.1.2 := by
  cases hreceive : selection.ownerFibreBoundaryReceive? A strategy hwin one
      two (inputOne, inputTwo) with
  | none =>
      exact ⟨by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using
            hone.noRecv A strategy hwin key one inputOne,
        by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using
            htwo.noRecv A strategy hwin key two inputTwo⟩
  | some result =>
      have hall := selection.ownerFibreBoundaryReceive?_atKey A strategy hwin
        key one two (inputOne, inputTwo) result hone htwo hreceive
      exact ⟨by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using hall.2.1,
        by
          simpa [ownerFibreBoundaryCloseRound, hreceive] using hall.2.2.2⟩

/-- Every physical transition remains in its initial root-key fibre, for an
arbitrary selected policy. -/
theorem ownerFibreRound_atKey
    (key : RootKey A strategy)
    (controls : OneControl A strategy hwin × TwoControl A strategy hwin)
    (input : In₁ × In₂) (graph : Graph)
    (hone :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        controls.1)
    (htwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        controls.2) :
    let result := selection.ownerFibreRound A strategy hwin controls input
      graph
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneAtKey A strategy hwin key
        result.1.1 ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoAtKey A strategy hwin key
        result.1.2 := by
  cases graph with
  | right =>
      exact ⟨by
          simpa [ownerFibreRound] using
            hone.noRecv A strategy hwin key controls.1 input.1,
        by
          simpa [ownerFibreRound] using
            selection.ownerFibreBoundaryOpenRecvTwo_atKey A strategy hwin key
              controls.2 input.2 controls.1 input.1 htwo hone⟩
  | left =>
      exact ⟨by
          simpa [ownerFibreRound] using
            selection.ownerFibreBoundaryOpenRecvOne_atKey A strategy hwin key
              controls.1 input.1 controls.2 input.2 hone htwo,
        by
          simpa [ownerFibreRound] using
            htwo.noRecv A strategy hwin key controls.2 input.2⟩
  | both =>
      simpa [ownerFibreRound] using
        selection.ownerFibreBoundaryCloseRound_atKey A strategy hwin key
          controls.1 input.1 controls.2 input.2 hone htwo

end ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
