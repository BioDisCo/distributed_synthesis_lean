/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveInvariant

/-!
# Recurrent closure of the phase-live local carrier

The simultaneous boundary is the fragile transition.  It reverses the active
orientation, starts the new receiver in row `both`, and demotes the old active
orientation only after advancing both its owner and receiver on the boundary
input.  This file proves those facts before treating the same-direction cases.
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

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

/-! ## Invariants ignore the opposite dormant receiver -/

theorem ProfiledRawJointRecurrentRightBoundaryInvariant.replaceOldReceiver
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
      (data.1, data.2.1, oldReceiver) := by
  exact hinvariant

theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.replaceOldReceiver
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
      (data.1, data.2.1, oldReceiver) := by
  exact hinvariant

/-! ## Exact simultaneous successors -/

/-- The left-oriented data selected after closing a right-oriented boundary.
The new active receiver starts in row `both`; the dormant right owner has
already taken its local no-receive step. -/
noncomputable def
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.afterBoth
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
  ⟨phaseData.1.freshLeftDataAt A strategy hwin input move .both,
    phaseData.1.1,
    (phaseData.1.step A strategy hwin input).owner A strategy hwin⟩

/-- Mirrored exact simultaneous successor. -/
noncomputable def
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.afterBoth
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
  ⟨phaseData.1.freshRightDataAt A strategy hwin input move .both,
    phaseData.1.1,
    (phaseData.1.step A strategy hwin input).owner A strategy hwin⟩

theorem ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant.afterBoth
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        phaseData)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (phaseData.1.successor A strategy hwin input).2.1.2.2 = some move ∧
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        (phaseData.afterBoth A strategy hwin input move) := by
  rcases hinvariant with ⟨hactive, hdormant⟩
  obtain ⟨move, hmove, hfresh⟩ :=
    hactive.exists_freshLeftAt A strategy hwin phaseData.1 input .both
  refine ⟨move, hmove, hfresh, ?_⟩
  have hstepped := hactive.step A strategy hwin phaseData.1 input
  let newOldReceiver :=
    ProfiledRawJointRecurrentLeftBoundaryData.receiver A strategy hwin
      (phaseData.1.freshLeftDataAt A strategy hwin input move .both)
  exact
    ProfiledRawJointRecurrentRightBoundaryInvariant.replaceOldReceiver A
      strategy hwin (phaseData.1.step A strategy hwin input) hstepped
        newOldReceiver

theorem ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant.afterBoth
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        phaseData)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (phaseData.1.successor A strategy hwin input).2.1.2.1 = some move ∧
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        (phaseData.afterBoth A strategy hwin input move) := by
  rcases hinvariant with ⟨hactive, hdormant⟩
  obtain ⟨move, hmove, hfresh⟩ :=
    hactive.exists_freshRightAt A strategy hwin phaseData.1 input .both
  refine ⟨move, hmove, hfresh, ?_⟩
  have hstepped := hactive.step A strategy hwin phaseData.1 input
  let newOldReceiver :=
    ProfiledRawJointRecurrentRightBoundaryData.receiver A strategy hwin
      (phaseData.1.freshRightDataAt A strategy hwin input move .both)
  exact
    ProfiledRawJointRecurrentLeftBoundaryInvariant.replaceOldReceiver A
      strategy hwin (phaseData.1.step A strategy hwin input) hstepped
        newOldReceiver

/-! ## Simultaneous-close decoder equations -/

theorem
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.close_decodes_left
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove :
      (phaseData.1.successor A strategy hwin input).2.1.2.2 = some move) :
    let result := phaseData.receive A strategy hwin input
    profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin
        result.1.1.closedControl result.2.1.closedControl =
      some (phaseData.afterBoth A strategy hwin input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨rightMove, row, receiverState, lastTarget⟩
  rcases oldReceiver with
    ⟨leftMove, oldRow, oldReceiverState, oldLastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((rightMove.memberController A false).labelOf owner).2 receiverState
      (input.2, input.1)).target row)
  have hmove' :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target).successor.2.1.2.2 = some move := by
    simpa only [target,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hmove
  dsimp only [target,
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] at hmove'
  have hnewMove :
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target)).2.1.2.2.getD leftMove = move := by
    dsimp only [target]
    simp [hmove']
  dsimp only [target] at hnewMove
  simp [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.receive,
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.afterBoth,
    ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt,
    ProfiledRawJointRecurrentRightBoundaryData.target,
    ProfiledRawJointRecurrentRightBoundaryData.successor,
    ProfiledRawJointRecurrentRightBoundaryData.step,
    ProfiledRawJointRecurrentRightBoundaryData.receiver,
    ProfiledRawJointRecurrentRightBoundaryData.owner,
    ProfiledRawJointRecurrentRightBoundaryData.phaseLiveReceive,
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
    profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
    profiledRawJointRecurrentRightToLeftMove,
    profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
    profiledRawJointRecurrentRightToLeftPhaseLiveShared,
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
    profiledRawJointRecurrentRightReceiveFor,
    initialProfiledRawJointLeftPhysicalSiblingReceiver,
    target, hmove', hnewMove]
  rw [hnewMove]
  exact
    profiledRawJointRecurrentPhaseLeftBoundaryData?_phaseInstalledReceiver A
      strategy hwin state
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
          state
            (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
              strategy hwin state target))
        (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove owner
          row receiverState (input.2, input.1)).2
        (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove false
          owner input.1).2
        (initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both)
        (move.memberController A false).initial
        (oldState,
          (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove
            oldOwner oldRow oldReceiverState input).2)
        (state,
          profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target))
        (state,
          profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target))

theorem
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.close_decodes_right
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove :
      (phaseData.1.successor A strategy hwin input).2.1.2.1 = some move) :
    let result := phaseData.receive A strategy hwin input
    profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
        result.1.1.closedControl result.2.1.closedControl =
      some (phaseData.afterBoth A strategy hwin input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨leftMove, row, receiverState, lastTarget⟩
  rcases oldReceiver with
    ⟨rightMove, oldRow, oldReceiverState, oldLastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((leftMove.memberController A false).labelOf owner).2 receiverState
      input).target row)
  have hmove' :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target).successor.2.1.2.1 = some move := by
    simpa only [target,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
      ProfiledRawJointRecurrentLeftBoundaryData.successor,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner] using hmove
  dsimp only [target,
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] at hmove'
  have hnewMove :
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target)).2.1.2.1.getD rightMove = move := by
    dsimp only [target]
    simp [hmove']
  dsimp only [target] at hnewMove
  simp [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.receive,
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.afterBoth,
    ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt,
    ProfiledRawJointRecurrentLeftBoundaryData.target,
    ProfiledRawJointRecurrentLeftBoundaryData.successor,
    ProfiledRawJointRecurrentLeftBoundaryData.step,
    ProfiledRawJointRecurrentLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentLeftBoundaryData.owner,
    ProfiledRawJointRecurrentLeftBoundaryData.phaseLiveReceive,
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
    profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
    profiledRawJointRecurrentLeftToRightMove,
    profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
    profiledRawJointRecurrentLeftToRightPhaseLiveShared,
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
    profiledRawJointRecurrentLeftReceiveFor,
    initialProfiledRawJointRightPhysicalSiblingReceiver,
    target, hmove', hnewMove]
  rw [hnewMove]
  exact
    profiledRawJointRecurrentPhaseRightBoundaryData?_installedPhaseClosed A
      strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
          state
            (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
              strategy hwin state target))
        state
        (initialProfiledRawJointRightPhysicalSiblingReceiver A move .both)
        (move.memberController A false).initial
        (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove owner row
          receiverState input).2
        (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove false
          owner input.2).2
        (oldState,
          (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove
            oldOwner oldRow oldReceiverState (input.2, input.1)).2)
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
            state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target),
          state)
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
            state
              (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
                strategy hwin state target),
          state)

/-- The closed phase/installed pair produced from a right boundary is not
accepted by the priority right decoder. -/
theorem
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.close_rejects_right
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove :
      (phaseData.1.successor A strategy hwin input).2.1.2.2 = some move) :
    let result := phaseData.receive A strategy hwin input
    profiledRawJointRecurrentPhaseRightBoundaryData? A strategy hwin
        result.1.1.closedControl result.2.1.closedControl = none := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨rightMove, row, receiverState, lastTarget⟩
  rcases oldReceiver with
    ⟨leftMove, oldRow, oldReceiverState, oldLastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((rightMove.memberController A false).labelOf owner).2 receiverState
      (input.2, input.1)).target row)
  have hmove' :
      (profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target).successor.2.1.2.2 = some move := by
    simpa only [target,
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner] using hmove
  dsimp only [target,
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket] at hmove'
  simp [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.receive,
    ProfiledRawJointRecurrentRightBoundaryData.target,
    ProfiledRawJointRecurrentRightBoundaryData.successor,
    ProfiledRawJointRecurrentRightBoundaryData.receiver,
    ProfiledRawJointRecurrentRightBoundaryData.owner,
    ProfiledRawJointRecurrentRightBoundaryData.phaseLiveReceive,
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
    profiledRawJointRecurrentRightReceiveFor,
    profiledRawJointRecurrentPhaseRightBoundaryData?, target, hmove']

/-! ## Dual selected relation and exact-close preservation -/

/-- Successful phase decoding together with matched-prefix certificates for
both the active and dormant orientations. -/
inductive ProfiledRawJointRecurrentPhaseBoundaryDualSelected :
    ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin → Prop
  | right {one two}
      (phaseData :
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
      (hdata : profiledRawJointRecurrentPhaseRightBoundaryData? A strategy
        hwin one two = some phaseData)
      (invariant :
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
          phaseData) :
      ProfiledRawJointRecurrentPhaseBoundaryDualSelected one two
  | left {one two}
      (phaseData :
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
      (hright : profiledRawJointRecurrentPhaseRightBoundaryData? A strategy
        hwin one two = none)
      (hdata : profiledRawJointRecurrentPhaseLeftBoundaryData? A strategy hwin
        one two = some phaseData)
      (invariant :
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
          phaseData) :
      ProfiledRawJointRecurrentPhaseBoundaryDualSelected one two

/-- Exact simultaneous closing preserves the dual selected relation and
reverses the active orientation. -/
theorem profiledRawJointRecurrentPhaseBoundaryDualSelected_both
    (one : ProfiledRawJointRecurrentPhaseBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two : ProfiledRawJointRecurrentPhaseBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (hselected : ProfiledRawJointRecurrentPhaseBoundaryDualSelected A strategy
      hwin one two) :
    ProfiledRawJointRecurrentPhaseBoundaryDualSelected A strategy hwin
      (profiledRawJointRecurrentPhaseBoundaryClose A strategy hwin one inputOne
        two inputTwo).1
      (profiledRawJointRecurrentPhaseBoundaryClose A strategy hwin one inputOne
        two inputTwo).2 := by
  cases hselected with
  | right phaseData hdata hinvariant =>
      have hreceive :=
        profiledRawJointRecurrentPhaseBoundaryReceive?_of_right A strategy hwin
          one two phaseData hdata (inputOne, inputTwo)
      obtain ⟨move, hmove, hnextInvariant⟩ :=
        hinvariant.afterBoth A strategy hwin phaseData (inputOne, inputTwo)
      have hleft := phaseData.close_decodes_left A strategy hwin
        (inputOne, inputTwo) move hmove
      have hright := phaseData.close_rejects_right A strategy hwin
        (inputOne, inputTwo) move hmove
      simp only [profiledRawJointRecurrentPhaseBoundaryClose, hreceive]
      exact .left (phaseData.afterBoth A strategy hwin (inputOne, inputTwo) move)
        hright hleft hnextInvariant
  | left phaseData hright hdata hinvariant =>
      have hreceive :=
        profiledRawJointRecurrentPhaseBoundaryReceive?_of_left A strategy hwin
          one two phaseData hright hdata (inputOne, inputTwo)
      obtain ⟨move, hmove, hnextInvariant⟩ :=
        hinvariant.afterBoth A strategy hwin phaseData (inputOne, inputTwo)
      have hnext := phaseData.close_decodes_right A strategy hwin
        (inputOne, inputTwo) move hmove
      simp only [profiledRawJointRecurrentPhaseBoundaryClose, hreceive]
      exact .right (phaseData.afterBoth A strategy hwin (inputOne, inputTwo) move)
        hnext hnextInvariant

end

end DetParityAutomaton

end DistributedSynthesis
