/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreController

/-!
# Strict-direction closure tests for the owner-fibre carrier

The first theorem treats the clock-skew case that rejected the two-owner
proposal.  A left-oriented state is represented by a right fibre at process
one and an installed left owner at process two.  On a strict-right round,
process one advances its right fibre with no receive, while process two
receives and creates a new left fibre.  The resulting deferred/deferred pair
decodes as a right-oriented state whose two matched-prefix invariants follow
from the two fibre certificates.
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

/-- The strict reversal closes without relating an old
owner to its successor.  Both the source and target pairs satisfy the strong
dual selected relation. -/
theorem profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_switch
    (leftState rightState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (hactive :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate))
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let coordinates :
        ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin :=
      (rightState, leftState)
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (true,
        (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, coordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        coordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
        rightFibre.receiverAt A rightTemplate),
      rightState, rightFibre.2.1⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            (rightState, leftState)) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled A
        strategy hwin leftState leftReceiver leftOwner rightTemplate
          rightFibre oldLeft (rightState, leftState) (rightState, leftState)
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            (rightState, leftState)) = none := by
    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
  have hcurrentInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreInstalled
        A strategy hwin leftState leftReceiver leftOwner rightTemplate
          rightFibre rightState hactive hrightFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentInvariant, ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            (rightState, leftState))
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]

  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let leftAdvancedOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false leftOwner inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftReceiver.1.memberController A false).labelOf leftOwner).2
          leftReceiver.2.2.1 (inputOne, inputTwo) |>.target leftReceiver.2.1)
  let newRightMove :=
    packet.successor.2.1.2.1.getD rightFibre.1
  let newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A newRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightNext.receiverAt A rightAdvanced, rightNext.2.1⟩,
        leftNext.receiverAt A leftReceiver),
      leftState, leftNext.2.1⟩

  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          (rightState, leftState)) inputOne).1 =
        (.inr
            (true,
              (rightNext, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          (rightState, leftState)) := by
    rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          (rightState, leftState)) inputTwo
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          (rightState, leftState)) inputOne).1 =
        (.inr
            (false, (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
      profiledRawJointRecurrentLeftToRightPhaseLiveShared,
      profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentLeftToRightMove,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      leftNext, leftAdvancedOwner, rightAdvanced, packet, newRight,
      newRightMove]
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
              (true,
                (rightNext, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inr
              (false,
                (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
            (rightState, leftState)) =
        some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightAdvanced leftReceiver
          rightNext leftNext oldLeft newRight (rightState, leftState)
            (rightState, leftState)

  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    exact ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre
      hrightFibre inputOne
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin
          (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate) inputTwo
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, _past, hleftState, hleftCode, hleftRoot, hleftMove,
      _hleftOwner, _hleftMonitor⟩
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightAdvanced leftReceiver
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .right nextPhase hnextDecode hnextInvariant

/-- Exact mirror: an installed right boundary and a delivered left fibre
survive a strict-left reversal and become a valid left deferred/deferred
boundary. -/
theorem profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_switch
    (rightState leftState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (hactive :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate))
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot : profiledRawJointOneSidedCurrentSlots A .left leftCode () =
      some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let coordinates :
        ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin :=
      (rightState, leftState)
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (true,
        (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        coordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, coordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            (rightState, leftState))
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState)) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre A
        strategy hwin rightState rightReceiver rightOwner leftTemplate
          leftFibre oldRight (rightState, leftState) (rightState, leftState)
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_installedFibre
        A strategy hwin rightState rightReceiver rightOwner leftTemplate
          leftFibre leftState hactive hleftFibre hleftState leftCode hleftCode
            leftRoot hleftRoot hleftMove
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            (rightState, leftState))
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState))
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]

  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftTemplate.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightReceiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
        false rightOwner inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightReceiver.1.memberController A false).labelOf rightOwner).2
          rightReceiver.2.2.1 (inputTwo, inputOne) |>.target
            rightReceiver.2.1)
  let newLeftMove :=
    packet.successor.2.1.2.2.getD leftFibre.1
  let newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A newLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftNext.receiverAt A leftAdvanced, leftNext.2.1⟩,
        rightNext.receiverAt A rightReceiver),
      rightState, rightNext.2.1⟩

  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          (rightState, leftState)) inputOne
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          (rightState, leftState)) inputTwo).1 =
        (.inr
            (false, (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
      profiledRawJointRecurrentRightToLeftPhaseLiveShared,
      profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentRightToLeftMove,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightNext, rightAdvancedOwner, leftAdvanced, packet, newLeft,
      newLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          (rightState, leftState)) inputTwo).1 =
        (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          (rightState, leftState)) := by
    rfl
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
              (false,
                (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
            (rightState, leftState))
          (.inr
              (true,
                (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState)) =
        some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre A
        strategy hwin rightState leftState rightReceiver leftAdvanced
          rightNext leftNext newLeft oldRight (rightState, leftState)
            (rightState, leftState)

  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    exact ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre
      inputTwo
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hactive.advancedOwnerFibreControl_valid A strategy hwin
          (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate) inputOne
  have hactiveCopy := hactive
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, _past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightMonitor⟩
  have hnextInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightReceiver leftAdvanced
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .left nextPhase (by
    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]) hnextDecode
      hnextInvariant

/-- The equal-bit state produced after two alternating strict rounds is not a
terminal decoder artefact.  If process one receives next, the right-priority
interpretation remains selected: process one installs a freshly certified
right fibre, while process two advances its left fibre blindly. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_openOpen
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () =
        some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre newLeft newRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]

  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftTemplate.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightFibre.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightFibre.1
        false rightFibre.2.1 inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
          rightFibre.2.2 (inputTwo, inputOne) |>.target
            rightTemplate.2.1)
  let newLeftMove :=
    packet.successor.2.1.2.2.getD leftFibre.1
  let nextNewLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A newLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightNext.receiverAt A rightTemplate, rightNext.2.1⟩,
        leftNext.receiverAt A leftAdvanced),
      leftState, leftNext.2.1⟩

  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates) inputOne
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), nextNewLeft⟩), ()),
          (rightState, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
      profiledRawJointRecurrentRightToLeftPhaseLiveShared,
      profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentRightToLeftMove,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightNext, rightAdvancedOwner, leftAdvanced, packet, nextNewLeft,
      newLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo).1 =
        (.inr
            (false,
              (leftNext, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) := by
    rfl
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), nextNewLeft⟩), ()),
            (rightState, leftState))
          (.inr
            (false,
              (leftNext, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) =
        some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
        strategy hwin rightState leftState rightTemplate leftAdvanced
          rightNext leftNext nextNewLeft newRight (rightState, leftState)
            twoCoordinates

  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hcurrentInvariant.1.advancedOwnerFibreControl_valid A strategy hwin
          currentPhase.1 inputOne
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    exact ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre
      inputTwo
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftAdvanced
          rightNext leftNext hrightNext hleftNext hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  exact .right nextPhase hnextDecode hnextInvariant

/-- The complementary continuation of the equal-bit state crosses the
fibre/staged seam.  Process one advances its right fibre blindly, process two
stages the target computed from the coherent right boundary, and the bank
resolver supplies the fresh left move needed by the decoder. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_openOpen
    (rightState leftState : BankControl A strategy hwin)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newLeft : ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (newRight : ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hrightState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.2.1 = some rightFibre.1)
    (hleftState :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () =
        some leftRoot)
    (hleftMove : leftState.2.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let pendingOne :
        ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr pendingTwo, twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
        leftFibre.receiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre newLeft newRight oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_fibreFibre A
        strategy hwin rightState leftState rightTemplate leftTemplate
          rightFibre leftFibre hrightFibre hleftFibre hrightState rightCode
            hrightCode rightRoot hrightRoot hrightMove hleftState leftCode
              hleftCode leftRoot hleftRoot hleftMove
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]

  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
          rightFibre.2.2 (inputTwo, inputOne) |>.target rightTemplate.2.1)
  obtain ⟨leftMove, hleftMoveAt, hfreshLeft⟩ :=
    hcurrentInvariant.1.exists_freshLeftAt A strategy hwin currentPhase.1
      (inputOne, inputTwo) .first
  have hpacketMove : packet.successor.2.1.2.2 = some leftMove := by
    simpa only [packet, currentPhase,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using hleftMoveAt
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightNext.receiverAt A rightAdvanced, rightNext.2.1⟩,
        leftInitial),
      packet.successor, (leftMove.memberController A false).initial⟩

  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (rightNext, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates) := by
    rfl
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
      profiledRawJointRecurrentRightReceiveFor,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      rightAdvanced, packet]
    split <;> rfl
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightAdvanced, some packet)),
            (rightState, packet.successor)) =
        some nextPhase := by
    simpa only [nextPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged A
        strategy hwin rightState rightAdvanced rightNext
          (leftState, leftTemplate) newLeft packet leftMove hpacketMove
            oneCoordinates (rightState, packet.successor)

  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    exact ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre
      hrightFibre inputOne
  have hrightNextMove : rightState.2.1.2.1 = some rightNext.1 := by
    simpa only [rightNext, profiledRawJointRightOwnerFibreNoRecv] using
      hrightMove
  have hactiveNext :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        nextPhase.1 := by
    simpa only [nextPhase, leftInitial,
      ProfiledRawJointRightOwnerFibreControl.boundaryData,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using
        hrightNext.boundaryInvariant A strategy hwin rightNext rightState
          hrightState rightCode hrightCode rightRoot hrightRoot hrightNextMove
            rightAdvanced.2.1 leftInitial
  have hfreshLeftReplaced :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        ((currentPhase.1.freshLeftDataAt A strategy hwin
          (inputOne, inputTwo) leftMove .first).1,
        (currentPhase.1.freshLeftDataAt A strategy hwin
          (inputOne, inputTwo) leftMove .first).2.1,
        rightNext.receiverAt A rightAdvanced) := by
    exact
      ProfiledRawJointRecurrentLeftBoundaryInvariant.replaceOldReceiver A
        strategy hwin _ hfreshLeft (rightNext.receiverAt A rightAdvanced)
  have hdormantNext :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (nextPhase.dormantLeftData A strategy hwin) := by
    simpa only [nextPhase, leftInitial, packet, currentPhase,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt,
      ProfiledRawJointRecurrentRightBoundaryData.successor,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRightOwnerFibreControl.receiverAt] using
        hfreshLeftReplaced
  exact .right nextPhase hnextDecode ⟨hactiveNext, hdormantNext⟩

/-- A strict-left step from the reachable fibre/staged shape installs the
left owner carried by the staged packet and simultaneously creates a fresh
right fibre.  This is the bridge-to-physical handoff that would expose a
remaining one-round skew. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreStaged
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hrightCoordinate : twoCoordinates.1 = rightState)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hsourceInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(rightState,
            ⟨rightFibre.receiverAt A rightReceiver, rightFibre.2.1⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          oldPacket.successor,
          (leftMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1 := by
  dsimp only
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState,
        ⟨rightFibre.receiverAt A rightReceiver, rightFibre.2.1⟩,
        leftInitial),
      oldPacket.successor, (leftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged A
        strategy hwin rightState rightReceiver rightFibre oldLeft newLeft
          oldPacket leftMove hleftMove oneCoordinates twoCoordinates
  have hcurrentInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase, leftInitial] using hsourceInvariant
  refine ⟨.right currentPhase hcurrentRight hcurrentInvariant, ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight]

  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove
      (leftMove.memberController A false).initial leftInitial.2.1
        leftInitial.2.2.1 (inputOne, inputTwo)).2
  let leftAdvancedOwner :=
    (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove false
      (leftMove.memberController A false).initial inputTwo).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightFibre.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightFibre.1
        false rightFibre.2.1 inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin rightState
        (((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
          rightFibre.2.2 (inputTwo, inputOne) |>.target rightReceiver.2.1)
  let nextLeftMove := packet.successor.2.1.2.2.getD leftMove
  let nextNewLeft :
      ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A nextLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(oldPacket.successor, ⟨leftAdvanced, leftAdvancedOwner⟩,
        rightNext.receiverAt A rightReceiver),
      rightState, rightNext.2.1⟩

  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 =
        (.inr
            (false,
              (rightNext,
                ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ()),
          (rightState, oldPacket.successor)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
    dsimp [currentPhase, leftInitial,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentRightToLeftPhaseLivePendingFork,
      profiledRawJointRecurrentRightToLeftPhaseLiveShared,
      profiledRawJointRecurrentRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentRightToLeftMove,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      ProfiledRawJointRecurrentRightBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.receiverAt,
      initialProfiledRawJointLeftPhysicalSiblingReceiver,
      leftAdvanced, rightNext, rightAdvancedOwner, packet, nextNewLeft,
      nextLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 =
        (.inl
            (.inr
              (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
                rightReceiver)),
          twoCoordinates) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
      profiledRawJointRecurrentRightToLeftBridgeNoRecv, hleftMove,
      leftAdvancedOwner]
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inr
            (false,
              (rightNext,
                ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ()),
            (rightState, oldPacket.successor))
          (.inl
              (.inr
                (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
                  rightReceiver)),
            twoCoordinates) =
        some nextPhase := by
    simpa only [nextPhase, hrightCoordinate] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_openFibreInstalled
        A strategy hwin oldPacket.successor leftAdvanced leftAdvancedOwner
          rightReceiver rightNext nextNewLeft (rightState, oldPacket.successor)
            twoCoordinates

  have hleftStepped :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        ((currentPhase.dormantLeftData A strategy hwin).step A strategy hwin
          (inputOne, inputTwo)) := by
    exact hcurrentInvariant.2.step A strategy hwin
      (currentPhase.dormantLeftData A strategy hwin) (inputOne, inputTwo)
  have hleftActive :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (oldPacket.successor,
          ⟨leftAdvanced, leftAdvancedOwner⟩,
          rightReceiver) := by
    simpa only [currentPhase, leftInitial, leftAdvanced, leftAdvancedOwner,
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
      ProfiledRawJointRecurrentLeftBoundaryData.step,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      initialProfiledRawJointLeftPhysicalSiblingReceiver] using hleftStepped
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        hcurrentInvariant.1.advancedOwnerFibreControl_valid A strategy hwin
          currentPhase.1 inputOne
  have hactiveCopy := hcurrentInvariant.1
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, _past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightMonitor⟩
  have hrightNextMove : rightState.2.1.2.1 = some rightNext.1 := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using hrightMove
  have hnextInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryInvariant_fibreInstalled
        A strategy hwin oldPacket.successor leftAdvanced leftAdvancedOwner
          rightReceiver rightNext rightState hleftActive hrightNext hrightState
            rightCode hrightCode rightRoot hrightRoot hrightNextMove
  exact .left nextPhase (by
    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]) hnextDecode
      hnextInvariant

/-- Mirrored bridge-to-physical handoff: a strict-right step from a
staged/fibre left boundary installs the fresh right owner and retains a
newly certified left fibre. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_stagedFibre
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight newRight :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
    (oldPacket :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (honeLeftState : oneCoordinates.2 = leftState)
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hsourceInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(leftState,
            ⟨leftFibre.receiverAt A leftReceiver, leftFibre.2.1⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          oldPacket.successor,
          (rightMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let one :
        ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
      (.inl (.inl (leftState, leftReceiver, some oldPacket)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
      (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
        twoCoordinates)
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one
        two ∧
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1 := by
  dsimp only
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState,
        ⟨leftFibre.receiverAt A leftReceiver, leftFibre.2.1⟩,
        rightInitial),
      oldPacket.successor, (rightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase, rightInitial] using
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedFibre A
        strategy hwin leftState leftReceiver leftFibre oldRight newRight
          oldPacket rightMove hrightMove oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
            twoCoordinates) = none := by
    simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
  have hcurrentInvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        currentPhase := by
    simpa only [currentPhase, rightInitial] using hsourceInvariant
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentInvariant, ?_⟩

  have hreceive :
      profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some
          (currentPhase.ownerFibreReceive A strategy hwin
            (inputOne, inputTwo)) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hcurrentRight,
      hcurrentLeft]

  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove
      (rightMove.memberController A false).initial rightInitial.2.1
        rightInitial.2.2.1 (inputTwo, inputOne)).2
  let rightAdvancedOwner :=
    (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove false
      (rightMove.memberController A false).initial inputOne).2
  let leftAdvancedOwner :
      ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftFibre.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftFibre.1
        false leftFibre.2.1 inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin leftState
        (((leftFibre.1.memberController A false).labelOf leftFibre.2.1).2
          leftFibre.2.2 (inputOne, inputTwo) |>.target leftReceiver.2.1)
  let nextRightMove := packet.successor.2.1.2.1.getD rightMove
  let nextNewRight :
      ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A nextRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(oldPacket.successor, ⟨rightAdvanced, rightAdvancedOwner⟩,
        leftNext.receiverAt A leftReceiver),
      leftState, leftNext.2.1⟩

  have honeNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne).1 =
        (.inl
            (.inr
              (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩,
                leftReceiver)),
          oneCoordinates) := by
    simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
      profiledRawJointRecurrentLeftToRightBridgeNoRecv, hrightMove,
      rightAdvancedOwner]
  have htwoNext :
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
          twoCoordinates) inputTwo
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (leftNext,
                ⟨(oldPacket.successor, rightAdvanced), nextNewRight⟩), ()),
          (oldPacket.successor, leftState)) := by
    rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
    dsimp [currentPhase, rightInitial,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
      ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive,
      profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
      profiledRawJointRecurrentLeftToRightPhaseLivePendingFork,
      profiledRawJointRecurrentLeftToRightPhaseLiveShared,
      profiledRawJointRecurrentLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentLeftToRightMove,
      ProfiledRawJointRecurrentLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentLeftBoundaryData.owner,
      ProfiledRawJointRecurrentLeftBoundaryData.target,
      ProfiledRawJointLeftOwnerFibreControl.receiverAt,
      initialProfiledRawJointRightPhysicalSiblingReceiver,
      rightAdvanced, leftNext, leftAdvancedOwner, packet, nextNewRight,
      nextRightMove]
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
          (.inl
              (.inr
                (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩,
                  leftReceiver)),
            oneCoordinates)
          (.inr
            (false,
              (leftNext,
                ⟨(oldPacket.successor, rightAdvanced), nextNewRight⟩), ()),
            (oldPacket.successor, leftState)) =
        some nextPhase := by
    simpa only [nextPhase, honeLeftState] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre A
        strategy hwin oldPacket.successor rightAdvanced rightAdvancedOwner
          leftReceiver leftNext nextNewRight oneCoordinates
            (oldPacket.successor, leftState)

  have hrightStepped :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        ((currentPhase.dormantRightData A strategy hwin).step A strategy hwin
          (inputOne, inputTwo)) := by
    exact hcurrentInvariant.2.step A strategy hwin
      (currentPhase.dormantRightData A strategy hwin) (inputOne, inputTwo)
  have hrightActive :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (oldPacket.successor, ⟨rightAdvanced, rightAdvancedOwner⟩,
          leftReceiver) := by
    simpa only [currentPhase, rightInitial, rightAdvanced,
      rightAdvancedOwner,
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
      ProfiledRawJointRecurrentRightBoundaryData.step,
      ProfiledRawJointRecurrentRightBoundaryData.receiver,
      ProfiledRawJointRecurrentRightBoundaryData.owner,
      initialProfiledRawJointRightPhysicalSiblingReceiver] using hrightStepped
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        hcurrentInvariant.1.advancedOwnerFibreControl_valid A strategy hwin
          currentPhase.1 inputTwo
  have hactiveCopy := hcurrentInvariant.1
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hactiveCopy
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, _past, hleftState, hleftCode, hleftRoot,
      hleftMove, _hleftOwner, _hleftMonitor⟩
  have hleftNextMove : leftState.2.1.2.2 = some leftNext.1 := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using hleftMove
  have hnextInvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentOwnerFibreRightBoundaryInvariant_installedFibre
        A strategy hwin oldPacket.successor rightAdvanced rightAdvancedOwner
          leftReceiver leftNext leftState hrightActive hleftNext hleftState
            leftCode hleftCode leftRoot hleftRoot hleftNextMove
  exact .right nextPhase hnextDecode hnextInvariant

end

end DetParityAutomaton

end DistributedSynthesis
